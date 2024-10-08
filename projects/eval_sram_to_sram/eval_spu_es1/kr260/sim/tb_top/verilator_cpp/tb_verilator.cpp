#include <cstdint>
#include <random>
#include <memory>
#include <verilated.h>
#include "Vtb_main.h"
#include "jelly/simulator/Manager.h"
#include "jelly/simulator/ResetNode.h"
#include "jelly/simulator/ClockNode.h"
#include "jelly/simulator/VerilatorNode.h"
#include "jelly/simulator/WishboneMasterNode.h"
#include "jelly/JellyRegs.h"


namespace jsim = jelly::simulator;


#if VM_TRACE
#include <verilated_fst_c.h> 
#include <verilated_vcd_c.h> 
#endif

void pack64(const std::int8_t mem[8], std::uint64_t& data)
{
    data = 0;
    for (int i = 0; i < 8; ++i) {
        data |= (std::uint64_t)(mem[i] & 0xff) << (i * 8);
    }
}

void unpack64(std::int8_t mem[8], std::uint64_t data)
{
    for (int i = 0; i < 8; ++i) {
        mem[i] = (std::int8_t)((data >> (i * 8)) & 0xff);
    }
}

int main(int argc, char** argv)
{
    auto contextp = std::make_shared<VerilatedContext>();
    contextp->debug(0);
    contextp->randReset(2);
    contextp->commandArgs(argc, argv);
    
    const auto top = std::make_shared<Vtb_main>(contextp.get(), "top");


    jsim::trace_ptr_t tfp = nullptr;
#if VM_TRACE
    contextp->traceEverOn(true);

    tfp = std::make_shared<jsim::trace_t>();
    top->trace(tfp.get(), 100);
    tfp->open("tb_verilator" TRACE_EXT);
#endif

    auto mng = jsim::Manager::Create();

    mng->AddNode(jsim::VerilatorNode_Create(top, tfp));

    mng->AddNode(jsim::ResetNode_Create(&top->reset, 100));
    mng->AddNode(jsim::ClockNode_Create(&top->clk300, 1000.0/200.0));
    mng->AddNode(jsim::ClockNode_Create(&top->clk500, 1000.0/500.0));

    jsim::WishboneMaster wishbone_signals =
            {
                &top->reset,
                &top->clk300,
                &top->s_wb_adr_i,
                &top->s_wb_dat_o,
                &top->s_wb_dat_i,
                &top->s_wb_sel_i,
                &top->s_wb_we_i,
                &top->s_wb_stb_i,
                &top->s_wb_ack_o
            };
    auto wb = jsim::WishboneMasterNode_Create(wishbone_signals);
    mng->AddNode(wb);


    // データ準備
    const int MEM_SIZE      = 1024 * 8;
    const int PIPELINE_SIZE = 256;
    static std::int8_t mem0[MEM_SIZE];
    static std::int8_t mem1[MEM_SIZE];
    static std::int8_t mem2[MEM_SIZE];
    static std::int8_t mem3[MEM_SIZE];
    static std::int8_t exp0[MEM_SIZE];
    static std::int8_t exp1[MEM_SIZE];

    // 乱数で初期値生成
    std::mt19937 engine(1234);
    std::uniform_int_distribution<std::int8_t> dist(-128, +127);
    for (int i = 0; i < MEM_SIZE; ++i) {
        mem0[i] = dist(engine);
        mem1[i] = dist(engine);
    }

    // 期待値生成
    static  std::int8_t data0[PIPELINE_SIZE+1][MEM_SIZE];
    static  std::int8_t data1[PIPELINE_SIZE+1][MEM_SIZE];
    for (int i = 0; i < MEM_SIZE; ++i) {
        data0[0][i] = mem0[i];
        data1[0][i] = mem1[i];
    }
    for (int i = 0; i < MEM_SIZE; ++i) {
        for (int j = 0; j < PIPELINE_SIZE; ++j) {
            data0[j+1][i] = data0[j][i] * data1[j][i];
            data1[j+1][i] = data0[j][i] + data1[j][i];
        }
    }
    for (int i = 0; i < MEM_SIZE; ++i) {
        exp0[i] = data0[PIPELINE_SIZE][i];
        exp1[i] = data1[PIPELINE_SIZE][i];
    }

    const   int     ADR_REG  = 0x00000000;
    const   int     ADR_MEM0 = 0x00001000;
    const   int     ADR_MEM1 = 0x00001400;
    const   int     ADR_MEM2 = 0x00001800;
    const   int     ADR_MEM3 = 0x00001c00;

    // リセット解除待ち
    wb->Wait(1000);
    wb->Display("start");

    // ----- メモリ読み書きテスト -----
    wb->Display("---- mem read/write test ----");
    wb->ExecWrite(ADR_MEM0 + 0, 0x0706050403020100, 0xff);
    wb->ExecWrite(ADR_MEM0 + 1, 0x0f0e0d0c0b0a0908, 0xff);
    wb->ExecWrite(ADR_MEM0 + 2, 0x1716151413121110, 0xff);
    wb->ExecWrite(ADR_MEM0 + 3, 0x1f1e1d1c1b1a1918, 0xff);
    wb->ExecWrite(ADR_MEM0 + 4, 0x2726252423222120, 0xff);
    wb->ExecWrite(ADR_MEM0 + 5, 0x2f2e2d2c2b2a2928, 0xff);
    wb->ExecWrite(ADR_MEM0 + 6, 0x3736353433323130, 0xff);
    wb->ExecWrite(ADR_MEM0 + 7, 0x3f3e3d3c3b3a3938, 0xff);
    wb->ExecWrite(ADR_MEM0 + 8, 0x4746454443424140, 0xff);
    wb->ExecWrite(ADR_MEM0 + 9, 0x4f4e4d4c4b4a4948, 0xff);
    wb->ExecWrite(ADR_MEM1 + 1, 0x0000000000000011, 0x01);
    wb->ExecWrite(ADR_MEM1 + 1, 0x0000000000002200, 0x02);
    wb->ExecWrite(ADR_MEM1 + 1, 0x0000000000330000, 0x04);
    wb->ExecWrite(ADR_MEM1 + 1, 0x0000000044000099, 0x08);
    wb->ExecWrite(ADR_MEM1 + 1, 0x0000005500000099, 0x10);
    wb->ExecWrite(ADR_MEM1 + 1, 0x0000660000000099, 0x20);
    wb->ExecWrite(ADR_MEM1 + 1, 0x0077000000000099, 0x40);
    wb->ExecWrite(ADR_MEM1 + 1, 0x8800000000000099, 0x80);
    wb->ExecWrite(ADR_MEM2 + 0, 0x0000000000003333, 0xff);
    wb->ExecWrite(ADR_MEM3 + 0, 0x0000000000004444, 0xff);
    assert(wb->ExecRead(ADR_MEM0 + 0) == 0x0706050403020100);
    assert(wb->ExecRead(ADR_MEM0 + 1) == 0x0f0e0d0c0b0a0908);
    assert(wb->ExecRead(ADR_MEM0 + 2) == 0x1716151413121110);
    assert(wb->ExecRead(ADR_MEM0 + 3) == 0x1f1e1d1c1b1a1918);
    assert(wb->ExecRead(ADR_MEM0 + 4) == 0x2726252423222120);
    assert(wb->ExecRead(ADR_MEM0 + 5) == 0x2f2e2d2c2b2a2928);
    assert(wb->ExecRead(ADR_MEM0 + 6) == 0x3736353433323130);
    assert(wb->ExecRead(ADR_MEM0 + 7) == 0x3f3e3d3c3b3a3938);
    assert(wb->ExecRead(ADR_MEM0 + 8) == 0x4746454443424140);
    assert(wb->ExecRead(ADR_MEM0 + 9) == 0x4f4e4d4c4b4a4948);
    assert(wb->ExecRead(ADR_MEM1 + 1) == 0x8877665544332211);
    assert(wb->ExecRead(ADR_MEM2 + 0) == 0x0000000000003333);
    assert(wb->ExecRead(ADR_MEM3 + 0) == 0x0000000000004444);


    // ---- 演算テスト ----

    wb->Display("---- MUL and ADD test ---- ");

    // 入力データ書き込み
    for ( int i = 0; i < 1024; i++ ) {
        std::uint64_t dat0, dat1;
        pack64(&mem0[i*8], dat0);
        pack64(&mem1[i*8], dat1);
        wb->ExecWrite(ADR_MEM0 + i, dat0, 0xff);
        wb->ExecWrite(ADR_MEM1 + i, dat1, 0xff);
    }

    // start
    wb->Display("start");
    wb->ExecWrite(ADR_REG + 0, 1, 0xff);

    // wait for done
    wb->Display("wait for done");
    do {
        wb->Wait(100);
    } while ( wb->ExecRead(ADR_REG + 1) == 0 );
    wb->Display("done");
    wb->ExecWrite(ADR_REG + 1, 0, 0xff);

    // read
    for ( int i = 0; i < 1024; i++ ) {
        std::uint64_t expect0, expect1;
        pack64(&exp0[i*8], expect0);
        pack64(&exp1[i*8], expect1);

        std::uint64_t dat0 = wb->ExecRead(ADR_MEM2 + i);
        std::cout << "mem2[" << i << "] = " << std::hex << dat0 << " (expect:" << expect0 << ")" << std::endl;
        assert (dat0 == expect0);

        std::uint64_t dat1 = wb->ExecRead(ADR_MEM3 + i);
        std::cout << "mem3[" << i << "] = " << std::hex << dat1 << " (expect:" << expect1 << ")" << std::endl;
        assert (dat1 == expect1);
    }


    // ---- 終了 ----

    // 波形を読みやすくするのに少し余分に実行
    mng->Run(1000);


#if VM_TRACE
    tfp->close();
#endif

#if VM_COVERAGE
    contextp->coveragep()->write("coverage.dat");
#endif

    return 0;
}


// end of file
