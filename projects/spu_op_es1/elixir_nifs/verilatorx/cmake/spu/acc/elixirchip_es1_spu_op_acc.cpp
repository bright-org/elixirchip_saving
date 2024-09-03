

#include <verilated.h>

#if VM_TRACE
#include <verilated_fst_c.h> 
#include <verilated_vcd_c.h> 

#if VM_TRACE_FST
#define TRACE_EXT   ".fst"
using trace_t     = VerilatedFstC;
#else
#define TRACE_EXT   ".vcd"
using trace_t     = VerilatedVcdC;
#endif
using trace_ptr_t = std::shared_ptr<trace_t>;
#endif


#include "Velixirchip_es1_spu_op_acc_wrapper.h"
using ModuleType = Velixirchip_es1_spu_op_acc_wrapper;

#include "elixirchip_es1_spu_op_acc.h"

// コンテキスト
struct SpuAccContext {
    std::shared_ptr<VerilatedContext>   contextp;
    std::shared_ptr<ModuleType>         top;
#if VM_TRACE
    std::shared_ptr<trace_t>            tfp;
    int                                 time_counter;
#endif

    void dump() {
#if VM_TRACE
        tfp->dump(time_counter);
        time_counter++;
#endif
    }
};

// 生成
void elixirchip_es1_spu_op_acc_create(SpuAcc *self, const char *name)
{
    SpuAccContext* ctx = new SpuAccContext();

    // モデル生成
    ctx->contextp = std::make_shared<VerilatedContext>();
    ctx->contextp->debug(0);
    ctx->contextp->randReset(2);
//  ctx->contextp->commandArgs(argc, argv);
    ctx->top = std::make_shared<ModuleType>(ctx->contextp.get(), "top");

#if VM_TRACE
    ctx->contextp->traceEverOn(true);
    ctx->tfp = std::make_shared<trace_t>();
    ctx->top->trace(ctx->tfp.get(), 100);
    ctx->tfp->open((name + TRACE_EXT).c_str());
    ctx->time_counter = 0;
#endif

    // 初期化
    ctx->top->reset       = 1;
    ctx->top->clk         = 0;
    ctx->top->cke         = 1;
    ctx->top->s_sub       = 0;
    ctx->top->s_carry     = 0;
    ctx->top->s_data      = 0;
    ctx->top->s_clear     = 0;
    ctx->top->s_valid     = 0;

    // リセット期間
    for ( int i = 0; i < 16; i++ )
    {
        ctx->top->clk = 0;
        ctx->top->eval();
        ctx->dump();
        ctx->top->clk = 1;
        ctx->top->eval();
        ctx->dump();
    }
    ctx->top->reset   = 0;

    // 生成したコンテキストを設定
    self->context = ctx;
}

// 破棄
void elixirchip_es1_spu_op_acc_delete(SpuAcc *self)
{
    auto ctx = self->context;

    ctx->top->final();
    delete ctx;
    self->context = nullptr;

#if VM_TRACE
    ctx->tfp->close();
#endif
}

// 演算
void elixirchip_es1_spu_op_acc(
            SpuAcc *self,
            int s_sub,
            int s_carry,
            int s_data,
            int s_clear,
            int s_valid,
            int& m_carry,
            int& m_data
        )
{
    auto ctx = self->context;

    // 入力設定
    ctx->top->s_sub = s_sub;
    ctx->top->s_carry = s_carry;
    ctx->top->s_data = s_data;
    ctx->top->s_clear = s_clear;
    ctx->top->s_valid = s_valid;

    // latency 分クロックを入れる
    for ( int i = 0; i < 1; i++ ) {
        ctx->top->clk = 0;
        ctx->top->eval();
        ctx->dump();
        ctx->top->clk = 1;
        ctx->top->eval();
        ctx->dump();
    }

    // 結果取り出し
    m_data  = ctx->top->m_data;
    m_carry = ctx->top->m_carry;
}

// end of file