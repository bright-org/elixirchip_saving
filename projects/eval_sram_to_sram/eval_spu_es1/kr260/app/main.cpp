#include <iostream>
#include <cstdint>
#include <random>
#include <unistd.h>
#include "jelly/UioAccessor.h"


#define REG_START   0x00
#define REG_DONE    0x01
#define REG_REPEAT  0x02
#define REG_TIME    0x03
#define REG_COUNTER 0x04


#define MEM_SIZE        (1024*8)
#define PIPELINE_SIZE   256

int main(int argc, char *argv[])
{

    // mmap uio
    jelly::UioAccessor uio_acc("uio_pl_peri", 0x08000000);
    if ( !uio_acc.IsMapped() ) {
        std::cout << "uio_pl_peri mmap error" << std::endl;
        return 1;
    }
    auto acc_reg  = uio_acc.GetAccessor(0x00000000);
    auto acc_mem0 = uio_acc.GetAccessor(0x00008000);
    auto acc_mem1 = uio_acc.GetAccessor(0x0000a000);
    auto acc_mem2 = uio_acc.GetAccessor(0x0000c000);
    auto acc_mem3 = uio_acc.GetAccessor(0x0000e000);

    // データ準備
    static std::int8_t mem0[MEM_SIZE];
    static std::int8_t mem1[MEM_SIZE];
    static std::int8_t mem2[MEM_SIZE];
    static std::int8_t mem3[MEM_SIZE];
    static std::int8_t exp0[MEM_SIZE];
    static std::int8_t exp1[MEM_SIZE];

    // 乱数で初期値生成
//  std::random_device seed_gen;
//  std::mt19937 engine(seed_gen());
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

    // データ転送
    acc_mem0.MemCopyFrom(0, mem0, MEM_SIZE);
    acc_mem1.MemCopyFrom(0, mem1, MEM_SIZE);

    // 計算実施
    acc_reg.WriteReg(REG_START, 1);
    while ( acc_reg.ReadReg(REG_DONE) == 0 ) {
        usleep(1000);
    }

    // 結果読み出し
    acc_mem2.MemCopyTo(mem2, 0, MEM_SIZE);
    acc_mem3.MemCopyTo(mem3, 0, MEM_SIZE);

    // 結果チェック
    bool ok = true;
    for (int i = 0; i < MEM_SIZE; ++i) {
        std::cout << "MEM2[" << i << "] : " << (int)mem2[i] << "  exp : " << (int)exp0[i];
        if (mem2[i] != exp0[i]) {
            std::cout << " !!! NG !!!" << std::endl;
            ok = false;
//            return 1;
        }
        else {
            std::cout << " OK" << std::endl;
        }

        std::cout << "MEM3[" << i << "] : " << (int)mem3[i] << "  exp : " << (int)exp1[i];
        if (mem3[i] != exp1[i]) {
            std::cout << " !!! NG !!!" << std::endl;
            ok = false;
//            return 1;
        }
        else {
            std::cout << " OK" << std::endl;
        }
    }
    if ( ok ) {
        std::cout << "ALL OK!" << std::endl;
    }
    else {
        std::cout << "!!!ERROR!!!" << std::endl;
    }

    auto time = acc_reg.ReadReg(REG_TIME);
    std::cout << "time : " << time  / 166.6 << " [us]" << std::endl;

#if 0
    // 10秒間連続実行(電力計測用)
    std::cout << "" << std::endl;
    std::cout << "repeat run 10s" << std::endl;
    acc_reg.WriteReg(REG_REPEAT, 1);
    acc_reg.WriteReg(REG_START, 1);
    usleep(10000000);
    acc_reg.WriteReg(REG_REPEAT, 0);
    std::cout << "end" << std::endl;
#endif

    return 0;
}




// end of file
