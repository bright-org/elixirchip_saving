#include <iostream>
#include <cstdint>
#include <random>
#include <unistd.h>
#include "jelly/UioAccessor.h"


#define REG_START   0x00
#define REG_DONE    0x01

#define MEM_SIZE    (1024*64)

int main(int argc, char *argv[])
{

    // mmap uio
    jelly::UioAccessor uio_acc("uio_pl_peri", 0x08000000);
    if ( !uio_acc.IsMapped() ) {
        std::cout << "uio_pl_peri mmap error" << std::endl;
        return 1;
    }
    auto acc_reg  = uio_acc.GetAccessor(0x00000000);
    auto acc_mem0 = uio_acc.GetAccessor(0x00010000);
    auto acc_mem1 = uio_acc.GetAccessor(0x00020000);
    auto acc_mem2 = uio_acc.GetAccessor(0x00030000);

    std::cout << " mem0[0] : " << acc_mem0.ReadReg(0) << std::endl;
    acc_mem0.WriteReg(0, 123);
    std::cout << " mem0[0] : " << acc_mem0.ReadReg(0) << std::endl;


    std::int8_t mem0[MEM_SIZE];
    std::int8_t mem1[MEM_SIZE];
    std::int8_t mem2[MEM_SIZE];
    std::int8_t exp[MEM_SIZE];

    // 乱数で初期値生成
    std::random_device seed_gen;
    std::mt19937 engine(seed_gen());
    std::uniform_int_distribution<std::int8_t> dist(-10, +10);
    for (int i = 0; i < MEM_SIZE; ++i) {
        mem0[i] = dist(engine);
        mem1[i] = dist(engine);
    }

    // 期待値生成
    for (int i = 0; i < MEM_SIZE; ++i) {
        exp[i] = mem0[i] * mem1[i] + 17;
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

    // 結果チェック
    for (int i = 0; i < MEM_SIZE; ++i) {
        std::cout << "MEM[" << i << "] " << (int)mem0[i] << " * "  << (int)mem1[i] << " + 17 => " << (int)mem2[i] << "  exp : " << (int)exp[i];
        if (mem2[i] != exp[i]) {
            std::cout << " !!! NG !!!" << std::endl;
            return 1;
        }
        std::cout << " OK" << std::endl;
    }
    std::cout << "ALL OK!" << std::endl;

    return 0;
}




// end of file
