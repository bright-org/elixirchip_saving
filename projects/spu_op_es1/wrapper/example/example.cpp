#include <iostream>
#include <cassert>

#include "elixirchip_es1_spu_op_acc.h"
#include "elixirchip_es1_spu_op_add.h"

int main()
{
    std::cout << "start" << std::endl;

    // ---------------------------------
    //  生成(2つ作ってみる)
    // ---------------------------------

    auto acc1 = elixirchip_es1_spu_op_acc_create("acc1");
    auto acc2 = elixirchip_es1_spu_op_acc_create("acc2");
    auto add  = elixirchip_es1_spu_op_add_create("add");


    // ---------------------------------
    //  演算
    // ---------------------------------
    
    int acc1_s_sub, acc1_s_carry, acc1_s_data, acc1_s_clear, acc1_s_valid, acc1_m_carry, acc1_m_data;
    int acc2_s_sub, acc2_s_carry, acc2_s_data, acc2_s_clear, acc2_s_valid, acc2_m_carry, acc2_m_data;

    // acc1 を クリア
    acc1_s_sub       = 0;
    acc1_s_carry     = 0;
    acc1_s_data      = 0;
    acc1_s_clear     = 1;
    acc1_s_valid     = 1;
    elixirchip_es1_spu_op_acc(acc1, acc1_s_sub, acc1_s_carry, acc1_s_data, acc1_s_clear, acc1_s_valid, acc1_m_carry, acc1_m_data);
    std::cout << "acc1: " << acc1_m_data << std::endl;
    assert(acc1_m_carry == 0);
    assert(acc1_m_data  == 0);

    // acc2 を クリア
    acc2_s_sub       = 0;
    acc2_s_carry     = 0;
    acc2_s_data      = 0;
    acc2_s_clear     = 1;
    acc2_s_valid     = 1;
    elixirchip_es1_spu_op_acc(acc2, acc2_s_sub, acc2_s_carry, acc2_s_data, acc2_s_clear, acc2_s_valid, acc2_m_carry, acc2_m_data);
    std::cout << "acc2: " << acc2_m_data << std::endl;
    assert(acc2_m_carry == 0);
    assert(acc2_m_data  == 0);

    // acc1 に 10 を加算
    acc1_s_sub       = 0;
    acc1_s_carry     = 0;
    acc1_s_data      = 10;
    acc1_s_clear     = 0;
    acc1_s_valid     = 1;
    elixirchip_es1_spu_op_acc(acc1, acc1_s_sub, acc1_s_carry, acc1_s_data, acc1_s_clear, acc1_s_valid, acc1_m_carry, acc1_m_data);
    std::cout << "acc1: " << acc1_m_data << std::endl;
    assert(acc1_m_carry ==  0);
    assert(acc1_m_data  == 10);

    // acc2 に 20 を加算
    acc2_s_sub       = 0;
    acc2_s_carry     = 0;
    acc2_s_data      = 20;
    acc2_s_clear     = 0;
    acc2_s_valid     = 1;
    elixirchip_es1_spu_op_acc(acc2, acc2_s_sub, acc2_s_carry, acc2_s_data, acc2_s_clear, acc2_s_valid, acc2_m_carry, acc2_m_data);
    std::cout << "acc2: " << acc2_m_data << std::endl;
    assert(acc2_m_carry ==  0);
    assert(acc2_m_data  == 20);

    // acc1 に 2 を加算
    acc1_s_sub       = 0;
    acc1_s_carry     = 0;
    acc1_s_data      = 2;
    acc1_s_clear     = 0;
    acc1_s_valid     = 1;
    elixirchip_es1_spu_op_acc(acc1, acc1_s_sub, acc1_s_carry, acc1_s_data, acc1_s_clear, acc1_s_valid, acc1_m_carry, acc1_m_data);
    std::cout << "acc1: " << acc1_m_data << std::endl;
    assert(acc1_m_carry == 0);
    assert(acc1_m_data ==  12);

    // acc2 に 3 を減算
    acc2_s_sub       = 1;
    acc2_s_carry     = 1;
    acc2_s_data      = 3;
    acc2_s_clear     = 0;
    acc2_s_valid     = 1;
    elixirchip_es1_spu_op_acc(acc2, acc2_s_sub, acc2_s_carry, acc2_s_data, acc2_s_clear, acc2_s_valid, acc2_m_carry, acc2_m_data);
    std::cout << "acc2: " << acc2_m_data << std::endl;
    assert(acc2_m_carry == 1);
    assert(acc2_m_data  == 17);

    // acc1 の結果と acc2 の結果を加算
    int add_s_carry = 0;
    int add_s_data0 = acc1_m_data;
    int add_s_data1 = acc2_m_data;
    int add_s_clear = 0;
    int add_s_valid = 1;
    int add_m_data;
    int add_m_carry;
    int add_m_msb_c;
    elixirchip_es1_spu_op_add(add, add_s_carry, add_s_data0, add_s_data1, add_s_clear, add_s_valid, add_m_data, add_m_carry, add_m_msb_c);
    std::cout << "add: " << add_m_data << std::endl;
    assert(add_m_data  == 12+17);
    assert(add_m_carry == 0);
    assert(add_m_msb_c == 0);


    // ---------------------------------
    //  終了処理
    // ---------------------------------

    elixirchip_es1_spu_op_acc_delete(acc1);
    elixirchip_es1_spu_op_acc_delete(acc2);


    std::cout << "end" << std::endl;

    return 0;
}

