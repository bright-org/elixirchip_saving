#include <iostream>
#include <cassert>

#include "elixirchip_es1_spu_op_add.h"

int main()
{
    std::cout << "start" << std::endl;

    // ---------------------------------
    //  生成
    // ---------------------------------

    auto add8bit = elixirchip_es1_spu_op_add_create("add");


    // ---------------------------------
    // 演算 (add は副作用はないので同じbit幅なら使いまわしても構わない)
    // ---------------------------------
    
    int m_data, m_carry, m_msb_c;

    // 1 + 2    
    elixirchip_es1_spu_op_add(add8bit, 0, 1, 2, 0, 1, m_data, m_carry, m_msb_c);
    std::cout << "s_carry: 0, s_data0: 1 , s_data1: 2  -> m_data: " << m_data << ", m_carry: " << m_carry << ", m_msb_c:" << m_msb_c << std::endl;
    assert(m_carry == 0);
    assert(m_msb_c == 0);
    assert(m_data  == 1 + 2);

    // 2 + 3 + 1(carry)    
    elixirchip_es1_spu_op_add(add8bit, 1, 2, 3, 0, 1, m_data, m_carry, m_msb_c);
    std::cout << "s_carry: 1, s_data0: 2 , s_data1: 3  -> m_data: " << m_data <<  ", m_carry: " << m_carry << ", m_msb_c:" << m_msb_c << std::endl;
    assert(m_carry == 0);
    assert(m_msb_c == 0);
    assert(m_data  == 2 + 3 + 1);

    // 100 + 28 (符号付きの範囲溢れ)
    elixirchip_es1_spu_op_add(add8bit, 0, 100, 28, 0, 1, m_data, m_carry, m_msb_c);
    std::cout << "s_carry: 0, s_data0: 100 , s_data1: 28 -> m_data: " << m_data << ", m_carry: " << m_carry << ", m_msb_c:" << m_msb_c << std::endl;
    assert(m_carry == 0);
    assert(m_msb_c == 1);
    assert(m_data  == 128);

    // 128 + 128 (符号無しの範囲溢れ)
    elixirchip_es1_spu_op_add(add8bit, 0, 128, 128, 0, 1, m_data, m_carry, m_msb_c);
    std::cout << "s_carry: 0, s_data0: 128 , s_data1: 128 -> m_data: " << m_data << ", m_carry: " << m_carry << ", m_msb_c:" << m_msb_c << std::endl;
    assert(m_carry == 1);
    assert(m_msb_c == 0);
    assert(m_data  == 0);

    // 200 + 56 + 1
    elixirchip_es1_spu_op_add(add8bit, 1, 200, 56, 0, 1, m_data, m_carry, m_msb_c);
    std::cout << "s_carry: 1, s_data0: 200 , s_data1: 56 -> m_data: " << m_data << ", m_carry: " << m_carry << ", m_msb_c:" << m_msb_c << std::endl;
    assert(m_carry == 1);
    assert(m_msb_c == 1);
    assert(m_data  == 1);

    // s_valid = 0 で値キープ
    elixirchip_es1_spu_op_add(add8bit, 1, 99, 99, 0, 0, m_data, m_carry, m_msb_c);
    std::cout << "s_valid = 0 -> m_data: " << m_data << ", m_carry: " << m_carry << ", m_msb_c:" << m_msb_c << std::endl;
    assert(m_carry == 1);
    assert(m_msb_c == 1);
    assert(m_data  == 1);

    // s_clear = 1 で値クリア
    elixirchip_es1_spu_op_add(add8bit, 1, 77, 77, 1, 1, m_data, m_carry, m_msb_c);
    std::cout << "s_clear = 0 -> m_data: " << m_data << ", m_carry: " << m_carry << ", m_msb_c:" << m_msb_c << std::endl;
    assert(m_carry == 0);
    assert(m_msb_c == 0);
    assert(m_data  == 0);

    // 終了処理
    elixirchip_es1_spu_op_add_delete(add8bit);

    std::cout << "end" << std::endl;

    return 0;
}

