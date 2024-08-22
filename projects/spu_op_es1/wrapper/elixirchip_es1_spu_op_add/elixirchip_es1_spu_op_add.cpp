

#include <verilated.h>

#include "Velixirchip_es1_spu_op_add_wrapper.h"
using ModuleType = Velixirchip_es1_spu_op_add_wrapper;

#include "elixirchip_es1_spu_op_add.h"

// コンテキスト
struct Context {
    std::shared_ptr<VerilatedContext>   contextp;
    std::shared_ptr<ModuleType>         top;
};

// 生成
void* elixirchip_es1_spu_op_add_create(const char *name)
{
    Context* ctx = new Context();

    // モデル生成
    ctx->contextp = std::make_shared<VerilatedContext>();
    ctx->contextp->debug(0);
    ctx->contextp->randReset(2);
//  ctx->contextp->commandArgs(argc, argv);
    ctx->top = std::make_shared<ModuleType>(ctx->contextp.get(), "top");

    // 初期化
    ctx->top->reset   = 1;
    ctx->top->clk     = 0;
    ctx->top->cke     = 1;
    ctx->top->s_carry = 0;
    ctx->top->s_data0 = 0;
    ctx->top->s_data1 = 0;

    // リセット期間
    for ( int i = 0; i < 16; i++ )
    {
        ctx->top->clk = 0;
        ctx->top->eval();
        ctx->top->clk = 1;
        ctx->top->eval();
    }
    ctx->top->reset   = 0;

    return ctx;
}

// 破棄
void elixirchip_es1_spu_op_add_delete(void* handle)
{
    auto ctx = static_cast<Context*>(handle);

    ctx->top->final();
    delete ctx;
}

// 演算
void elixirchip_es1_spu_op_add(
            void* handle,
            int s_carry,
            int s_data0,
            int s_data1,
            int s_clear,
            int s_valid,
            int& m_data,
            int& m_carry,
            int& m_msb_c
        )
{
    auto ctx = static_cast<Context*>(handle);

    // 入力設定
    ctx->top->s_carry = s_carry;
    ctx->top->s_data0 = s_data0;
    ctx->top->s_data1 = s_data1;
    ctx->top->s_clear = s_clear;
    ctx->top->s_valid = s_valid;

    // latency 分クロックを入れる
    for ( int i = 0; i < 1; i++ ) {
        ctx->top->clk = 0;
        ctx->top->eval();
        ctx->top->clk = 1;
        ctx->top->eval();
    }

    // 結果取り出し
    m_data  = ctx->top->m_data;
    m_carry = ctx->top->m_carry;
    m_msb_c = ctx->top->m_msb_c;
}

// end of file
