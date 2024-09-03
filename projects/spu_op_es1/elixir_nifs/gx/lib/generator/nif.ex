defmodule Generator.Cmake do
  import Generator

  def sv_wrapper_header() do
    File.write!(join_base_path("spu/elixirchip_es1_spu_op_acc.h"), ~S"""


    #ifndef __ELIXIRCHIP_ES1_SPU_OP_ACC__H__
    #define __ELIXIRCHIP_ES1_SPU_OP_ACC__H__

    #include <string>

    #ifdef __cplusplus
    extern "C" {
    #endif

    struct SpuAccContext;

    struct SpuAcc {
        struct SpuAccContext *context;
    };


    // 作成したライブラリの関数宣言
    void    elixirchip_es1_spu_op_acc_create(SpuAcc *self, const char *name);
    void    elixirchip_es1_spu_op_acc_delete(SpuAcc *self);
    void    elixirchip_es1_spu_op_acc(
                SpuAcc *self,
                int s_sub,
                int s_carry,
                int s_data,
                int s_clear,
                int s_valid,
                # int& m_carry,
                int& m_data
            );

    #ifdef __cplusplus
    }
    #endif


    #endif // __ELIXIRCHIP_ES1_SPU_OP_ACC__H__

    """)
  end

  def sv_wrapper_cpp() do
    File.write!(join_base_path("spu/elixirchip_es1_spu_op_acc.cpp"), ~S"""


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

    """)
  end

  def sv_nif_cpp() do
    File.write!(join_base_path("spu_nif/wrapper_call.cpp"), ~S"""
    #include <erl_nif.h>
    #include <string.h>

    #include "elixirchip_es1_spu_op_acc.h"

    ErlNifResourceType *SpuAccType;

    void get_args(
        ErlNifEnv *env, const ERL_NIF_TERM argv[],
        int *s_sub,
        int *s_carry,
        int *s_data,
        int *s_clear,
        int *s_valid,
        int *m_carry,
        int *m_data)
    {
        enif_get_int(env, argv[1], s_sub);
        enif_get_int(env, argv[2], s_carry);
        enif_get_int(env, argv[3], s_data);
        enif_get_int(env, argv[4], s_clear);
        enif_get_int(env, argv[5], s_valid);
        enif_get_int(env, argv[6], m_carry);
        enif_get_int(env, argv[7], m_data);
    }

    void destruct_spu_acc(ErlNifEnv *caller_env, void *obj)
    {
        enif_fprintf(stdout, "destruct %p\n", obj);
        SpuAcc *spu_acc = (SpuAcc *)obj;
        elixirchip_es1_spu_op_acc_delete(spu_acc);
    }

    int load(ErlNifEnv *caller_env, void **priv_data, ERL_NIF_TERM load_info)
    {
        SpuAccType = enif_open_resource_type(caller_env, "SpuAcc", "SpuAcc", destruct_spu_acc, ERL_NIF_RT_CREATE, nullptr);
        return 0;
    }

    ERL_NIF_TERM create(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[])
    {
        // 文字列取り出し
        ErlNifBinary bin;
        if (!enif_inspect_binary(env, argv[0], &bin))
        {
            return enif_make_badarg(env);
        }
        char *str = (char *)malloc(bin.size + 1);
        memcpy(str, bin.data, bin.size);
        str[bin.size] = '\0';

        // 生成
        SpuAcc *resource = (SpuAcc *)enif_alloc_resource(SpuAccType, sizeof(SpuAcc));
        elixirchip_es1_spu_op_acc_create(resource, str);
        ERL_NIF_TERM handle = enif_make_resource(env, resource);

        // リソースオブジェクトを返す
        free(str);
        return enif_make_tuple2(env, enif_make_atom(env, "ok"), handle);
    }

    ERL_NIF_TERM acc_clk(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[])
    {
        void *resource;
        enif_get_resource(env, argv[0], SpuAccType, &resource);
        SpuAcc *spu = (SpuAcc *)resource;

        int s_sub, s_carry, s_data, s_clear, s_valid, m_carry, m_data;
        get_args(env, argv, &s_sub, &s_carry, &s_data, &s_clear, &s_valid, &m_carry, &m_data);

        elixirchip_es1_spu_op_acc(spu, s_sub, s_carry, s_data, s_clear, s_valid, m_carry, m_data);
        // enif_fprintf(stdout, "test %p\n", m_data);

        return enif_make_tuple3(
            env,
            enif_make_atom(env, "ok"),
            enif_make_int(env, m_carry),
            enif_make_int(env, m_data)
            );
    }

    static ErlNifFunc nif_funcs[] = {
        {"create", 1, create},
        {"acc_clk", 8, acc_clk}};

    ERL_NIF_INIT(Elixir.SpuNif, nif_funcs, load, NULL, NULL, NULL)

    """)
  end

  def nif_cmakelists() do
    File.write!(join_base_path("spu_nif/CMakeLists.txt"), ~S"""
    file(GLOB EXAMPLE_SRC ./*.cpp)

    include_directories(
    ../spu
    )

    link_directories(
    ../spu/build
    )

    add_library(spu SHARED ${EXAMPLE_SRC})

    # ライブラリの名前を 任意の名前に変更
    set_target_properties(spu PROPERTIES OUTPUT_NAME "spu" PREFIX "" SUFFIX ".so")
    target_link_libraries(spu
    pthread
    elixirchip_es1_spu_op_acc
    )
    """)
  end
end
