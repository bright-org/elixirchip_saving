defmodule SvParser do
  @moduledoc """
  Documentation for `SvParser`.
  """

  @ext ".sv"
  @doc """
  Hello world.

  ## Examples

      iex> SvParser.hello()
      :world

  """
  def run do
    files =
      Path.wildcard("./rtl copy/*" <> @ext)
      |> dbg()

    File.rm_rf("cmake/src")

    files
    |> Enum.each(&parse/1)

    file_names =
      Enum.map(
        files,
        &(&1
          |> Path.basename()
          |> Path.rootname(@ext))
      )
  end

  def parse(file_path) do
    string =
      File.read!(file_path)

    regex = ~r/^\s*(input|output)\s+\w+\s+\w+\s+(\w+)/

    %{inputs: inputs, outputs: outputs} =
      string
      |> String.split("\n")
      |> Enum.filter(&Regex.match?(regex, &1))
      |> Enum.map(fn line ->
        Regex.run(regex, line)
        [_, type, var] = Regex.run(regex, line)
        {type, var}
      end)
      |> Enum.reduce(%{inputs: [], outputs: []}, fn {type, var}, acc ->
        case type do
          "input" -> Map.update(acc, :inputs, var, fn lists -> lists ++ [var] end)
          "output" -> Map.update(acc, :outputs, var, fn lists -> lists ++ [var] end)
        end
      end)
      |> dbg()

    regex = ~r/^\s*parameter\s+\w+\s+(\w+)/

    parameters =
      string
      |> String.split("\n")
      |> Enum.filter(&Regex.match?(regex, &1))
      |> Enum.map(fn line ->
        [_, var] = Regex.run(regex, line)
        var
      end)

    # ( )();
    regex =
      ~r/(\s*#\(\s+\w+\s*.*?\s*\);)/s

    [_, arguments] =
      Regex.run(regex, string)

    [_, module_name] = Regex.run(~r/\s*module\s+(\w+)/, string)

    base_name =
      file_path
      |> Path.basename()
      |> Path.rootname(@ext)

    wrapper_name = "#{module_name}_wrapper"

    work_dir = "cmake/src/#{module_name}/"

    File.mkdir_p!(work_dir)

    File.write!(work_dir <> "#{wrapper_name}.sv", """
    `timescale 1ns / 1ps
    `default_nettype none

    module #{wrapper_name}
    #{arguments}

    // パラメータを差し替えてラッピングする
        #{module_name}
            #(
                #{list_expand(parameters)}
            )
        u_#{module_name}
            (
                #{list_expand(inputs ++ outputs)}
            );

    endmodule


    `default_nettype wire
    """)

    [_, _, _ | deps_inputs] = inputs

    File.write!(work_dir <> "#{module_name}.cpp", """
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


    #include "V#{wrapper_name}.h"
    using ModuleType = V#{wrapper_name};

    #include "#{module_name}.h"

    // コンテキスト
    struct SpuContext {
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
    void #{module_name}_create(Spu *self, const char *name)
    {
      SpuContext* ctx = new SpuContext();

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
    #{inputs |> Enum.map(&"ctx->top->#{&1} = 0") |> Enum.join(";\n")};
    ctx->top->reset       = 1;
    ctx->top->clk         = 0;
    ctx->top->cke         = 1;


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
    void #{module_name}_delete(Spu *self)
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
    void #{module_name}(
            Spu *self,
            #{c_inputs(deps_inputs)},
            #{c_outputs(outputs)}
        )
    {
    auto ctx = self->context;

    // 入力設定
    #{deps_inputs |> Enum.map(&"ctx->top->#{&1} = #{&1}") |> Enum.join(";\n")};

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
    #{outputs |> Enum.map(&"#{&1} = ctx->top->#{&1}") |> Enum.join(";\n")};
    }

    // end of file
    """)

    File.write!(work_dir <> "#{module_name}.h", """
    #ifndef __#{String.upcase(module_name)}_H__
    #define __#{String.upcase(module_name)}_H__

    #include <string>

    #ifdef __cplusplus
    extern "C" {
    #endif

    struct SpuContext;

    struct Spu {
        struct SpuContext *context;
    };

    // 作成したライブラリの関数宣言
    void    #{module_name}_create(Spu *self, const char *name);
    void    #{module_name}_delete(Spu *self);
    void    #{module_name}(
                Spu *self,
                #{c_inputs(deps_inputs)},
                #{c_outputs(outputs)}
            );

    #ifdef __cplusplus
    }
    #endif


    #endif // __ELIXIRCHIP_ES1_SPU_OP_ACC__H__

    """)

    nif_dir = Path.join(work_dir, "nif")
    File.mkdir_p!(nif_dir)

    temp =
      module_name
      |> String.split("_")
      |> Enum.map(&String.capitalize/1)
      |> Enum.join("")

    nif_module = Module.concat([SpuNif, temp])

    File.write!(nif_dir <> "/#{module_name}.cpp", """
    #include <erl_nif.h>
    #include <string.h>

    #include "#{module_name}.h"

    ErlNifResourceType *SpuType;

    void get_args(
        ErlNifEnv *env, const ERL_NIF_TERM argv[],
        #{(deps_inputs ++ outputs) |> Enum.map(&"int *#{&1}") |> Enum.join(",\n")}
        )
    {
        #{get_args(deps_inputs ++ outputs)}
    }

    void destruct_spu(ErlNifEnv *caller_env, void *obj)
    {
        Spu *spu = (Spu *)obj;
        #{module_name}_delete(spu);
    }

    int load(ErlNifEnv *caller_env, void **priv_data, ERL_NIF_TERM load_info)
    {
        SpuType = enif_open_resource_type(caller_env, "Spu", "Spu", destruct_spu, ERL_NIF_RT_CREATE, nullptr);
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
        str[bin.size] = '\\0';

        // 生成
        Spu *resource = (Spu *)enif_alloc_resource(SpuType, sizeof(Spu));
        #{module_name}_create(resource, str);
        ERL_NIF_TERM handle = enif_make_resource(env, resource);

        // リソースオブジェクトを返す
        free(str);
        return enif_make_tuple2(env, enif_make_atom(env, "ok"), handle);
    }

    ERL_NIF_TERM clk(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[])
    {
        void *resource;
        enif_get_resource(env, argv[0], SpuType, &resource);
        Spu *spu = (Spu *)resource;

        int #{Enum.join(deps_inputs ++ outputs, ", ")};
        get_args(env, argv, #{Enum.map(deps_inputs ++ outputs, &"&#{&1}") |> Enum.join(", ")});

        #{module_name}(spu, #{Enum.join(deps_inputs ++ outputs, ", ")});

        return enif_make_tuple#{length(outputs) + 1}(
            env,
            enif_make_atom(env, "ok"),
            #{enif_make_int(outputs)}
            );
    }


    static ErlNifFunc nif_funcs[] = {
        {"create", 1, create},
        {"clk", #{length(deps_inputs) + length(outputs) + 1}, clk}};

    ERL_NIF_INIT(#{nif_module}, nif_funcs, load, NULL, NULL, NULL)

    """)
  end

  def list_expand(parameters) do
    Enum.map(parameters, &expand/1)
    |> Enum.join(",\n            ")
  end

  def expand(parameter) do
    ".#{parameter} (#{parameter})"
  end

  def c_inputs(parameters) do
    Enum.map(parameters, fn x ->
      "int #{x}"
    end)
    |> Enum.join(",\n            ")
  end

  def c_outputs(parameters) do
    Enum.map(parameters, fn x ->
      "int& #{x}"
    end)
    |> Enum.join(",\n            ")
  end

  def get_args(parameters) do
    {list, _} =
      Enum.reduce(parameters, {[], 1}, fn x, {list, index} ->
        {list ++ ["enif_get_int(env, argv[#{index}], #{x});"], index + 1}
      end)

    Enum.join(list, "")
  end

  def enif_make_int(parameters) do
    Enum.map(parameters, &"enif_make_int(env, #{&1})")
    |> Enum.join(",\n")
  end
end

SvParser.run()
File.rm_rf!("../verilatorx/cmake/src")
File.mkdir_p!("../verilatorx/cmake/src")
File.cp_r!("./cmake/src", "../verilatorx/cmake/src")
