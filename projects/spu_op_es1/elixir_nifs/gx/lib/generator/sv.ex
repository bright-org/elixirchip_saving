defmodule Generator.Sv do
  import Generator

  def sv() do
    File.write!(join_base_path("spu/elixirchip_es1_spu_op_acc_wrapper.sv"), ~S"""

    `timescale 1ns / 1ps
    `default_nettype none

    module
     elixirchip_es1_spu_op_acc_wrapper
        #(
            parameter   int         LATENCY        = 1                              ,   // レイテンシ指定
            parameter   int         S_DATA_BITS    = 8                              ,   // s_data0 幅指定
            parameter   type        s_data_t       = logic signed [S_DATA_BITS-1:0] ,   // s_data0 型指定(オプション)
            parameter   int         M_DATA_BITS    = 8                              ,   // m_data 幅指定
            parameter   type        m_data_t       = logic signed [M_DATA_BITS-1:0] ,   // m_data 型指定(オプション)
            parameter   m_data_t    CLEAR_DATA     = '0                             ,   // m_data クリア値
            parameter   logic       CLEAR_CARRY    = '0                             ,   // m_carryクリア値
            parameter   bit         IMMEDIATE_DATA = 1'b0                           ,   // s_data0 が即値の場合に1にする(オプション)
            parameter               DEVICE         = "RTL"                          ,   // デバイス名
            parameter               SIMULATION     = "false"                        ,   // シミュレーション
            parameter               DEBUG          = "false"                            // デバッグ
        )
        (
            input   var logic           reset       ,   // 同期リセット(制論理)
            input   var logic           clk         ,   // クロック
            input   var logic           cke         ,   // クロックイネーブル

            input   var logic           s_sub       ,   // 1の時にアキュミュレータの演算を加算ではなく減算にする
            input   var logic           s_carry     ,   // キャリー入力 (sub 時は 0 でボローあり)
            input   var s_data_t        s_data      ,   // 入力データ
            input   var logic           s_clear     ,   // クリア
            input   var logic           s_valid     ,   // 1の時有効データ

            output  var logic           m_carry     ,   // キャリー
            output  var m_data_t        m_data          // 出力データ
        );

    // パラメータを差し替えてラッピングする
    elixirchip_es1_spu_op_acc
            #(
                .LATENCY        (LATENCY        ),
                .S_DATA_BITS    (S_DATA_BITS    ),
                .s_data_t       (s_data_t       ),
                .M_DATA_BITS    (M_DATA_BITS    ),
                .m_data_t       (m_data_t       ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .CLEAR_CARRY    (CLEAR_CARRY    ),
                .IMMEDIATE_DATA (IMMEDIATE_DATA ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_acc
            (
                .reset          (reset          ),
                .clk            (clk            ),
                .cke            (cke            ),
                .s_sub          (s_sub          ),
                .s_carry        (s_carry        ),
                .s_data         (s_data         ),
                .s_clear        (s_clear        ),
                .s_valid        (s_valid        ),
                .m_carry        (m_carry        ),
                .m_data         (m_data         )
            );

    endmodule


    `default_nettype wire
    """)
  end

  def sv_cmakelist() do
    File.write!(join_base_path("spu/CMakeLists.txt"), """

    cmake_minimum_required(VERSION 3.16)

    set(TARGET elixirchip_es1_spu_op_acc)

    project(${TARGET})

    find_package(verilator 4.218 REQUIRED HINTS $ENV{VERILATOR_ROOT} ${VERILATOR_ROOT})
    if (NOT verilator_FOUND)
    message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
    endif()

    add_library(${TARGET} STATIC ./${TARGET}.cpp)
    set_target_properties(${TARGET} PROPERTIES POSITION_INDEPENDENT_CODE ON)

    set(CMAKE_CXX_STANDARD 14)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)

    verilate(${TARGET}
    VERILATOR_ARGS -D__VERILATOR__ -O3 -y /src/rtl # --assert --trace-fst --trace-params --trace-structs --trace-underscore
    SOURCES ./${TARGET}_wrapper.sv
    )

    """)
  end
end
