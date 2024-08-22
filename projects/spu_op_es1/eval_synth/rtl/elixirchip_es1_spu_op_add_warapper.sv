
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_add_warapper
        #(
            parameter   int     LATENCY    = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   bit     IMMEDIATE_CARRY = 1'b1                   ,   // s_carry が即値の場合に1にする
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                   ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                   ,   // s_data1 が即値の場合に1にする
            parameter   data_t  CLEAR_DATA  = 8'h5a                 ,   // m_data クリア値
            parameter   logic   CLEAR_CARRY = 1'b1                  ,   // m_carryクリア値
            parameter   logic   CLEAR_MSB_C = 1'b0                  ,   // m_msb_c クリア値
            parameter           DEVICE     = "ULTRASCALE_PLUS",// "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var logic           s_carry ,   // キャリー入力
            input   var data_t          s_data0 ,   // 入力データ0
            input   var data_t          s_data1 ,   // 入力データ1
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var data_t          m_data  ,   // 出力データ
            output  var logic           m_carry ,   // キャリー出力
            output  var logic           m_msb_c     // 最上位ビットのキャリー出力
        );


    elixirchip_es1_spu_op_add
            #(
                .LATENCY        (LATENCY        ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         ),
                .IMMEDIATE_CARRY     (IMMEDIATE_CARRY     ),
                .IMMEDIATE_DATA0     (IMMEDIATE_DATA0     ),
                .IMMEDIATE_DATA1     (IMMEDIATE_DATA1     ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .CLEAR_CARRY    (CLEAR_CARRY    ),
                .CLEAR_MSB_C    (CLEAR_MSB_C    ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_add
            (
                .cke            (1'b1           ),

                .*
            );

endmodule


`default_nettype wire

