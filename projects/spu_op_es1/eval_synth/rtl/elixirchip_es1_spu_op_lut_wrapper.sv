
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_lut_wrapper
        #(
            parameter   int                         LATENCY      = 1                        ,   // レイテンシ指定
            parameter   int                         TABLE_SIZE   = 64                       ,   // テーブルサイズ
            parameter   int                         ADDR_BITS    = $clog2(TABLE_SIZE)       ,   // アドレス幅
            parameter   type                        addr_t       = logic [ADDR_BITS-1:0]    ,   // データ型指定(オプション)
            parameter   int                         DATA_BITS    = 1                        ,   // データ幅指定
            parameter   type                        data_t       = logic [DATA_BITS-1:0]    ,   // データ型指定(オプション)
            parameter   data_t                      CLEAR_DATA   = '0                       ,   // m_data クリア値
            parameter   data_t  [TABLE_SIZE-1:0]    TABLE_VALUES = '{0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0},
                                                                                                // テーブルデータ
            parameter                               DEVICE       = "ULTRASCALE_PLUS",// "RTL"                    ,   // デバイス名
            parameter                               SIMULATION   = "false"                  ,   // シミュレーション
            parameter                               DEBUG        = "false"                      // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var addr_t          s_addr  ,   // アドレス入力
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var data_t          m_data      // 出力データ
        );


    elixirchip_es1_spu_op_lut
            #(
                .LATENCY        (LATENCY        ),
                .TABLE_SIZE     (TABLE_SIZE     ),
                .ADDR_BITS      (ADDR_BITS      ),
                .addr_t         (addr_t         ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .TABLE_VALUES   (TABLE_VALUES   ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_lut
            (
                .cke            (1'b1           ),
                .*
            );


endmodule


`default_nettype wire

