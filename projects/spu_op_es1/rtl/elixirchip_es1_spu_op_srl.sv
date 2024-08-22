
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_srl
        #(
            parameter   int     LATENCY         = 1                       ,   // レイテンシ指定
            parameter   int     DATA_BITS       = 8                       ,   // データ幅指定
            parameter   type    data_t          = logic [DATA_BITS-1:0]   ,   // データ型指定(オプション)
            parameter   int     MAX_SHIFT       = DATA_BITS               ,   // 最大シフト量
            parameter   int     SHIFT_BITS      = $clog2(MAX_SHIFT)       ,   // シフト量幅
            parameter   type    shift_t         = logic [SHIFT_BITS-1:0]  ,   // シフト量型指定
            parameter   data_t  CLEAR_DATA      = 'x                      ,   // m_data クリア値
            parameter   bit     IMMEDIATE_SHIFT = 1'b0                    ,   // s_shift が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA  = 1'b0                    ,   // s_data  が即値の場合に1にする(オプション)
            parameter           DEVICE          = "RTL"                   ,   // デバイス名
            parameter           SIMULATION      = "false"                 ,   // シミュレーション
            parameter           DEBUG           = "false"                     // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var shift_t         s_shift ,   // 入力シフト量
            input   var data_t          s_data  ,   // 入力データ
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var data_t          m_data      // 出力データ
        );

    // パラメータチェック
    localparam  int     LATENCY1 = LATENCY > 0 ? LATENCY : 1;
    initial begin
        assert ( LATENCY >= 0              ) else begin $error("Illegal Latency"); end
        assert ( DATA_BITS <= 32**LATENCY1 ) else begin $warning("Not recommended latency"); end
    end

    // 演算
    data_t  st0_data;
    logic   st0_clear   ;
    logic   st0_valid   ;
    assign st0_data  = s_data >> s_shift;
    assign st0_clear = s_clear;
    assign st0_valid = s_valid;

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY                ),
                .DATA_BITS  ($bits(m_data)          ),
                .CLEAR_DATA (CLEAR_DATA             ),
                .DEVICE     (DEVICE                 ),
                .SIMULATION (SIMULATION             ),
                .DEBUG      (DEBUG                  )
            )
        u_additional_latency
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (st0_data               ),
                .s_clear    (st0_clear              ),
                .s_valid    (st0_valid              ),

                .m_data     (m_data                 )
            );

endmodule


`default_nettype wire

