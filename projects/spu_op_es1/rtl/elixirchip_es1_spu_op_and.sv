
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_and
        #(
            parameter   int     LATENCY         = 1                     ,   // レイテンシ指定
            parameter   int     DATA_BITS       = 8                     ,   // データ幅指定
            parameter   type    data_t          = logic [DATA_BITS-1:0] ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA      = 'x                    ,   // m_data クリア値
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                  ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                  ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE          = "RTL"                 ,   // デバイス名
            parameter           SIMULATION      = "false"               ,   // シミュレーション
            parameter           DEBUG           = "false"                   // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var data_t          s_data0 ,   // 入力データ0
            input   var data_t          s_data1 ,   // 入力データ1
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var data_t          m_data      // 出力データ
        );
    
    // パラメータチェック
    initial begin
        assert ( LATENCY >= 0 ) else begin $error("Illegal Latency"); end
//      assert ( LATENCY >= 1 ) else begin $warning("Not recommended latency"); end
    end

    // 演算
    data_t  st0_data    ;
    logic   st0_clear   ;
    logic   st0_valid   ;
    assign st0_data  = s_data0 & s_data1;
    assign st0_clear = s_clear;
    assign st0_valid = s_valid;

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY        ),
                .DATA_BITS  ($bits(m_data)  ),
                .CLEAR_DATA (CLEAR_DATA     ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          )
            )
        u_additional_latency
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (st0_data       ),
                .s_clear    (st0_clear      ),
                .s_valid    (st0_valid      ),

                .m_data     (m_data         )
            );

endmodule


`default_nettype wire

