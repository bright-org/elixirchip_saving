
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_data_delay
        #(
            parameter   int     LATENCY         = 8                             ,   // レイテンシ指定
            parameter   int     DATA_BITS       = 8                             ,   // データ幅指定
            parameter   type    data_t          = logic signed [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter           DEVICE          = "RTL"                         ,   // デバイス名
            parameter           SIMULATION      = "false"                       ,   // シミュレーション
            parameter           DEBUG           = "false"                           // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var data_t          s_data  ,   // 入力データ

            output  var data_t          m_data      // 出力データ
        );

    // パイプライン遅延
    data_t  stage_data  [0:LATENCY];

    assign stage_data [0] = s_data  ;

    for ( genvar i = 1; i <= LATENCY; i++ ) begin : stage
        always_ff @( posedge clk ) begin
            if ( cke ) begin
                stage_data [i] <= stage_data [i-1];
            end
        end
    end
    
    assign m_data = stage_data[LATENCY];

endmodule


`default_nettype wire

