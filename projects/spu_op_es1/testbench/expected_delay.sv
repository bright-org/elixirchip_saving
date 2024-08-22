
`timescale 1ns / 1ps
`default_nettype none


// SVA でサイクル遅延記述ができない verilator でも検証できるように期待値遅延モジュールを作成
module expected_delay
        #(
            parameter   int     LATENCY       = 1                           ,   // レイテンシ指定
            parameter   int     EXPECTED_BITS = 8                           ,   // データ幅指定
            parameter   type    data_t        = logic [EXPECTED_BITS-1:0]   ,   // データ型指定(オプション)
            parameter           DEVICE        = "RTL"                       ,   // デバイス名
            parameter           SIMULATION    = "false"                     ,   // シミュレーション
            parameter           DEBUG         = "false"                         // デバッグ
        )
        (
            input   var logic           reset       ,   // 同期リセット(制論理)
            input   var logic           clk         ,   // クロック
            input   var logic           cke         ,   // クロックイネーブル

            input   var data_t          s_data      ,   // 期待値データ
            input   var logic           s_valid     ,   // 期待値データが有効かどうか

            output  var data_t          m_data      ,   // 遅延させた期待値データ
            output  var logic           m_valid         // 遅延させた期待値データが有効かどうか
        );

    // LATENCY が負の値ならエラーにする
    initial begin
        assert ( LATENCY >= 0 ) else begin $error("Illegal Latency"); $finish; end
    end

    // パイプライン遅延
    data_t  delay_data [0:LATENCY];
    logic       delay_valid     [0:LATENCY];
    assign delay_data[0]  = s_data;
    assign delay_valid[0] = s_valid;

    for ( genvar i = 0; i < LATENCY; i++ ) begin : stage
        always_ff @( posedge clk ) begin
            if ( reset ) begin
                delay_data[i+1]  <= 'x;
                delay_valid[i+1] <= 1'b0;
            end
            else if ( cke ) begin
                delay_data[i+1]  <= delay_data[i];
                delay_valid[i+1] <= delay_valid[i];
            end
        end
    end

    assign m_data  = delay_data[LATENCY];
    assign m_valid = delay_valid[LATENCY];

endmodule


`default_nettype wire

