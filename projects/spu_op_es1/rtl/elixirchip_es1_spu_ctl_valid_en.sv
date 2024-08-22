
`timescale 1ns / 1ps
`default_nettype none

// valid信号のマスク
module elixirchip_es1_spu_ctl_valid_en
        #(
            parameter int       LATENCY   = 1           ,   // レイテンシ指定
            parameter           DEVICE     = "RTL"      ,   // デバイス名
            parameter           SIMULATION = "false"    ,   // シミュレーション
            parameter           DEBUG      = "false"        // デバッグ
        )
        (
            input   var logic       reset       ,   // 同期リセット(制論理)
            input   var logic       clk         ,   // クロック
            input   var logic       cke         ,   // クロックイネーブル

            input   var logic       s_enable    ,   // 有効化入力
            input   var logic       s_valid     ,   // 信号有効

            output  var logic       m_valid         // 信号有効   
        );

    // パラメータチェック
    initial begin
        assert ( LATENCY >= 0 ) else begin $error("Error: LATENCY must be positive value."); end
        assert ( LATENCY >= 1 ) else begin $warning("Not recommended latency"); end
    end

    // パイプライン遅延
    logic       stage_valid [0:LATENCY];
    assign stage_valid[0] = s_valid & s_enable;

    for ( genvar i = 0; i < LATENCY; i++ ) begin : stage
        always_ff @( posedge clk ) begin
            if ( reset ) begin
                stage_valid[i+1] <= 1'b0;
            end
            else if ( cke ) begin
                stage_valid[i+1] <= stage_valid[i];
            end
        end
    end

    assign m_valid = stage_valid[LATENCY];

endmodule


`default_nettype wire

