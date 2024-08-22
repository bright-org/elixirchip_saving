
`timescale 1ns / 1ps
`default_nettype none

module elixirchip_es1_spu_op_reg
        #(
            parameter   int     LATENCY    = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA = 'x                     ,   // m_data クリア値
            parameter           DEVICE     = "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var data_t          s_data  ,   // 入力データ
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 入力有効

            output  var data_t          m_data      // 出力データ
        );

    // パラメータチェック
    initial begin
        assert ( LATENCY >= 1 ) else begin $error("Illegal Latency"); end
    end

    // 演算
    data_t  st0_data;
    always_ff @( posedge clk ) begin
        if ( cke ) begin
            if ( s_clear ) begin
                st0_data <= CLEAR_DATA;
            end
            else begin
                if ( s_valid ) begin
                    st0_data <= s_data;
                end
            end
        end
    end
    
    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY - 1    ),
                .DATA_BITS  ($bits(m_data)  ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          )
            )
        u_additional_latency
            (
                .reset      (1'b0           ),
                .clk        ,
                .cke        ,

                .s_data     (st0_data       ),
                .s_clear    (1'b0           ),
                .s_valid    (1'b1           ),

                .m_data     (m_data         )
            );

endmodule


`default_nettype wire

