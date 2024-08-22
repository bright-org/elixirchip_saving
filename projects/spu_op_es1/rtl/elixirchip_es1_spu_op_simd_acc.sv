
`timescale 1ns / 1ps
`default_nettype none


(* use_dsp = "simd" *)
module elixirchip_es1_spu_op_simd_acc
        #(
            parameter   int     LATENCY    = 2                       ,   // レイテンシ指定
            parameter   int     N          = 4                       ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 12                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]   ,   // データ型指定(オプション)
            parameter           DEVICE     = "RTL"                   ,   // デバイス名
            parameter           SIMULATION = "false"                 ,   // シミュレーション
            parameter           DEBUG      = "false"                     // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var logic           s_clear ,   // 累積クリア
            input   var data_t  [N-1:0] s_data  ,   // 入力データ
            input   var logic           s_valid ,   // 有効信号

            output  var data_t  [N-1:0] m_data  ,   // 出力データ
            output  var logic   [N-1:0] m_carry     // キャリー出力
        );


    logic           st0_clear   ;
    data_t  [N-1:0] st0_data    ;
    logic           st0_valid   ;
    logic   [N-1:0] st1_carry   ;
    data_t  [N-1:0] st1_data    ;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_clear <= '0;
            st0_data  <= '0;
            st0_valid <= '0;
            st1_carry <= '0;
            st1_data  <= '0;
        end
        else if ( cke ) begin
            // stage 0
            st0_data  <= s_data;
            st0_valid <= s_valid;

            // stage 1
            for ( int i = 0; i < N; i++ ) begin
                if ( st0_valid ) begin
                    if ( st0_clear ) begin
                        {st1_carry[i], st1_data[i]} <= '0;
                    end
                    else begin
                        {st1_carry[i], st1_data[i]} <= st1_data[i] + st0_data[i];
                    end
                end
            end
        end
    end

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY - 2                ),
                .DATA_BITS  ($bits({m_carry, m_data})   ),
                .DEVICE     (DEVICE                     ),
                .SIMULATION (SIMULATION                 ),
                .DEBUG      (DEBUG                      )
            )
        u_additional_latency
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     ({st1_carry, st1_data}      ),

                .m_data     ({m_carry,   m_data}        )
            );

endmodule


`default_nettype wire
