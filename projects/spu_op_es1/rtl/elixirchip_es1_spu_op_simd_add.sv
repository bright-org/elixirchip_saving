
`timescale 1ns / 1ps
`default_nettype none


(* use_dsp = "simd" *)
module elixirchip_es1_spu_op_simd_add
        #(
            parameter   int     LATENCY         = 2                     ,   // レイテンシ指定
            parameter   int     N               = 4                     ,   // レイテンシ指定
            parameter   int     DATA_BITS       = 12                    ,   // データ幅指定
            parameter   type    data_t          = logic [DATA_BITS-1:0] ,   // データ型指定(オプション)
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

            input   var data_t  [N-1:0] s_data0 ,   // 入力データ0
            input   var data_t  [N-1:0] s_data1 ,   // 入力データ1

            output  var data_t  [N-1:0] m_data  ,   // 出力データ
            output  var logic   [N-1:0] m_carry     // キャリー出力
        );

    data_t  [N-1:0] st0_data0   ;
    data_t  [N-1:0] st0_data1   ;
    logic   [N-1:0] st1_carry   ;
    data_t  [N-1:0] st1_data    ;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_data0 <= '0;
            st0_data1 <= '0;
            st1_carry <= '0;
            st1_data  <= '0;
        end
        else if ( cke ) begin
            // stage 0
            st0_data0 <= s_data0;
            st0_data1 <= s_data1;

            // stage 1
            for ( int i = 0; i < N; i++ ) begin
                {st1_carry[i], st1_data[i]} <= st0_data0[i] + st0_data1[i];
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
