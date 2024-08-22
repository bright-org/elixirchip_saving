
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_mulsu
        #(
            parameter   int         LATENCY         = 3                                 ,   // レイテンシ指定
            parameter   int         S_DATA0_BITS    = 8                                 ,   // s_data0 幅指定
            parameter   type        s_data0_t       = logic signed   [S_DATA0_BITS-1:0] ,   // s_data0 型指定(オプション)
            parameter   int         S_DATA1_BITS    = 8                                 ,   // s_data1 幅指定
            parameter   type        s_data1_t       = logic unsigned [S_DATA1_BITS-1:0] ,   // s_data1 型指定(オプション)
            parameter   int         M_DATA_BITS     = 8                                 ,   // m_data 幅指定
            parameter   type        m_data_t        = logic signed   [M_DATA_BITS-1:0]  ,   // m_data 型指定(オプション)
            parameter   int         DATA_SHIFT      = 0                                 ,   // 出力前の右シフト量
            parameter   m_data_t    CLEAR_DATA      = 'x                                ,   // m_data クリア値
            parameter   bit         IMMEDIATE_DATA0 = 1'b0                              ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit         IMMEDIATE_DATA1 = 1'b0                              ,   // s_data1 が即値の場合に1にする
            parameter               DEVICE          = "RTL"                             ,   // デバイス名
            parameter               SIMULATION      = "false"                           ,   // シミュレーション
            parameter               DEBUG           = "false"                               // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var s_data0_t       s_data0 ,   // 入力データ0
            input   var s_data1_t       s_data1 ,   // 入力データ1
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var m_data_t        m_data      // 出力データ
        );


    // パラメータ
    localparam  int     CALC_BITS = $bits(s_data0_t) + $bits(s_data1_t);
    localparam  type    calc_t    = logic   signed  [CALC_BITS-1:0];

    if ( LATENCY < 3 ) begin : lut_mul
        // 演算
        m_data_t    st0_data    ;
        logic       st0_clear   ;
        logic       st0_valid   ;
        assign st0_data  = m_data_t'((calc_t'(s_data0) * calc_t'(s_data1)) >>> DATA_SHIFT);
        assign st0_clear = s_clear;
        assign st0_valid = s_valid;

        // パイプライン遅延追加
        elixirchip_es1_spu_op_nop
                #(
                    .LATENCY    (LATENCY            ),
                    .DATA_BITS  ($bits(m_data)      ),
                    .CLEAR_DATA (CLEAR_DATA         ),
                    .DEVICE     (DEVICE             ),
                    .SIMULATION (SIMULATION         ),
                    .DEBUG      (DEBUG              )
                )
            u_additional_latency
                (
                    .reset      ,
                    .clk        ,
                    .cke        ,

                    .s_data     (st0_data           ),
                    .s_clear    (st0_clear          ),
                    .s_valid    (st0_valid          ),
                    
                    .m_data     (m_data             )
                );
    end
    else begin : dsp_mul
        s_data0_t   st0_data0;
        s_data1_t   st0_data1;
        logic       st0_clear;
        logic       st0_valid;
        calc_t      st1_data;
        logic       st1_clear;
        logic       st1_valid;
        m_data_t    st2_data;
        logic       st2_valid;

        always_ff @( posedge clk ) begin
            if ( cke ) begin
                // stage0
                st0_data0 <= s_data0;
                st0_data1 <= s_data1;
                st0_clear <= s_clear;
                st0_valid <= s_valid;

                // stage1
                st1_data  <= (calc_t'(st0_data0) * calc_t'(st0_data1)) >>> DATA_SHIFT;
                st1_clear <= st0_clear;
                st1_valid <= st0_valid;

                // stage2
                if ( st1_valid ) begin
                    if ( st1_clear ) begin
                        st2_data <= CLEAR_DATA;
                    end
                    else begin
                        st2_data <= m_data_t'(st1_data);
                    end
                end
                st2_valid = st1_valid;
            end
        end
        
        // パイプライン遅延追加
        elixirchip_es1_spu_op_nop
                #(
                    .LATENCY    (LATENCY - 3        ),
                    .DATA_BITS  ($bits(m_data)      ),
                    .CLEAR_DATA ('x                 ),
                    .DEVICE     (DEVICE             ),
                    .SIMULATION (SIMULATION         ),
                    .DEBUG      (DEBUG              )
                )
            u_additional_latency
                (
                    .reset      ,
                    .clk        ,
                    .cke        ,

                    .s_data     (st2_data           ),
                    .s_clear    (1'b0               ),
                    .s_valid    (st2_valid          ),

                    .m_data     (m_data             )
                );
    end

endmodule


`default_nettype wire

