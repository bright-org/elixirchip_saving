
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_mac
        #(
            parameter   int     LATENCY         = 3                                 ,   // レイテンシ指定
            parameter   int     S_DATA0_BITS    = 8                                 ,   // s_data0 幅指定
            parameter   type    s_data0_t       = logic signed [S_DATA0_BITS-1:0]   ,   // s_data0 型指定(オプション)
            parameter   int     S_DATA1_BITS    = 8                                 ,   // s_data1 幅指定
            parameter   type    s_data1_t       = logic signed [S_DATA1_BITS-1:0]   ,   // s_data1 型指定(オプション)
            parameter   int     M_DATA_BITS     = 8                                 ,   // m_data 幅指定
            parameter   type    m_data_t        = logic signed [M_DATA_BITS-1:0]    ,   // m_data 型指定(オプション)
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                              ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                              ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE          = "RTL"                             ,   // デバイス名
            parameter           SIMULATION      = "false"                           ,   // シミュレーション
            parameter           DEBUG           = "false"                               // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var logic           s_set   ,   // 1の時にアキュミュレータは積算せずに新しい値をセット
            input   var logic           s_sub   ,   // 1の時にアキュミュレータの演算を加算ではなく減算にする
            input   var s_data0_t       s_data0 ,   // 入力データ0
            input   var s_data1_t       s_data1 ,   // 入力データ1
            input   var logic           s_valid ,   // 1の時有効データ

            output  var m_data_t        m_data      // 出力データ
        );

    // パラメータ
    localparam  int     CALC_BITS = $bits(s_data0_t) + $bits(s_data1_t);
    localparam  type    calc_t    = logic signed [CALC_BITS-1:0];

    logic       st0_set     ;
    logic       st0_sub     ;
    s_data0_t   st0_data0   ;
    s_data1_t   st0_data1   ;
    logic       st0_valid   ;

    logic       st1_set     ;
    logic       st1_sub     ;
    calc_t      st1_data    ;
    logic       st1_valid   ;

    m_data_t    st2_data    ;

    /*
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_valid <= 1'b0;
            st1_valid <= 1'b0;
        end
        else if ( cke ) begin
            st0_valid <= s_valid;
            st1_valid <= st0_valid;
        end
    end
    */

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_set   <= 'x     ;
            st0_sub   <= 'x     ;
            st0_data0 <= 'x     ;
            st0_data1 <= 'x     ;
            st0_valid <= 1'b0   ;
            st1_set   <= 'x     ;
            st1_sub   <= 'x     ;
            st1_data  <= 'x     ;
            st1_valid <= 1'b0   ;
            st2_data  <= '0     ;
        end
        else if ( cke ) begin
            // stage0
            st0_set   <= s_set;
            st0_sub   <= s_sub;
            st0_data0 <= s_data0;
            st0_data1 <= s_data1;
            st0_valid <= s_valid;

            // stage1
            st1_set   <= st0_set;
            st1_sub   <= st0_sub;
            st1_data  <= st0_data0 * st0_data1;
            st1_valid <= st0_valid;

            // stage2
            if ( st1_valid ) begin
                if ( st1_set ) begin
                    st2_data <= m_data_t'(st1_data);
                end
                else begin
                    if ( st1_sub ) begin
                        st2_data <= st2_data - m_data_t'(st1_data);
                    end
                    else begin
                        st2_data <= st2_data + m_data_t'(st1_data);
                    end
                end
            end
        end
    end

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY - 3        ),
                .DATA_BITS  ($bits(m_data)      ),
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
                .s_valid    (1'b1               ),

                .m_data     (m_data             )
            );

endmodule


`default_nettype wire

