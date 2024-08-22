

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_mac
        #(
            parameter   int     LATENCY      = 1                                ,   // レイテンシ指定
            parameter   int     S_DATA0_BITS = 8                                ,   // s_data1 幅指定
            parameter   type    s_data0_t    = logic signed [S_DATA0_BITS-1:0]  ,   // s_data0 型指定(オプション)
            parameter   int     S_DATA1_BITS = 8                                ,   // s_data1 幅指定
            parameter   type    s_data1_t    = logic signed [S_DATA1_BITS-1:0]  ,   // s_data1 型指定(オプション)
            parameter   int     M_DATA_BITS  = 8                                ,   // m_data 幅指定
            parameter   type    m_data_t     = logic signed [M_DATA_BITS-1:0]   ,   // m_data 型指定(オプション)
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                               ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                               ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE       = "RTL"                            ,   // デバイス名
            parameter           SIMULATION   = "false"                          ,   // シミュレーション
            parameter           DEBUG        = "false"                              // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk         // クロック
        );

    // ランダムにCKEを下げる
    logic           cke     = 1'b1;
    always_ff @( negedge clk ) begin
        cke <= $urandom_range(0, 9) != 0;
    end

    logic           s_set   ;
    logic           s_sub   ;
    s_data0_t       s_data0 ;
    s_data1_t       s_data1 ;
    logic           s_valid ;
    m_data_t        m_data  ;

    elixirchip_es1_spu_op_mac
            #(
                .LATENCY        (LATENCY        ),
                .S_DATA0_BITS   (S_DATA0_BITS   ),
                .s_data0_t      (s_data0_t      ),
                .S_DATA1_BITS   (S_DATA1_BITS   ),
                .s_data1_t      (s_data1_t      ),
                .M_DATA_BITS    (M_DATA_BITS    ),
                .m_data_t       (m_data_t       ),
                .IMMEDIATE_DATA0     (IMMEDIATE_DATA0     ),
                .IMMEDIATE_DATA1     (IMMEDIATE_DATA1     ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_mac
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_set          ,
                .s_sub          ,
                .s_data0        ,
                .s_data1        ,
                .s_valid        ,
                
                .m_data         
            );


    // -----------------------------------------
    //  testbench
    // -----------------------------------------

    int     cycle = 0;
    always_ff @(posedge clk) begin
        if ( reset ) begin
            cycle <= 0;
        end
        else if ( cke ) begin
            cycle <= cycle + 1;
        end
    end

    int     sel0;
    int     sel1;
    always_ff @(posedge clk) begin
        if ( cycle < 2048 ) begin
            // 前半は網羅テスト
            s_valid <= cycle[0];
            s_set   <= cycle[1];
            s_sub   <= cycle[2];
            sel0    <= int'(cycle[6:3]);
            sel1    <= int'(cycle[10:7]);
        end
        else begin
            // 前半は網羅テスト
            s_valid <= $urandom_range(0, 10) != 0;
            s_set   <= $urandom_range(0, 10) == 0;
            s_sub   <= $urandom_range(0,  3) == 0;
            sel0    <= $urandom_range(0, 8);
            sel1    <= $urandom_range(0, 8);
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_data0 <= '0;
            s_data1 <= '0;
        end
        else if ( cke ) begin
            case ( sel0 )
            0:          s_data0 <= '0;
            1:          s_data0 <= '1;
            2:          s_data0 <= ~(s_data0_t'(1) << $urandom_range(0, S_DATA0_BITS-1));
            3:          s_data0 <=  (s_data0_t'(1) << $urandom_range(0, S_DATA0_BITS-1));
            default:    s_data0 <= s_data0_t'($urandom());
            endcase

            case ( sel1 )
            0:          s_data1 <= '0;
            1:          s_data1 <= '1;
            2:          s_data1 <= ~(s_data1_t'(1) << $urandom_range(0, S_DATA1_BITS-1));
            3:          s_data1 <=  (s_data1_t'(1) << $urandom_range(0, S_DATA1_BITS-1));
            default:    s_data1 <= s_data1_t'($urandom());
            endcase
        end
    end
    

endmodule


`default_nettype wire


// end of file
