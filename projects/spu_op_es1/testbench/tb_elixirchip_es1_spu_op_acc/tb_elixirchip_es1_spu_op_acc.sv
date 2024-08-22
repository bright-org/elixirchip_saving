

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_acc
        #(
            parameter   int         LATENCY      = 1                                ,   // レイテンシ指定
            parameter   int         S_DATA_BITS  = 8                                ,   // s_data 幅指定
            parameter   type        s_data_t     = logic signed [S_DATA_BITS-1:0]   ,   // s_data 型指定(オプション)
            parameter   int         M_DATA_BITS  = 8                                ,   // m_data 幅指定
            parameter   type        m_data_t     = logic signed [M_DATA_BITS-1:0]   ,   // m_data 型指定(オプション)
            parameter   m_data_t    CLEAR_DATA   = 'x                               ,   // m_data クリア値
            parameter   logic       CLEAR_CARRY  = 'x                               ,   // m_carryクリア値
            parameter   bit         IMMEDIATE_DATA    = 1'b0                             ,   // s_data が即値の場合に1にする
            parameter               DEVICE       = "RTL"                            ,   // デバイス名
            parameter               SIMULATION   = "false"                          ,   // シミュレーション
            parameter               DEBUG        = "false"                              // デバッグ
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

    logic           s_carry ;
    logic           s_sub   ;
    s_data_t        s_data  ;
    logic           s_valid ;
    logic           s_clear ;
    logic           m_carry ;
    m_data_t        m_data  ;

    elixirchip_es1_spu_op_acc
            #(
                .LATENCY        (LATENCY        ),
                .S_DATA_BITS    (S_DATA_BITS    ),
                .s_data_t       (s_data_t       ),
                .M_DATA_BITS    (M_DATA_BITS    ),
                .m_data_t       (m_data_t       ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .CLEAR_CARRY    (CLEAR_CARRY    ),
                .IMMEDIATE_DATA      (IMMEDIATE_DATA      ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_acc
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_carry        ,
                .s_sub          ,
                .s_data         ,

                .s_valid        ,
                .s_clear        ,
                .m_carry        ,
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
            s_carry <= cycle[1];
            s_sub   <= cycle[2];
            sel0    <= int'(cycle[6:3]);
            sel1    <= int'(cycle[10:7]);
        end
        else begin
            // 前半は網羅テスト
            s_valid <= $urandom_range(0, 10) != 0;
            s_carry <= $urandom_range(0, 10) == 0;
            s_sub   <= $urandom_range(0,  3) == 0;
            sel0    <= $urandom_range(0, 8);
            sel1    <= $urandom_range(0, 8);
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_clear  <= '0;
            s_data   <= '0;
        end
        else if ( cke ) begin
            case ( sel1 )
            0:          s_data <= '0;
            1:          s_data <= '1;
            2:          s_data <= ~(s_data_t'(1) << $urandom_range(0, S_DATA_BITS-1));
            3:          s_data <=  (s_data_t'(1) << $urandom_range(0, S_DATA_BITS-1));
            default:    s_data <= s_data_t'($urandom());
            endcase
        end
    end
    

endmodule


`default_nettype wire


// end of file
