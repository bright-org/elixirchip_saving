

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_mulu
        #(
            parameter   int         LATENCY      = 3                                ,   // レイテンシ指定
            parameter   int         S_DATA0_BITS = 8                                ,   // s_data0 幅指定
            parameter   type        s_data0_t    = logic unsigned [S_DATA0_BITS-1:0],   // s_data0 型指定(オプション)
            parameter   int         S_DATA1_BITS = 8                                ,   // s_data1 幅指定
            parameter   type        s_data1_t    = logic unsigned [S_DATA1_BITS-1:0],   // s_data1 型指定(オプション)
            parameter   int         M_DATA_BITS  = 8                                ,   // m_data 幅指定
            parameter   type        m_data_t     = logic unsigned [M_DATA_BITS-1:0] ,   // m_data 型指定(オプション)
            parameter   int         DATA_SHIFT   = 0                                ,   // 出力前の右シフト量
            parameter   m_data_t    CLEAR_DATA   = '0                               ,   // m_data クリア値
            parameter   bit         IMMEDIATE_DATA0   = 1'b0                             ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit         IMMEDIATE_DATA1   = 1'b0                             ,   // s_data1 が即値の場合に1にする
            parameter               DEVICE       = "RTL"                            ,   // デバイス名
            parameter               SIMULATION   = "false"                          ,   // シミュレーション
            parameter               DEBUG        = "false"                              // デバッグ
            )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk         // クロック
        );

    // ランダムにCKEを下げる
    logic           cke     ;
    always_ff @( negedge clk ) begin
        cke <= ($urandom_range(0, 9) != 0);
    end

    s_data0_t       s_data0 ;
    s_data1_t       s_data1 ;
    logic           s_clear ;
    logic           s_valid ;
    m_data_t        m_data  ;

    elixirchip_es1_spu_op_mulu
            #(
                .LATENCY        (LATENCY        ),
                .S_DATA0_BITS   (S_DATA0_BITS   ),
                .s_data0_t      (s_data0_t      ),
                .S_DATA1_BITS   (S_DATA1_BITS   ),
                .s_data1_t      (s_data1_t      ),
                .M_DATA_BITS    (M_DATA_BITS    ),
                .m_data_t       (m_data_t       ),
                .DATA_SHIFT     (DATA_SHIFT     ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .IMMEDIATE_DATA0     (IMMEDIATE_DATA0     ),
                .IMMEDIATE_DATA1     (IMMEDIATE_DATA1     ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
              )
        u_elixirchip_es1_spu_op_mulu
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        ,
                .s_data1        ,
                .s_clear        ,
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

    int             sel0;
    int             sel1;
    logic   [1:0]   sel2;
    always_ff @(posedge clk) begin
        if ( cycle < 256 ) begin
            // 前半は網羅テスト
            sel0    <= int'(cycle[4:2]);
            sel1    <= int'(cycle[7:5]);
            sel2    <=   2'(cycle[1:0]);
        end
        else begin
            // 後半はランダムテスト
            sel0    <= $urandom_range(0, 7);
            sel1    <= $urandom_range(0, 7);
            sel2    <= 2'($urandom_range(0, 3));
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_data0 <= '0;
            s_data1 <= '0;
            s_clear <= 1'b0;
            s_valid <= 1'b0;
        end
        else if ( cke ) begin
            case ( sel0 )
            0:          s_data0 <= '0;                                                      // unsigned min ALL-0
            1:          s_data0 <= '1;                                                      // unsigned max ALL-1
            3:          s_data0 <=  s_data0_t'(2**($bits(s_data0)-1)  );                    // signed min
            4:          s_data0 <=  s_data0_t'(2**($bits(s_data0)-1)-1);                    // signed max
            5:          s_data0 <=  (s_data0_t'(1) << $urandom_range(0, $bits(s_data0)-1)); // one-hot
            6:          s_data0 <= ~(s_data0_t'(1) << $urandom_range(0, $bits(s_data0)-1)); // one-hot(neg)
            default:    s_data0 <= s_data0_t'($urandom());                                  // random
            endcase

            case ( sel1 )
            0:          s_data1 <= '0;                                                      // unsigned min ALL-0
            1:          s_data1 <= '1;                                                      // unsigned max ALL-1
            3:          s_data1 <=  s_data1_t'(2**($bits(s_data1)-1)  );                    // signed min
            4:          s_data1 <=  s_data1_t'(2**($bits(s_data1)-1)-1);                    // signed max
            5:          s_data1 <=  (s_data1_t'(1) << $urandom_range(0, $bits(s_data1)-1)); // one-hot
            6:          s_data1 <= ~(s_data1_t'(1) << $urandom_range(0, $bits(s_data1)-1)); // one-hot(neg)
            default:    s_data1 <= s_data1_t'($urandom());                                  // random
            endcase

            s_clear <= &sel2;
            s_valid <= sel2[0];
        end
    end
    
endmodule


`default_nettype wire


// end of file
