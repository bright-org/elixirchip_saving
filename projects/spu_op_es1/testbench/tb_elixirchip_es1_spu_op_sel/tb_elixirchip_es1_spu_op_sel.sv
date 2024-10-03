

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_sel
        #(
            parameter   int     LATENCY        = 1                      ,   // レイテンシ指定
            parameter   int     N              = 4                      ,   // 入力データ数
            parameter   int     SEL_BITS       = $clog2(N)              ,   // セレクタの幅
            parameter   type    sel_t          = logic [SEL_BITS-1:0]   ,   // データ型指定(オプション)
            parameter   int     DATA_BITS      = 8                      ,   // データ幅指定
            parameter   type    data_t         = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA     = '1                     ,   // m_data クリア値
            parameter   bit     IMMEDIATE_SEL  = 1'b0                   ,   // s_sel が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA = 1'b0                   ,   // s_data が即値の場合に1にする(オプション)
            parameter           DEVICE         = "RTL"                  ,   // デバイス名
            parameter           SIMULATION     = "false"                ,   // シミュレーション
            parameter           DEBUG          = "false"                    // デバッグ
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

    sel_t           s_sel   ;
    data_t  [N-1:0] s_data  ;
    logic           s_clear ;
    logic           s_valid ;
    data_t          m_data  ;

    elixirchip_es1_spu_op_sel
            #(
                .LATENCY        (LATENCY        ),
                .N              (N              ),
                .SEL_BITS       (SEL_BITS       ),
                .sel_t          (sel_t          ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .IMMEDIATE_SEL  (IMMEDIATE_SEL  ),
                .IMMEDIATE_DATA (IMMEDIATE_DATA ),
                .USE_CLEAR      (1'b1           ),
                .USE_VALID      (1'b1           ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_sel
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_sel      ,
                .s_data     ,
                .s_clear    ,
                .s_valid    ,

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

    logic   [1:0]   flg ;
    always_ff @(posedge clk) begin
        if ( cke ) begin
            flg <= 2'($urandom_range(0, 3));
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_sel   <= '0;
            s_data  <= '0;
            s_clear <= '0;
            s_valid <= '0;
        end
        else if ( cke ) begin
            s_sel   <=  sel_t'($urandom_range(0, N-1));
            for ( int i = 0; i < N; i++ ) begin
                s_data[i] <=  data_t'($urandom());
            end
            s_clear <= &flg;
            s_valid <= flg[0];
        end
    end
    
endmodule


`default_nettype wire


// end of file
