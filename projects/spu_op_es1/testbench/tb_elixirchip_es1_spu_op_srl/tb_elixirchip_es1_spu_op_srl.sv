

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_srl
        #(
            parameter   int     LATENCY         = 1                       ,   // レイテンシ指定
            parameter   int     DATA_BITS       = 8                       ,   // データ幅指定
            parameter   type    data_t          = logic [DATA_BITS-1:0]   ,   // データ型指定(オプション)
            parameter   int     MAX_SHIFT       = DATA_BITS               ,   // 最大シフト量
            parameter   int     SHIFT_BITS      = $clog2(MAX_SHIFT)       ,   // シフト量幅
            parameter   type    shift_t         = logic [SHIFT_BITS-1:0]  ,   // シフト量型指定
            parameter   data_t  CLEAR_DATA      = '1                      ,   // m_data クリア値
            parameter   bit     IMMEDIATE_SHIFT = 1'b0                    ,   // s_shift が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA  = 1'b0                    ,   // s_data  が即値の場合に1にする(オプション)
            parameter           DEVICE          = "RTL"                   ,   // デバイス名
            parameter           SIMULATION      = "false"                 ,   // シミュレーション
            parameter           DEBUG           = "false"                     // デバッグ
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

    shift_t         s_shift ;   // 入力シフト量
    data_t          s_data  ;   // 入力データ
    logic           s_clear ;
    logic           s_valid ;
    data_t          m_data  ;   // 出力データ

    elixirchip_es1_spu_op_srl
            #(
                .LATENCY            (LATENCY        ),
                .DATA_BITS          (DATA_BITS      ),
                .data_t             (data_t         ),
                .MAX_SHIFT          (MAX_SHIFT      ),
                .SHIFT_BITS         (SHIFT_BITS     ),
                .shift_t            (shift_t        ),
                .CLEAR_DATA         (CLEAR_DATA     ),
                .IMMEDIATE_SHIFT    (IMMEDIATE_SHIFT),
                .IMMEDIATE_DATA     (IMMEDIATE_DATA ),
                .DEVICE             (DEVICE         ),
                .SIMULATION         (SIMULATION     ),
                .DEBUG              (DEBUG          )
            )
        u_elixirchip_es1_spu_op_srl
            (
                .reset   ,
                .clk     ,
                .cke     ,

                .s_shift ,
                .s_data  ,
                .s_clear ,
                .s_valid ,

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
        flg     <= 2'($urandom_range(0, 3));
    end
    
    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_shift <= '0;
            s_data  <= '0;
            s_clear <= 1'b0;
            s_valid <= 1'b0;
        end
        else if ( cke ) begin
            s_shift <= shift_t'($urandom_range(0, MAX_SHIFT));
            s_data  <= data_t'($urandom());    
            s_clear <= &flg;
            s_valid <= flg[0];
        end
    end
    
endmodule


`default_nettype wire


// end of file
