

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_nop
        #(
            parameter   int     LATENCY    = 1                       ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                       ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]   ,   // データ型指定(オプション)
            parameter           DEVICE     = "RTL"                   ,   // デバイス名
            parameter           SIMULATION = "false"                 ,   // シミュレーション
            parameter           DEBUG      = "false"                     // デバッグ
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

    logic           s_clear ;
    data_t          s_data  ;
    logic           s_valid ;
    data_t          m_data  ;

    elixirchip_es1_spu_op_nop
            #(
                .LATENCY        (LATENCY    ),
                .DATA_BITS      (DATA_BITS  ),
                .data_t         (data_t     ),
                .DEVICE         (DEVICE     ),
                .CLEAR_DATA     ('1         ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      ) 
            )
        u_elixirchip_es1_spu_op_nop
            (
                .reset   ,
                .clk     ,
                .cke     ,

                .s_clear ,
                .s_data  ,
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

    int             sel0;
    logic   [1:0]   sel1;
    always_ff @(posedge clk) begin
        if ( cycle < 256 ) begin
            // 前半は網羅テスト
            sel0    <= int'(cycle[1:0]);
            sel1    <=   2'(cycle[3:2]);
        end
        else begin
            // 後半はランダムテスト
            sel0 <= $urandom_range(0, 3);
            sel1 <= 2'($urandom_range(0, 3));
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_clear <= '0;
            s_data  <= '0;
            s_valid <= '0;
        end
        else if ( cke ) begin
            case ( sel0 )
            0:          s_data <= '0;                      // unsigned min ALL-0
            1:          s_data <= '1;                      // unsigned max ALL-1
            default:    s_data <= data_t'($urandom());     // random
            endcase
            s_clear <= &sel1;
            s_valid <= sel1[0];
        end
    end
    
endmodule


`default_nettype wire


// end of file
