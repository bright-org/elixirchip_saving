

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_ctl_valid_en
        #(
            parameter   int     LATENCY    = 1                       ,   // レイテンシ指定
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

    logic           s_enable;
    logic           s_valid  ;
    logic           m_valid  ;

    elixirchip_es1_spu_ctl_valid_en
            #(
                .LATENCY        (LATENCY    ),
                .DEVICE         (DEVICE     ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      ) 
            )
        u_elixirchip_es1_spu_ctl_valid
            (
                .reset   ,
                .clk     ,
                .cke     ,

                .s_enable,
                .s_valid ,

                .m_valid  
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

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_enable <= 'x;
            s_valid  <= '0;
        end
        else if ( cke ) begin
            s_enable <= 1'($urandom_range(0, 1));
            s_valid  <= 1'($urandom_range(0, 1));
        end
    end
    
endmodule


`default_nettype wire


// end of file
