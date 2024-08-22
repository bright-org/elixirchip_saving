

`timescale 1ns / 1ps
`default_nettype none


// 以降は Verilator で C++ のテストドライバも使えるように時間待ちを書かない
module tb_main
        #(
            parameter           DEVICE     = "RTL"   ,   // デバイス名
            parameter           SIMULATION = "true"  ,   // シミュレーション
            parameter           DEBUG      = "false"     // デバッグ
        )
        (
            input   var logic       reset       ,
            input   var logic       clk25       ,
            input   var logic       clk125      ,
            input   var logic       clk580      ,
            input   var logic       ether0_clk  ,
            input   var logic       ether1_clk  
        );

    // -----------------------------------------
    //  top
    // -----------------------------------------

    var logic            fan_en          ;
    var logic            in_clk25a       ;
    var logic            in_clk25b       ;
    var logic    [1:0]   led             ;
    var logic            rgmii0_reset_n  ;
    var logic            rgmii0_mdc      ;
    tri logic            rgmii0_mdio     ;
    var logic            rgmii0_gtx_clk  ;
    var logic            rgmii0_tx_ctrl  ;
    var logic    [3:0]   rgmii0_tx_d     ;
    var logic            rgmii0_rx_clk   ;
    var logic            rgmii0_rx_ctrl  ;
    var logic    [3:0]   rgmii0_rx_d     ;
    var logic    [2:0]   rgmii0_led      ;
    var logic            rgmii1_reset_n  ;
    var logic            rgmii1_mdc      ;
    tri logic            rgmii1_mdio     ;
    var logic            rgmii1_gtx_clk  ;
    var logic            rgmii1_tx_ctrl  ;
    var logic    [3:0]   rgmii1_tx_d     ;
    var logic            rgmii1_rx_clk   ;
    var logic            rgmii1_rx_ctrl  ;
    var logic    [3:0]   rgmii1_rx_d     ;
    var logic    [2:0]   rgmii1_led      ;

    assign in_clk25a = clk25;
    assign in_clk25b = clk25;

    eval_ether_tx_test_kr260
            #( 
                .DEVICE     (DEVICE     ),
                .SIMULATION (SIMULATION ),
                .DEBUG      (DEBUG      )
            )
        u_top
            (
                .*
            );
    
    // Zynq のスタブの中にクロックとバスアクセスを接続
    always_comb force u_top.u_design_1.reset  = reset;
    always_comb force u_top.u_design_1.clk125 = clk125;
    always_comb force u_top.u_design_1.clk580 = clk580;

    // loopback
    /*
    assign #2 rgmii0_rx_clk  = rgmii1_gtx_clk;
    assign rgmii0_rx_ctrl = rgmii1_tx_ctrl;
    assign rgmii0_rx_d    = rgmii1_tx_d   ;

    assign #2 rgmii1_rx_clk  = rgmii0_gtx_clk;
    assign rgmii1_rx_ctrl = rgmii0_tx_ctrl;
    assign rgmii1_rx_d    = rgmii0_tx_d   ;
    */

    
    // 遅延挿入
    assign #2 rgmii0_rx_clk = ether0_clk;
    logic       rgmii0_tx_clk;
    assign #2 rgmii0_tx_clk = rgmii0_gtx_clk;

    logic   [7:0]   ether0_data;
    logic           ether0_valid;
    rgmii_if
            #(
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_rgmii_if_0
            (
                .tx_reset       (reset          ),
                .tx_clk         (ether0_clk     ),
                .s_tx_error     (ether0_valid   ),
                .s_tx_data      (ether0_data    ),
                .s_tx_valid     (ether0_valid   ),

                .rx_reset       (reset          ),
                .rx_clk         (rgmii0_tx_clk  ),
                .m_rx_error     (),
                .m_rx_last      (),
                .m_rx_data      (),
                .m_rx_valid     (),

                .rgmii_tx_ctrl  (rgmii0_rx_ctrl ),
                .rgmii_tx_d     (rgmii0_rx_d    ),
                .rgmii_rx_ctrl  (rgmii0_tx_ctrl ),
                .rgmii_rx_d     (rgmii0_tx_d    )
            );

    logic   [31:0]   ether0_cycle;
    always_ff @(posedge ether0_clk) begin
        if ( reset ) begin
            ether0_cycle <= 0;
        end
        else begin
            ether0_cycle <= ether0_cycle + 1;

            if ( ether0_cycle > 10000 ) begin
                $finish;
            end
        end
    end

    assign ether0_data  = ether0_cycle[7:0];
    assign ether0_valid = (ether0_cycle[10:0] >= 10);

    // 遅延挿入
    assign #2 rgmii1_rx_clk = ether1_clk;

    // loopback
    assign rgmii1_rx_ctrl = rgmii1_tx_ctrl  ;
    assign rgmii1_rx_d    = rgmii1_tx_d     ;
    

endmodule


`default_nettype wire


// end of file
