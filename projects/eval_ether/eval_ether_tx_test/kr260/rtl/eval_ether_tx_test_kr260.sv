
`timescale 1ns / 1ps
`default_nettype none


// ボード依存のトップネット(KR260用)
module eval_ether_tx_test_kr260
        #(
            parameter   MODE       = "test_pattern"     ,
            parameter   DEVICE     = "ULTRASCALE_PLUS"  ,   // デバイス名
            parameter   SIMULATION = "false"            ,   // シミュレーション
            parameter   DEBUG      = "true"                 // デバッグ
        )
        (
            output  var logic           fan_en         ,

            // clock
            input  var logic            in_clk25a       ,
            input  var logic            in_clk25b       ,

            // LED
            output var logic    [1:0]   led             ,

            // Ether0
            output var logic            rgmii0_reset_n  ,
            output var logic            rgmii0_mdc      ,
            inout  tri logic            rgmii0_mdio     ,
            output var logic            rgmii0_gtx_clk  ,
            output var logic            rgmii0_tx_ctrl  ,
            output var logic    [3:0]   rgmii0_tx_d     ,
            input  var logic            rgmii0_rx_clk   ,
            input  var logic            rgmii0_rx_ctrl  ,
            input  var logic    [3:0]   rgmii0_rx_d     ,
            input  var logic    [2:0]   rgmii0_led      ,

            // Ether1
            output var logic            rgmii1_reset_n  ,
            output var logic            rgmii1_mdc      ,
            inout  tri logic            rgmii1_mdio     ,
            output var logic            rgmii1_gtx_clk  ,
            output var logic            rgmii1_tx_ctrl  ,
            output var logic    [3:0]   rgmii1_tx_d     ,
            input  var logic            rgmii1_rx_clk   ,
            input  var logic            rgmii1_rx_ctrl  ,
            input  var logic    [3:0]   rgmii1_rx_d     ,
            input  var logic    [2:0]   rgmii1_led      
        );

    // リセット
    var logic           in_reset;
    var logic   [7:0]   reset_counter = '1;
    always_ff @(posedge in_clk25a ) begin
        if ( reset_counter > 0 ) begin
            reset_counter <= reset_counter - 1'b1;
            in_reset      <= 1'b1;
        end
        else begin
            in_reset      <= 1'b0;
        end
    end


    // ZynqMP PS
    logic   in_clk25        ;
    BUFG
        u_bufg
            (
                .I      (in_clk25b  ),
                .O      (in_clk25   )
            );

    logic   ether_reset     ;
    logic   ether_clk       ;

//    logic   core_reset      ;
//    logic   core_clk        ;

    logic   ref_reset       ;
    logic   ref_clk         ;

    design_1
        u_design_1
            (
                .fan_en         ,

                .in_reset       (in_reset   ),
                .in_clk25       (in_clk25   ),

                .ether_reset    (ether_reset),
                .ether_clk      (ether_clk  )

//              .core_reset     (core_reset ),
//              .core_clk       (core_clk   )

//                .ref_reset      (ref_reset  ),
//                .ref_clk        (ref_clk    )
            );


    // ------------------------------
    //  Ether
    // ------------------------------

    // ether0
    logic   rgmii0_tx_reset ;
    logic   rgmii0_tx_clk   ;
    
    logic   rgmii0_rx_reset ;
    jelly_reset u_reset_ether0_rx
        (
            .clk        (rgmii0_rx_clk  ),
            .in_reset   (in_reset       ),
            .out_reset  (rgmii0_rx_reset)
        );
    
    logic           ether0_tx_error;
    logic           ether0_tx_last;
    logic   [7:0]   ether0_tx_data;
    logic           ether0_tx_valid;

    logic           ether0_rx_error;
    logic           ether0_rx_last;
    logic   [7:0]   ether0_rx_data;
    logic           ether0_rx_valid;

    rgmii_if
            #(
                .DEVICE             (DEVICE         ),
                .SIMULATION         (SIMULATION     ),
                .DEBUG              (DEBUG          )
            )
        u_rgmii_if_0
            (
                .tx_reset           (rgmii0_tx_reset    ),
                .tx_clk             (rgmii0_tx_clk      ),
                .s_tx_error         (ether0_tx_valid ? ether0_tx_error : '0),
                .s_tx_data          (ether0_tx_valid ? ether0_tx_data  : '0),
                .s_tx_valid         (ether0_tx_valid),

                .rx_reset           (rgmii0_rx_reset),
                .rx_clk             (rgmii0_rx_clk  ),
                .m_rx_error         (ether0_rx_error),
                .m_rx_last          (ether0_rx_last ),
                .m_rx_data          (ether0_rx_data ),
                .m_rx_valid         (ether0_rx_valid),

                .rgmii_tx_ctrl      (rgmii0_tx_ctrl ),
                .rgmii_tx_d         (rgmii0_tx_d    ),
                .rgmii_rx_ctrl      (rgmii0_rx_ctrl ),
                .rgmii_rx_d         (rgmii0_rx_d    )
            );

    assign rgmii0_mdc     = 1'b0;
    assign rgmii0_mdio    = 1'bz;
    assign rgmii0_reset_n = ~ether_reset;
//  assign rgmii0_gtx_clk = ether_clk;
    ODDRE1
            #(
                .IS_C_INVERTED  (1'b0           ),
                .IS_D1_INVERTED (1'b0           ),
                .IS_D2_INVERTED (1'b0           ),
                .SIM_DEVICE     (DEVICE         ),
                .SRVAL          (1'b0           )
            )
        u_oddre1_tx_rgmii0_gtx_clk
            (
                .Q              (rgmii0_gtx_clk ),
                .C              (rgmii0_tx_clk  ),
                .D1             (1'b1           ),
                .D2             (1'b0           ),
                .SR             (1'b0           )
            );


    // ether 1
    logic   rgmii1_tx_reset ;
    logic   rgmii1_tx_clk   ;

    logic   rgmii1_rx_reset ;
    jelly_reset u_reset_ether1_rx
        (
            .clk        (rgmii1_rx_clk  ),
            .in_reset   (in_reset       ),
            .out_reset  (rgmii1_rx_reset)
        );

    logic           ether1_tx_error;
    logic           ether1_tx_last;
    logic   [7:0]   ether1_tx_data;
    logic           ether1_tx_valid;

    logic           ether1_rx_error;
    logic           ether1_rx_last;
    logic   [7:0]   ether1_rx_data;
    logic           ether1_rx_valid;

    rgmii_if
            #(
                .DEVICE             (DEVICE         ),
                .SIMULATION         (SIMULATION     ),
                .DEBUG              (DEBUG          )
            )
        u_rgmii_if_1
            (
                .tx_reset           (rgmii1_tx_reset),
                .tx_clk             (rgmii1_tx_clk  ),
                .s_tx_error         (ether1_tx_valid ? ether1_tx_error : '0),
                .s_tx_data          (ether1_tx_valid ? ether1_tx_data  : '0),
                .s_tx_valid         (ether1_tx_valid),

                .rx_reset           (rgmii1_rx_reset),
                .rx_clk             (rgmii1_rx_clk  ),
                .m_rx_error         (ether1_rx_error),
                .m_rx_last          (ether1_rx_last ),
                .m_rx_data          (ether1_rx_data ),
                .m_rx_valid         (ether1_rx_valid),

                .rgmii_tx_ctrl      (rgmii1_tx_ctrl ),
                .rgmii_tx_d         (rgmii1_tx_d    ),
                .rgmii_rx_ctrl      (rgmii1_rx_ctrl ),
                .rgmii_rx_d         (rgmii1_rx_d    )
            );

    assign rgmii1_mdc     = 1'b0;
    assign rgmii1_mdio    = 1'bz;
    assign rgmii1_reset_n = ~ether_reset;
//  assign rgmii1_gtx_clk = ether_clk;
    ODDRE1
            #(
                .IS_C_INVERTED  (1'b0           ),
                .IS_D1_INVERTED (1'b0           ),
                .IS_D2_INVERTED (1'b0           ),
                .SIM_DEVICE     (DEVICE         ),
                .SRVAL          (1'b0           )
            )
        u_oddre1_tx_rgmii1_gtx_clk
            (
                .Q              (rgmii1_gtx_clk ),
                .C              (rgmii1_tx_clk  ),
                .D1             (1'b1           ),
                .D2             (1'b0           ),
                .SR             (1'b0           )
            );


    // ------------------------------
    //  Test pattern
    // ------------------------------

    if ( MODE == "test_pattern" ) begin : sim
        logic   [9:0]   ether0_cycle;
        always_ff @(posedge ether_clk) begin
            if ( ether_reset ) begin
                ether0_cycle <= 0;
            end
            else begin
                ether0_cycle <= ether0_cycle + 1;
            end
        end

        assign rgmii0_tx_reset = ether_reset;
        assign rgmii0_tx_clk   = ether_clk;

        assign ether0_tx_error = ether0_tx_valid;
        assign ether0_tx_last  = ether0_cycle[7:0] == '1;
        assign ether0_tx_data  = ether0_cycle[7:0] <  7 ? 8'h55 :
                                 ether0_cycle[7:0] == 7 ? 8'hd5 :
                                 ether0_cycle[7:0];
        assign ether0_tx_valid = ether0_cycle[8];
    
        assign rgmii1_tx_reset = ether_reset;
        assign rgmii1_tx_clk   = ether_clk;
        assign ether1_tx_error = ether0_tx_valid;
        assign ether1_tx_last  = ether0_tx_last;
        assign ether1_tx_data  = ether0_tx_data;
        assign ether1_tx_valid = ether0_tx_valid;
    end
    else begin : bridge
        // bridge
//        assign rgmii1_tx_reset = ether_reset;
//        assign rgmii1_tx_clk   = ether_clk;
        assign rgmii1_tx_reset = rgmii0_rx_reset;
        assign rgmii1_tx_clk   = rgmii0_rx_clk;
        assign ether1_tx_error = ether0_rx_error;
        assign ether1_tx_last  = ether0_rx_last;
        assign ether1_tx_data  = ether0_rx_data;
        assign ether1_tx_valid = ether0_rx_valid;

//        assign rgmii0_tx_reset = ether_reset;
//        assign rgmii0_tx_clk   = ether_clk;
        assign rgmii0_tx_reset = rgmii1_rx_reset;
        assign rgmii0_tx_clk   = rgmii1_rx_clk;
        assign ether0_tx_error = ether1_rx_error;
        assign ether0_tx_last  = ether1_rx_last;
        assign ether0_tx_data  = ether1_rx_data;
        assign ether0_tx_valid = ether1_rx_valid;
    end


    // ------------------------------
    //  LED
    // ------------------------------

    logic [24:0] ether_clk_counter;
    always_ff @( posedge ether_clk ) begin
        if ( ether_reset ) begin
            ether_clk_counter <= '0;
        end
        else begin
            ether_clk_counter <= ether_clk_counter + 1'b1;
        end
    end
    /*
    logic [24:0] core_clk_counter;
    always_ff @( posedge core_clk ) begin
        if ( core_reset ) begin
            core_clk_counter <= '0;
        end
        else begin
          core_clk_counter <= core_clk_counter + 1'b1;
        end
    end
    */

    logic [24:0] ether0_rx_clk_counter = '0;
    always_ff @( posedge rgmii0_rx_clk ) begin
        ether0_rx_clk_counter <= ether0_rx_clk_counter + 1'b1 + ether0_rx_data + ether0_rx_valid;
    end

    logic [24:0] ether1_rx_clk_counter = '0;
    always_ff @( posedge rgmii1_rx_clk ) begin
        ether1_rx_clk_counter <= ether1_rx_clk_counter + 1'b1 + ether1_rx_data + ether1_rx_valid;
    end

    
    logic [24:0] clk_counter = '0;
    always_ff @( posedge in_clk25 ) begin
        clk_counter <= clk_counter + 1'b1;
    end

//    assign led[0] = core_clk_counter[24]; //ether0_rx_clk_counter[23]; //ether_clk_counter[23];
//    assign led[1] = core_reset;      //core_clk_counter[23];

    assign led[0] = ether0_rx_clk_counter[24];
    assign led[1] = ether1_rx_clk_counter[24];

endmodule


`default_nettype wire

