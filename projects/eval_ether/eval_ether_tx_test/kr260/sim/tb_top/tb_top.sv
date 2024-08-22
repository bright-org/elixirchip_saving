

`timescale 1ns / 1ps
`default_nettype none


module tb_top();
    
    initial begin
        $dumpfile("tb_top.vcd");
        $dumpvars(0, tb_top);
        
    #1000000
        $display("timeout");
        $finish;
    end
    
    
    // ---------------------------------
    //  clock & reset
    // ---------------------------------

    localparam RATE25  = 1000.0/ 25.00;
    localparam RATE125 = 1000.0/125.00;
    localparam RATE580 = 1000.0/580.00;
    localparam RATE_E0 = 1000.0/125.00 + 0.001;
    localparam RATE_E1 = 1000.0/125.00 - 0.001;

    logic       reset = 1;
    initial #100 reset = 0;

    logic       clk25 = 1'b1;
    always #(RATE25/2.0) clk25 <= ~clk25;

    logic       clk125 = 1'b1;
    always #(RATE125/2.0) clk125 <= ~clk125;

    logic       clk580 = 1'b1;
    always #(RATE580/2.0) clk580 <= ~clk580;

    logic       ether0_clk = 1'b1;
    always #(RATE_E0/2.0) ether0_clk <= ~ether0_clk;

    logic       ether1_clk = 1'b1;
    always #(RATE_E1/2.0) ether1_clk <= ~ether1_clk;


    // ---------------------------------
    //  main
    // ---------------------------------

    tb_main
            #(
                .DEVICE     ("ULTRASCALE_PLUS"  ),
                .SIMULATION ("true"             ),
                .DEBUG      ("false"            )
            )
        u_tb_main
            (
                .reset      ,
                .clk25      ,
                .clk125     ,
                .clk580     ,
                .ether0_clk ,
                .ether1_clk
            );
    
endmodule


`default_nettype wire


// end of file
