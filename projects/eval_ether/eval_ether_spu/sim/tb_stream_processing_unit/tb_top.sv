

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

    localparam RATE = 1000.0/580.00;

    logic       reset = 1;
    initial #100 reset = 0;

    logic       clk = 1'b1;
    always #(RATE/2.0) clk <= ~clk;


    // ---------------------------------
    //  main
    // ---------------------------------

`ifdef __VERILATOR__
    localparam  DEVICE     = "RTL"              ;   // デバイス名
`else
    localparam  DEVICE     = "ULTRASCALE_PLUS"  ;   // デバイス名
`endif 
    localparam  SIMULATION = "true"             ;   // シミュレーション
    localparam  DEBUG      = "false"            ;   // デバッグ

    tb_main
            #(
                .DEVICE     ("ULTRASCALE_PLUS"  ),
                .SIMULATION ("true"             ),
                .DEBUG      ("false"            )
            )
        u_tb_main
            (
                .reset      ,
                .clk        
            );
    
endmodule


`default_nettype wire


// end of file
