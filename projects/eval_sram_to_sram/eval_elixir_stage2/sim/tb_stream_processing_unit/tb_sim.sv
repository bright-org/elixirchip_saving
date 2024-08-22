

`timescale 1ns / 1ps
`default_nettype none


module tb_sim();
    
    initial begin
        $dumpfile("tb_sim.vcd");
        $dumpvars(0, tb_sim);
        
    #1000000
        $display("timeout");
        $finish;
    end
    
    
    // ---------------------------------
    //  clock & reset
    // ---------------------------------

    localparam RATE = 1000.0/500.00;

    logic       reset = 1;
    initial #100 reset = 0;

    logic       clk = 1'b1;
    always #(RATE/2.0) clk <= ~clk;


    
    // ---------------------------------
    //  Main
    // ---------------------------------

    tb_main
        u_tb_main
            (
                .reset  ,
                .clk
            );
   
    
endmodule


`default_nettype wire


// end of file
