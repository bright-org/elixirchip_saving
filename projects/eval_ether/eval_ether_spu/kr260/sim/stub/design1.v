`timescale 1 ps / 1 ps

module  design_1
            (
                output  wire    fan_en        ,
                input   wire    in_reset      ,
                input   wire    in_clk25      ,
                output  wire    ether_reset   ,
                output  wire    ether_clk     ,
                output  wire    core_reset    ,
                output  wire    core_clk      
            );

    // テストベンチから force する前提の信号
    reg             reset           /*verilator public_flat*/;
    reg             clk125          /*verilator public_flat*/;
    reg             clk580          /*verilator public_flat*/;

    assign ether_reset = reset;
    assign ether_clk   = clk125;
    assign core_reset  = reset;
    assign core_clk    = clk580;

endmodule
