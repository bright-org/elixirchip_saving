


`timescale 1ns / 1ps
`default_nettype none

`ifndef SEL_WIDTH
`define SEL_WIDTH   1
`endif

module mux_utilization
        #(
            parameter   int     SEL_BITS = `SEL_WIDTH,
            parameter   int     IN_BITS  = 1 << SEL_BITS
        )
        (
            input   var logic                   reset,
            input   var logic                   clk,
            input   var logic                   cke,

            input   var logic   [SEL_BITS-1:0]  sel,
            input   var logic   [IN_BITS-1:0]   din,
            output  var logic   [0:0]           dout
        );

    
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            dout    <= 0;
        end
        else if ( cke ) begin
            dout <= din[sel];
        end
    end

endmodule


`default_nettype wire
