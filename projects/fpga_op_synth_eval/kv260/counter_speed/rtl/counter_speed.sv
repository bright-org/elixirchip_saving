


`timescale 1ns / 1ps
`default_nettype none

`ifndef WIDTH
`define WIDTH 128
`endif

(* use_dsp = "no" *)
module counter_speed
        #(
            parameter   int     BITS   = `WIDTH
        )
        (
            input   var logic               reset,
            input   var logic               clk,
            input   var logic               cke,

            output  var logic   [0:0]       c
        );

    (* DONT_TOUCH = "yes" *)    logic   [BITS-1:0]  reg_c;

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            reg_c <= 0;
        end
        else if ( cke ) begin
            reg_c <= reg_c + 1;
        end
    end

    assign c = ^reg_c;

endmodule


`default_nettype wire
