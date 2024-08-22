


`timescale 1ns / 1ps
`default_nettype none

`ifndef SIGN
`define SIGN unsigned
`endif

`ifndef A_WIDTH
`define A_WIDTH 8
`endif

`ifndef B_WIDTH
`define B_WIDTH 8
`endif


// 乗算テスト
(* use_dsp = "no" *)
module mul_utilization
        #(
            parameter   int     A_BITS = `A_WIDTH,
            parameter   type    a_t    = logic signed [A_BITS-1:0],
            parameter   int     B_BITS = `B_WIDTH,
            parameter   type    b_t    = logic signed [B_BITS-1:0],
            parameter   int     C_BITS = A_BITS + B_BITS,
            parameter   type    c_t    = logic signed [C_BITS-1:0]
        )
        (
            input   var logic clk,

            input   var a_t   a,
            input   var b_t   b,
            output  var c_t   c
        );

`ifdef INS_FF
    always_ff @( posedge clk ) begin
        c <= a * b;
    end
`else
    assign c = a * b;
`endif 

endmodule


`default_nettype wire
