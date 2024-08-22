


`timescale 1ns / 1ps
`default_nettype none

`ifndef DATA_WIDTH
`define DATA_WIDTH  32
`endif


// 比較
(* use_dsp = "no" *)
module cmp_speed
        #(
            parameter   int     DATA_BITS = `DATA_WIDTH                     ,
            parameter   type    data_t    = logic [DATA_BITS-1:0]    
        )
        (
            input   var logic           reset,
            input   var logic           clk,
            input   var logic           cke,

            input   var data_t          a,
            input   var data_t          b,
            output  var logic           c
        );

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            c <= 0;
        end
        else if ( cke ) begin
            c <= (a > b);
        end
    end

endmodule


`default_nettype wire
