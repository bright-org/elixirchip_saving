


`timescale 1ns / 1ps
`default_nettype none

`ifndef SEL_WIDTH
`define SEL_WIDTH   10
`endif

module mux_speed
        #(
            parameter   int     SEL_BITS = `SEL_WIDTH,
            parameter   int     IN_BITS  = 1 << SEL_BITS
        )
        (
            input   var logic                   reset,
            input   var logic                   clk,
            input   var logic                   cke,

            input   var logic   [0:0]           sel,
            input   var logic   [0:0]           din,
            output  var logic   [0:0]           dout
        );

    // シフトレジスタを作ってI/O数を減らす
    (* DONT_TOUCH = "yes" *)    logic   [SEL_BITS-1:0]  s_sel;
    (* DONT_TOUCH = "yes" *)    logic   [IN_BITS-1:0]   s_din;
    always_ff @( posedge clk ) begin
        s_sel <= SEL_BITS'({s_sel, sel});
        s_din <=  IN_BITS'({s_din, din});
    end

    (* DONT_TOUCH = "yes" *)    logic   [SEL_BITS-1:0]  reg_sel;
    (* DONT_TOUCH = "yes" *)    logic   [IN_BITS-1:0]   reg_din;
    
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            reg_sel <= 0;
            reg_din <= 0;
            dout    <= 0;
        end
        else if ( cke ) begin
            reg_sel <= s_sel;
            reg_din <= s_din;
            dout    <= reg_din[reg_sel];
        end
    end

endmodule


`default_nettype wire
