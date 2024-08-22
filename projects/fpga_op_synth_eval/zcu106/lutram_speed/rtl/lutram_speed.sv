


`timescale 1ns / 1ps
`default_nettype none

module lutram_speed
        (
            input   var logic           reset,
            input   var logic           clk,
            input   var logic           cke,

            input   var logic   [8:0]   adr,
            input   var logic   [0:0]   we,
            input   var logic   [0:0]   din,
            output  var logic   [0:0]   dout
        );

    logic   [8:0]   reg_addr;
    logic   [0:0]   reg_we;
    logic   [0:0]   reg_din;
    logic   [0:0]   o;

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            reg_addr <= '0;
            reg_we <='0;
            reg_din <= '0;
            dout    <= '0;
        end
        else if ( cke ) begin
            reg_addr <= adr;
            reg_we <= we;
            reg_din <= din;
            dout    <= o;
        end
    end


    RAM512X1S
            #(
                .INIT               (512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
                .IS_WCLK_INVERTED   (1'b0) // Specifies active high/low WCLK
            )
        RAM512X1S_inst
            (
                .O      (o          ),     // Read/write port 1-bit output
                .A      (reg_addr   ), // Read/write port 9-bit address input
                .WE     (reg_we     ),   // Write enable input
                .WCLK   (clk        ),      // Write clock input
                .D      (reg_din    ) // RAM data input
        );

endmodule


`default_nettype wire
