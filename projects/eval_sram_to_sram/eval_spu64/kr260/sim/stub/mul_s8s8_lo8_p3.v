
`timescale 1ns / 1ps
`default_nettype none

// シミュレーション用のスタブ
module mul_s8s8_lo8_p3
        (
            input   wire                    CLK ,
            input   wire                    CE  ,
            input   wire    signed  [7:0]   A   ,
            input   wire    signed  [7:0]   B   ,
            output  wire    signed  [7:0]   P   
        );

    reg     [7:0]   st0_p;
    reg     [7:0]   st1_p;
    reg     [7:0]   st2_p;
    always @(posedge CLK) begin
        if ( CE ) begin
            st0_p <= A * B;
            st1_p <= st0_p;
            st2_p <= st1_p;
        end
    end

    assign  P = st2_p;

endmodule

`default_nettype wire
