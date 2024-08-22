


`timescale 1ns / 1ps
`default_nettype none

`ifndef LATENCY
`define LATENCY 18
`endif

`ifndef A_WIDTH
`define A_WIDTH 64
`endif

`ifndef B_WIDTH
`define B_WIDTH 64
`endif

`ifndef P_WIDTH
`define P_WIDTH 128
`endif

`ifndef A_SIGN
`define A_SIGN  signed
`endif
`ifndef B_SIGN
`define B_SIGN  signed
`endif

`ifndef P_SIGN
`define P_SIGN  signed
`endif

`ifndef SHIFT
`define SHIFT   0
`endif


// 乗算テスト
(* use_dsp = "yes" *)
module dsp_mul_speed
        #(
            parameter   int     LATENCY = `LATENCY                  ,
            parameter   int     A_BITS  = `A_WIDTH                  ,
            parameter   type    a_t     = logic `B_SIGN [A_BITS-1:0],
            parameter   int     B_BITS  = `B_WIDTH                  ,
            parameter   type    b_t     = logic `B_SIGN [B_BITS-1:0],
            parameter   int     M_BITS  = A_BITS + B_BITS           ,
            parameter   type    m_t     = logic `P_SIGN [M_BITS-1:0],
            parameter   int     P_BITS  = `P_WIDTH                  ,
            parameter   type    p_t     = logic `P_SIGN [P_BITS-1:0],
            parameter   int     SHIFT   = `SHIFT                    
        )
        (
            input   var logic           reset   ,
            input   var logic           clk     ,
            input   var logic           cke     ,

            input   var logic   [7:0]   a       ,
            input   var logic   [7:0]   b       ,
            output  var logic   [0:0]   p
        );


    // 乗算前後のリタイミングを禁止(FF間の演算に制約する)
    (* DONT_TOUCH = "yes" *)    a_t     in_a;
    (* DONT_TOUCH = "yes" *)    b_t     in_b;
    (* DONT_TOUCH = "yes" *)    p_t     out_p;

    // DSP
    a_t                 dsp_a   ;
    b_t                 dsp_b   ;
    m_t                 dsp_m   ;
    m_t [LATENCY-1:2]   dsp_p   ;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            dsp_a <= '0;
            dsp_b <= '0;
            dsp_m <= '0;
            dsp_p <= '0;
        end
        else if ( cke ) begin
            // stage 0
            dsp_a <= in_a;
            dsp_b <= in_b;

            // stage 1
            dsp_m <= dsp_a * dsp_b;

            // stage 2
            dsp_p[2] <= dsp_m;

            // additional stage
            for ( int i = 3; i < LATENCY; i++ ) begin
                dsp_p[i] <= dsp_p[i-1];
            end
        end
    end


    // I/O
   always_ff @( posedge clk ) begin
        if ( reset ) begin
            in_a  <= '0;
            in_b  <= '0;
            out_p <= '0;
        end
        else if ( cke ) begin
            in_a  <= a_t'({in_a, a});
            in_b  <= b_t'({in_b, b});
            out_p <= p_t'(dsp_p[LATENCY-1] >> SHIFT);
        end
    end
    assign p = ^out_p;

endmodule


`default_nettype wire
