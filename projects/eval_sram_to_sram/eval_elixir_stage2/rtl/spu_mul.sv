
`timescale 1ns / 1ps
`default_nettype none


(* use_dsp = "no" *)
module spu_mul
        #(
            parameter   int     LATENCY      = 3                                ,
            parameter   int     S_DATA0_BITS = 8                                ,
            parameter   type    s_data0_t    = logic signed [S_DATA0_BITS-1:0]  ,
            parameter   int     S_DATA1_BITS = 8                                ,
            parameter   type    s_data1_t    = logic signed [S_DATA1_BITS-1:0]  ,
            parameter   int     M_DATA_BITS  = 8                                ,
            parameter   type    m_data_t     = logic signed [M_DATA_BITS-1:0]   ,
            parameter   int     DATA_SHIFT   = 0                                
        )
        (
            input   var logic       reset           ,
            input   var logic       clk             ,
            input   var logic       cke             ,

            input   var s_data0_t   s_data0         ,
            input   var s_data1_t   s_data1         ,
            input   var logic       s_valid         ,

            output  var m_data_t    m_data          ,
            output  var logic       m_valid         
        );

    localparam  int     MUL_BITS = $bits(s_data0_t) + $bits(s_data1_t);
    localparam  type    mut_t    = logic signed [MUL_BITS-1:0];


    m_data_t    mul_data;

    if ( LATENCY >= 3 && $bits(s_data0_t) == 8 && $bits(s_data1_t) == 8 && $bits(m_data_t) == 8 && DATA_SHIFT == 0) begin
        // IP core
        mul_s8s8_lo8_p3
            u_mul_s8s8_lo8_p3
                (
                    .CLK    (clk     ),
                    .CE     (cke     ),
                    .A      (s_data0 ),
                    .B      (s_data1 ),
                    .P      (mul_data)
                );
    end
    else begin
        s_data0_t   st0_data0;
        s_data1_t   st0_data1;
        mut_t       st1_data;
        m_data_t    st2_data;

        always_ff @( posedge clk ) begin
            if ( cke ) begin
                // stage0
                st0_data0 <= s_data0;
                st0_data1 <= s_data1;

                // stage1
                st1_data <= st0_data0 * st0_data1;

                // stage2
                st2_data <= m_data_t'(st1_data >>> DATA_SHIFT);
            end
        end
        assign mul_data = st2_data;
    end

    spu_data
            #(
                .LATENCY    (LATENCY - 3        ),
                .DATA_BITS  ($bits(m_data_t)    )
            )
        u_spu_data
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (mul_data           ),

                .m_data     (m_data             )
            );


endmodule


`default_nettype wire

