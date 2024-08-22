
`timescale 1ns / 1ps
`default_nettype none


module spu_nop
        #(
            parameter int  LATENCY      = 1,
            parameter int  S_DATA_BITS  = 8,
            parameter type s_data_t     = logic signed [S_DATA_BITS-1:0],
            parameter int  M_DATA_BITS  = 8,
            parameter type m_data_t     = logic signed [M_DATA_BITS-1:0]
        )
        (
            input   var logic       reset       ,
            input   var logic       clk         ,
            input   var logic       cke         ,

            input   var s_data_t    s_data      ,

            output  var m_data_t    m_data      
        );


    spu_data
            #(
                .LATENCY    (LATENCY            ),
                .DATA_BITS  ($bits(m_data_t)    )
            )
        u_spu_data
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (m_data_t'(s_data)  ),

                .m_data     (m_data             )
            );

endmodule


`default_nettype wire

