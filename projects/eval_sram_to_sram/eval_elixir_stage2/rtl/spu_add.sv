
`timescale 1ns / 1ps
`default_nettype none


module spu_add
        #(
            parameter int  LATENCY      = 1                                 ,
            parameter int  S_DATA0_BITS = 8                                 ,
            parameter type s_data0_t    = logic signed [S_DATA0_BITS-1:0]   ,
            parameter int  S_DATA1_BITS = 8                                 ,
            parameter type s_data1_t    = logic signed [S_DATA1_BITS-1:0]   ,
            parameter int  M_DATA_BITS  = 8                                 ,
            parameter type m_data_t     = logic signed [M_DATA_BITS-1:0]    
        )
        (
            input   var logic       reset       ,
            input   var logic       clk         ,
            input   var logic       cke         ,

            input   var s_data0_t   s_data0     ,
            input   var s_data1_t   s_data1     ,

            output  var m_data_t    m_data      
        );


    //  加算
    m_data_t    st0_data;
    assign st0_data = m_data_t'(s_data0) + m_data_t'(s_data1);

    // パイプライン遅延追加
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

                .s_data     (st0_data           ),

                .m_data     (m_data             )
            );

endmodule


`default_nettype wire

