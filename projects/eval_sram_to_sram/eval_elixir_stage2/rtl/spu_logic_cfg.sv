


`timescale 1ns / 1ps
`default_nettype none


module spu_logic_cfg
        #(
            parameter   int     LATENCY   = 1,
            parameter   int     DATA_BITS = 8,
            parameter   type    data_t    = logic [DATA_BITS-1:0]
        )
        (
            input   var logic           reset,
            input   var logic           clk,
            input   var logic           cke,

            input   var logic   [3:0]   cfg,

            input   var data_t          s_data0,
            input   var data_t          s_data1,

            output  var data_t          m_data
        );

    // stage0 
    data_t          st0_data;
    always_comb begin
        case ( cfg[3:0] )
        4'h0: st0_data =  s_data0 & s_data1;
        4'h1: st0_data =  s_data0 | s_data1;
        4'h2: st0_data =  s_data0 ^ s_data1;
        4'h3: st0_data =  s_data0;
        4'h4: st0_data =  s_data0 & ~s_data1;
        4'h5: st0_data =  s_data0 | ~s_data1;
        4'h6: st0_data =  s_data0 ^ ~s_data1;
        4'h7: st0_data =  s_data0;
        4'h8: st0_data =  ~s_data0 & s_data1;
        4'h9: st0_data =  ~s_data0 | s_data1;
        4'ha: st0_data =  ~s_data0 ^ s_data1;
        4'hb: st0_data =  ~s_data0;
        4'hc: st0_data =  ~s_data0 & ~s_data1;
        4'hd: st0_data =  ~s_data0 | ~s_data1;
        4'he: st0_data =  ~s_data0 ^ ~s_data1;
        4'hf: st0_data =  ~s_data0;
        endcase
    end

    spu_data
            #(
                .LATENCY    (LATENCY            ),
                .DATA_BITS  ($bits(data_t)      )
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
