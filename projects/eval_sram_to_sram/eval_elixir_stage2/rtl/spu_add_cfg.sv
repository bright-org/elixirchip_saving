


`timescale 1ns / 1ps
`default_nettype none

module spu_add_cfg
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

    if ( DATA_BITS == 8 ) begin : carry8
        // CARRY8
        logic                          carry8_ci;
        logic [DATA_BITS-1:0]          carry8_s;
        logic [DATA_BITS-1:0]          carry8_di;
        logic [DATA_BITS-1:0]          carry8_o;
        logic [DATA_BITS-1:0]          carry8_co;

        CARRY8
                #(
                    .CARRY_TYPE ("SINGLE_CY8") 
                )
            u_carry8
                (
                    .CO         (carry8_co  ),
                    .O          (carry8_o   ),
                    .CI         (carry8_ci  ),
                    .CI_TOP     (1'b0       ),
                    .DI         (carry8_di  ),
                    .S          (carry8_s   )
                );

        // operation
        data_t     p;
        always_comb begin
            case ( cfg[2:0] )
            3'h0: p = s_data0 ^  s_data1;       // s_data0 + s_data1
            3'h1: p = s_data0 ^ ~s_data1;       // s_data0 - s_data1
            3'h2: p = s_data0 ^ '1;             // s_data0 - 1
            3'h2: p = s_data0 ^  0;             // s_data0 + 1
            3'h3: p = s_data0 ^  s_data0;       // s_data0 + s_data0
            3'h4: p = s_data0 ^ ~s_data0;       // s_data0 - s_data0
            3'h0: p = s_data0 ^  (2*s_data1);   // s_data0 + 2*s_data1
            3'h1: p = s_data0 ^ ~(2*s_data1);   // s_data0 - 2*s_data1
            default: p = '0;
            endcase
        end

        assign carry8_di = s_data0;
        assign carry8_s  = p;
        assign carry8_ci = cfg[3];

        assign st0_data = carry8_o;
    end
    else begin : rtl
        data_t     p;
        always_comb begin
            case ( cfg[2:0] )
            3'h0: p = s_data0 + s_data1;
            3'h1: p = s_data0 - s_data1;
            3'h2: p = s_data0 - 1;
            3'h2: p = s_data0 + 1;
            3'h3: p = s_data0 + s_data0;
            3'h4: p = s_data0 - s_data0;
            3'h0: p = s_data0 + 2*s_data1;
            3'h1: p = s_data0 - 2*s_data1;
            default: p = '0;
            endcase

            p += cfg[3];
        end

        assign st0_data = p;
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
