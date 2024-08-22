
// 例によって jelly3_flipflops から派生


`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_xilinx_flipflops
        #(
            parameter   bit     BYPASS            = 1'b0                    ,
            parameter   int     DATA_BITS         = 1                       ,
            parameter   type    data_t            = logic [DATA_BITS-1:0]   ,
            parameter   data_t  RESET_VALUE       = 'x                      ,
            parameter           DEVICE            = "RTL"                   ,
            parameter           SIMULATION        = "false"                 ,
            parameter           DEBUG             = "false"                 
        )
        (
            input   var logic   reset       ,
            input   var logic   clk         ,
            input   var logic   cke         ,
            
            input   var data_t  din         ,
            output  var data_t  dout        
        );
    
    if ( BYPASS ) begin : bypass
        assign dout = din;
    end
    else begin : flipflops
        // Xilinx
        if ( string'(DEVICE) == "SPARTAN6"
                || string'(DEVICE) == "VIRTEX6"
                || string'(DEVICE) == "7SERIES"
                || string'(DEVICE) == "ULTRASCALE"
                || string'(DEVICE) == "ULTRASCALE_PLUS"
                || string'(DEVICE) == "ULTRASCALE_PLUS_ES1"
                || string'(DEVICE) == "ULTRASCALE_PLUS_ES2") begin : xilinx

            for ( genvar i = 0; i < DATA_BITS; i++ ) begin : loop
                if ( RESET_VALUE[i] == 1'b1 ) begin : fdse
                    FDSE
                            #(
                                .INIT               (RESET_VALUE[i]     ),
                                .IS_C_INVERTED      (1'b0               ),
                                .IS_D_INVERTED      (1'b0               ),
                                .IS_S_INVERTED      (1'b0               )
                            )
                        u_FDPE
                            (
                                .Q                  (dout[i]            ), 
                                .C                  (clk                ), 
                                .CE                 (cke                ),
                                .D                  (din[i]             ), 
                                .S                  (reset              )
                            );
                end
                else begin : fdre
                    FDRE
                            #(
                                .INIT               (RESET_VALUE[i]     ),
                                .IS_C_INVERTED      (1'b0               ),
                                .IS_D_INVERTED      (1'b0               ),
                                .IS_R_INVERTED      (1'b0               )
                            )
                        u_FDRE
                            (
                                .Q                  (dout[i]            ), 
                                .C                  (clk                ), 
                                .CE                 (cke                ),
                                .D                  (din[i]             ), 
                                .R                  (reset              )
                            );
                end
            end
        end
        else begin : rtl
            // RTL
            data_t  rtl_dout = RESET_VALUE;
            always_ff @( posedge clk ) begin
                if ( reset ) begin
                    rtl_dout <= RESET_VALUE;
                end
                else if ( cke ) begin
                    rtl_dout <= din;
                end
            end
            assign dout = rtl_dout;
        end

        // debug
        if ( string'(DEBUG) == "true" ) begin : debug
            (* MARK_DEBUG = "true" *)   data_t   dbg_dout;
            assign dbg_dout = dout;
        end
    end

endmodule


`default_nettype wire


// end of file
