
`timescale 1ns / 1ps
`default_nettype none


module sram_to_sram_write
        #(
            parameter int  ADDR_BITS = 10,
            parameter type addr_t    = logic [ADDR_BITS-1:0],
            parameter int  DATA_BITS = 8,
            parameter type data_t    = logic signed [DATA_BITS-1:0],
            parameter int  UNIT_LEN  = 64
        )
        (
            input   var logic                           reset           ,
            input   var logic                           clk             ,
            input   var logic                           cke             ,

            output  var logic                           done            ,

            output  var logic                           mem2_wen        ,
            output  var addr_t                          mem2_waddr      ,
            output  var data_t  [UNIT_LEN-1:0]          mem2_wdata      ,

            input   var data_t  [UNIT_LEN-1:0]          s_data          ,
            input   var logic                           s_valid         
        );

                                addr_t                  st0_addr    ;
    (* DONT_TOUCH = "yes" *)    data_t  [UNIT_LEN-1:0]  st0_data    ;
                                logic                   st0_valid   ;

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_addr    <= '0;
            st0_data    <= 'x;
            st0_valid   <= 1'b0;
            done        <= 1'b0;
        end
        else if ( cke ) begin
            // stage 0 (generate memory address)
            if ( st0_valid ) begin
                st0_addr  <= st0_addr + 1;
            end
            st0_data  <= s_data;
            st0_valid <= s_valid;

            // done
            done <= st0_valid & ~s_valid;
        end
    end

    assign mem2_wen   = st0_valid;
    assign mem2_waddr = st0_addr;
    assign mem2_wdata = st0_data;

endmodule

`default_nettype wire

