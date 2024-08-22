
`timescale 1ns / 1ps
`default_nettype none


module sram_to_sram_read
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

            input   var logic                           start           ,

            output  var logic                           mem0_ren        ,
            output  var addr_t                          mem0_raddr      ,
            input   var data_t  [UNIT_LEN-1:0]          mem0_rdata      ,

            output  var logic                           mem1_ren        ,
            output  var addr_t                          mem1_raddr      ,
            input   var data_t  [UNIT_LEN-1:0]          mem1_rdata      ,

            output  var addr_t                          m_addr          ,
            output  var data_t  [UNIT_LEN-1:0]          m_data0         ,
            output  var data_t  [UNIT_LEN-1:0]          m_data1         ,
            output  var logic                           m_valid         
        );


    addr_t                  st0_addr;
    logic                   st0_valid;

    addr_t                  st1_addr;
    logic                   st1_valid;

    addr_t                  st2_addr;
    logic                   st2_valid;

    addr_t                  st3_addr;
    logic                   st3_valid;

                                addr_t                  st4_addr;
    (* DONT_TOUCH = "yes" *)    data_t  [UNIT_LEN-1:0]  st4_data0;
    (* DONT_TOUCH = "yes" *)    data_t  [UNIT_LEN-1:0]  st4_data1;
                                logic                   st4_valid;

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_addr    <= 'x;
            st0_valid   <= 1'b0;
            st1_addr    <= 'x;
            st1_valid   <= 1'b0;
            st2_addr    <= 'x;
            st2_valid   <= 1'b0;
            st3_addr    <= 'x;
            st3_valid   <= 1'b0;
            st4_addr    <= 'x;
            st4_data0   <= 'x;
            st4_data1   <= 'x;
            st4_valid   <= 1'b0;
        end
        else if ( cke ) begin
            // stage 0 (generate memory address)
            if ( st0_valid ) begin
                st0_addr  <= st0_addr + 1;
                st0_valid <= (st0_addr != '1);
            end
            else begin
                st0_addr  <= '0;
                st0_valid <= start;
            end

            // stage 1 (memory command stage)
            st1_addr  <= st0_addr;
            st1_valid <= st0_valid;

            // stage 2 (memory read stage 1)
            st2_addr  <= st1_addr;
            st2_valid <= st1_valid;

            // stage 3 (memory read stage 2)
            st3_addr  <= st2_addr;
            st3_valid <= st2_valid;

            // stage 4 (fetch read data to FF)
            st4_addr  <= st3_addr;
            st4_data0 <= mem0_rdata;
            st4_data1 <= mem1_rdata;
            st4_valid <= st3_valid;
        end
    end

    assign mem0_ren   = st1_valid;
    assign mem0_raddr = st1_addr;
    assign mem1_ren   = st1_valid;
    assign mem1_raddr = st1_addr;

    assign m_addr  = st4_addr;
    assign m_data0 = st4_data0;
    assign m_data1 = st4_data1;
    assign m_valid = st4_valid;
    
endmodule

`default_nettype wire

