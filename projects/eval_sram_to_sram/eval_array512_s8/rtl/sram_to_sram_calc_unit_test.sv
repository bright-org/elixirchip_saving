
`timescale 1ns / 1ps
`default_nettype none


(* use_dsp = "no" *)
module sram_to_sram_calc_unit
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

            input   var data_t  [UNIT_LEN-1:0]          s_data0         ,
            input   var data_t  [UNIT_LEN-1:0]          s_data1         ,
            input   var logic                           s_valid         ,

            output  var data_t  [UNIT_LEN-1:0]          m_data0         ,
            output  var data_t  [UNIT_LEN-1:0]          m_data1         ,
            output  var logic                           m_valid         
        );

//(* retiming_backward = 1 *)
//(* retiming_forward = 1 *)
//   (* DONT_TOUCH = "yes" *) 
    
    data_t  [UNIT_LEN-1:0]  st0_data0;
    data_t  [UNIT_LEN-1:0]  st0_data1;
    logic                   st0_valid;

    data_t  [UNIT_LEN-1:0]  st1_data0;
    data_t  [UNIT_LEN-1:0]  st1_data1;
    logic                   st1_valid;
    data_t  [UNIT_LEN-1:0]  st2_data0;
    data_t  [UNIT_LEN-1:0]  st2_data1;
    logic                   st2_valid;

    /*
    (* DONT_TOUCH = "yes" *)    data_t  [UNIT_LEN-1:0]  st3_data0;
    (* DONT_TOUCH = "yes" *)    data_t  [UNIT_LEN-1:0]  st3_data1;
    (* DONT_TOUCH = "yes" *)    logic                   st3_valid;

    (* DONT_TOUCH = "yes" *)    data_t  [UNIT_LEN-1:0]  st4_data0;
    (* DONT_TOUCH = "yes" *)    data_t  [UNIT_LEN-1:0]  st4_data1;
    (* DONT_TOUCH = "yes" *)    logic                   st4_valid;
    */

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_data0 <= 'x;
            st0_data1 <= 'x;
            st0_valid <= 1'b0;

            st1_data0 <= 'x;
            st1_data1 <= 'x;
            st1_valid <= 1'b0;

            st2_data0 <= 'x;
            st2_data1 <= 'x;
            st2_valid <= 1'b0;

//            st3_data0 <= '0;
//            st3_data1 <= '0;
//            st3_valid <= 1'b0;
//
//            st4_data0 <= '0;
//            st4_data1 <= '0;
//            st4_valid <= 1'b0;
        end
        else if ( cke ) begin
            // stage0
            st0_data0 <= s_data0;
            st0_data1 <= s_data1;
            st0_valid <= s_valid;

            // stage1
            for ( int i = 0; i < UNIT_LEN; i++) begin
                st1_data0[i] <= st0_data0[i] - st0_data1[i];
                st1_data1[i] <= st0_data0[i] + st0_data1[i];
            end
            st1_valid <= st0_valid;

            // stage2
            st2_data0 <= st1_data0;
            st2_data1 <= st1_data1;
            st2_valid <= st1_valid;

 //           // stage3
 //           st3_data0 <= st2_data0;
 //           st3_data1 <= st2_data1;
 //           st3_valid <= st2_valid;
//
 //           // stage4
 //           st4_data0 <= st3_data0;
 //           st4_data1 <= st3_data1;
 //           st4_valid <= st3_valid;
        end
    end

    /*
    always_ff @( posedge clk ) begin
        st3_data0 <= st2_data0;
        st3_data1 <= st2_data1;
        st4_data0 <= st3_data0;
        st4_data1 <= st3_data1;
    end
    */

    assign m_data0 = st2_data0;
    assign m_data1 = st2_data1;
    assign m_valid = st2_valid;

endmodule

`default_nettype wire

