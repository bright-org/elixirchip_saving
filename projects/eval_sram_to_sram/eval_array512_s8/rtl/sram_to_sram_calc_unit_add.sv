
`timescale 1ns / 1ps
`default_nettype none


(* use_dsp = "no" *)
module sram_to_sram_calc_unit
        #(
            parameter int  DATA_BITS      = 8,
            parameter type data_t         = logic signed [DATA_BITS-1:0],
            parameter int  UNIT_LEN       = 64,
            parameter bit  INSERT_PRE_FF  = 0,
            parameter bit  INSERT_POST_FF = 0
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

// [memo]
// (* retiming_backward = 1 *)
// (* retiming_forward = 1 *)
// (* DONT_TOUCH = "yes" *) 


    // stage0
    data_t  [UNIT_LEN-1:0]  st0_data0;
    data_t  [UNIT_LEN-1:0]  st0_data1;
    logic                   st0_valid;
    if ( INSERT_PRE_FF ) begin
        always_ff @( posedge clk ) begin
            if ( reset ) begin
                st0_data0 <= 'x;
                st0_data1 <= 'x;
                st0_valid <= 1'b0;
            end
            else if ( cke ) begin
                st0_data0 <= s_data0;
                st0_data1 <= s_data1;
                st0_valid <= s_valid;
            end
        end
    end
    else begin
        assign st0_data0 = s_data0;
        assign st0_data1 = s_data1;
        assign st0_valid = s_valid;
    end


    // stage1
    data_t  [UNIT_LEN-1:0]  st1_data0;
    data_t  [UNIT_LEN-1:0]  st1_data1;
    logic                   st1_valid;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st1_data0 <= 'x;
            st1_data1 <= 'x;
            st1_valid <= 1'b0;
        end
        else if ( cke ) begin
            for ( int i = 0; i < UNIT_LEN; i++) begin
                st1_data0[i] <= st0_data0[i] + (st0_data1[i] >>> 1);
                st1_data1[i] <= st0_data0[i] + st0_data1[i];
            end
            st1_valid <= st0_valid;
        end
    end


    // stage2
    data_t  [UNIT_LEN-1:0]  st2_data0;
    data_t  [UNIT_LEN-1:0]  st2_data1;
    logic                   st2_valid;
    if ( INSERT_POST_FF ) begin
        always_ff @( posedge clk ) begin
            if ( reset ) begin
                st2_data0 <= 'x;
                st2_data1 <= 'x;
                st2_valid <= 1'b0;
            end
            else if ( cke ) begin
                st2_data0 <= st1_data0;
                st2_data1 <= st1_data1;
                st2_valid <= st1_valid;
            end
        end
    end
    else begin
        assign st2_data0 = st1_data0;
        assign st2_data1 = st1_data1;
        assign st2_valid = st1_valid;
    end

    assign m_data0 = st2_data0;
    assign m_data1 = st2_data1;
    assign m_valid = st2_valid;

endmodule


`default_nettype wire

