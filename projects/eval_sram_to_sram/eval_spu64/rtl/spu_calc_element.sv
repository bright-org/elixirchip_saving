
`timescale 1ns / 1ps
`default_nettype none


// 演算エレメントのサンプル
(* use_dsp = "no" *)
module spu_calc_element
        #(
            parameter int  DATA_BITS      = 8,
            parameter type data_t         = logic signed [DATA_BITS-1:0]
        )
        (
            input   var logic   reset           ,
            input   var logic   clk             ,
            input   var logic   cke             ,

            input   var data_t  s_data0         ,
            input   var data_t  s_data1         ,
            input   var logic   s_valid         ,

            output  var data_t  m_data0         ,
            output  var data_t  m_data1         ,
            output  var logic   m_valid         
        );


    // --------------------------------------------------
    //  IP core コアで行う乗算のみ別パイプライン
    // --------------------------------------------------

    // 別途生成した3段パイプラインの INT8 乗算
    mul_s8s8_lo8_p3
        u_mul_s8s8_lo8_p3
            (
                .CLK    (clk        ),
                .CE     (cke        ),
                .A      (s_data0    ),
                .B      (s_data1    ),
                .P      (m_data0    )
            );



    // --------------------------------------------------
    //  加算パイプライン (乗算に合わせて3段にする)
    // --------------------------------------------------

    data_t  st0_data0;
    data_t  st0_data1;
    logic   st0_valid;

    data_t  st1_data1;
    logic   st1_valid;

    data_t  st2_data1;
    logic   st2_valid;

    always_ff @( posedge clk ) begin
        if ( reset ) begin
            st0_data0 <= 'x;
            st0_data1 <= 'x;
            st0_valid <= 1'b0;

            st1_data1 <= 'x;
            st1_valid <= 1'b0;

            st2_data1 <= 'x;
            st2_valid <= 1'b0;
        end
        else if ( cke ) begin
            // stage0
            st0_data0 <= s_data0;
            st0_data1 <= s_data1;
            st0_valid <= s_valid;

            // stage1
            st1_data1 <= st0_data0 + st0_data1;
            st1_valid <= st0_valid;

            // stage2
            st2_data1 <= st1_data1;
            st2_valid <= st1_valid;

        end
    end

    assign m_data1 = st2_data1;
    assign m_valid = st2_valid;

endmodule


`default_nettype wire

