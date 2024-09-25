
`timescale 1ns / 1ps
`default_nettype none


module mul_s8s8s8
        (
            input   var logic                   reset   ,   // 同期リセット(制論理)
            input   var logic                   clk     ,   // クロック
//          input   var logic                   cke     ,   // クロックイネーブル

            input   var logic   signed  [7:0]  s_data0 ,   // 入力データ0
            input   var logic   signed  [7:0]  s_data1 ,   // 入力データ1

            output  var logic   signed  [7:0]  m_data      // 出力データ
        );

    logic   signed  [7:0]   st0_data0;
    logic   signed  [7:0]   st0_data1;
    logic   signed  [7:0]   st1_data;
    logic   signed  [7:0]   st2_data;

    always_ff @( posedge clk ) begin
        st0_data0 <= s_data0;
        st0_data1 <= s_data1;
        st1_data  <= st0_data0 * st0_data1;
        st2_data  <= st1_data;
    end

    assign m_data = st2_data;

    /*
    elixirchip_es1_spu_op_mul
            #(
                .LATENCY            (3                  ),
                .S_DATA0_BITS       (8                  ),
                .S_DATA1_BITS       (8                  ),
                .M_DATA_BITS        (8                  ),
                .DATA_SHIFT         (0                  ),
                .CLEAR_DATA         ('x                 ),
                .IMMEDIATE_DATA0    (1'b0               ),
                .IMMEDIATE_DATA1    (1'b0               ),
                .DEVICE             ("ULTRASCALE_PLUS"  ),
                .SIMULATION         (1'b0               ),
                .DEBUG              (1'b0               )
            )
        u_elixirchip_es1_spu_op_mul
            (
                .reset              ,
                .clk                ,
                .cke                (1'b1               ), 

                .s_data0            ,
                .s_data1            ,
                .s_clear            (1'b0               ),
                .s_valid            (1'b1               ),
                
                .m_data             
            );
    */

endmodule


`default_nettype wire

