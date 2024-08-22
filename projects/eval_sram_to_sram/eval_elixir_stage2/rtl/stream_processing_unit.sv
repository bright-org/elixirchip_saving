`timescale 1ns / 1ps
`default_nettype none


// ストリームプロセッシングユニットのサンプル
module stream_processing_unit
        (
            // system
            input   var logic               reset   ,   // リセット
            input   var logic               clk     ,   // クロック
            input   var logic               cke     ,   // クロックイネーブル

            // input port
            input   var logic   [63:0]      s_data0 ,   // source0
            input   var logic   [63:0]      s_data1 ,   // source1
            input   var logic               s_valid ,   // データ有効

            // output port
            output  var logic   [63:0]      m_data0 ,   // destination0
            output  var logic   [63:0]      m_data1 ,   // destination1
            output  var logic               m_valid     // データ有効
        );


    // --------------------------------------------------
    //  Stage 0 (a + 2), (1 + b)
    // --------------------------------------------------
    
    localparam STAGE0_LATENCY = 1;

    // data0
    logic   [7:0]   stage0_data0_0;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_0
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*0 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_0     )
            );
    
    logic   [7:0]   stage0_data0_1;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_1
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*1 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_1     )
            );
    

    logic   [7:0]   stage0_data0_2;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_2
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*2 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_2     )
            );
    

    logic   [7:0]   stage0_data0_3;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_3
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*3 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_3     )
            );
    

    logic   [7:0]   stage0_data0_4;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_4
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*4 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_4     )
            );
    
    logic   [7:0]   stage0_data0_5;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_5
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*5 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_5     )
            );
    
    logic   [7:0]   stage0_data0_6;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_6
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*6 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_6     )
            );
    
    logic   [7:0]   stage0_data0_7;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_0_7
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (s_data0[8*7 +: 8]  ),
                .s_data1        (8'd2               ),  // immediate

                .m_data         (stage0_data0_7     )
            );
    

    // data1
    logic   [7:0]  stage0_data1_0;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_0
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*0 +: 8]  ),

                .m_data         (stage0_data1_0     )
            );

    logic   [7:0]  stage0_data1_1;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_1
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*1 +: 8]  ),

                .m_data         (stage0_data1_1     )
            );

    logic   [7:0]  stage0_data1_2;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_2
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*2 +: 8]  ),

                .m_data         (stage0_data1_2     )
            );

    logic   [7:0]  stage0_data1_3;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_3
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*3 +: 8]  ),

                .m_data         (stage0_data1_3     )
            );

    logic   [7:0]  stage0_data1_4;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_4
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*4 +: 8]  ),

                .m_data         (stage0_data1_4     )
            );
   
    logic   [7:0]  stage0_data1_5;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_5
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*5 +: 8]  ),

                .m_data         (stage0_data1_5     )
            );
    
    logic   [7:0]  stage0_data1_6;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_6
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*6 +: 8]  ),

                .m_data         (stage0_data1_6     )
            );
   
    logic   [7:0]  stage0_data1_7;
    spu_add
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_0_1_7
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (8'd1               ),  // immediate
                .s_data1        (s_data1[8*7 +: 8]  ),

                .m_data         (stage0_data1_7     )
            );

    // valid
    logic           stage0_valid;
    spu_valid
            #(
                .LATENCY        (STAGE0_LATENCY     )
            )
        u_spu_valid_0
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_valid        (s_valid            ), 

                .m_valid        (stage0_valid       )
            );


    // --------------------------------------------------
    //  Stage 1 (a - b), 0
    // --------------------------------------------------
    
    localparam STAGE1_LATENCY = 1;

    // data0
    logic   [7:0]   stage1_data0_0;
    spu_sub
            #(
                .LATENCY        (STAGE1_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_0
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_0    ),
                .s_data1        (stage0_data1_0    ),

                .m_data         (stage1_data0_0    )
            );
    
    logic   [7:0]   stage1_data0_1;
    spu_sub
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_1
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_1    ),
                .s_data1        (stage0_data1_1    ),

                .m_data         (stage1_data0_1    )
            );
    

    logic   [7:0]   stage1_data0_2;
    spu_sub
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_2
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_2    ),
                .s_data1        (stage0_data1_2    ),

                .m_data         (stage1_data0_2    )
            );
    

    logic   [7:0]   stage1_data0_3;
    spu_sub
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_3
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_3    ),
                .s_data1        (stage0_data1_3    ),

                .m_data         (stage1_data0_3    )
            );
    

    logic   [7:0]   stage1_data0_4;
    spu_sub
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_4
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_4    ),
                .s_data1        (stage0_data1_4    ),

                .m_data         (stage1_data0_4    )
            );
    
    logic   [7:0]   stage1_data0_5;
    spu_sub
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_5
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_5    ),
                .s_data1        (stage0_data1_5    ),

                .m_data         (stage1_data0_5    )
            );
    
    logic   [7:0]   stage1_data0_6;
    spu_sub
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_6
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_6    ),
                .s_data1        (stage0_data1_6    ),

                .m_data         (stage1_data0_6    )
            );
    
    logic   [7:0]   stage1_data0_7;
    spu_sub
            #(
                .LATENCY        (STAGE0_LATENCY     ),
                .S_DATA0_BITS   (8                  ),
                .S_DATA1_BITS   (8                  ),
                .M_DATA_BITS    (8                  )
            )
        u_spu_op_1_0_7
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data0        (stage0_data0_7    ),
                .s_data1        (stage0_data1_7    ),

                .m_data         (stage1_data0_7    )
            );
    

    // valid
    logic           stage1_valid;
    spu_valid
            #(
                .LATENCY        (STAGE1_LATENCY     )
            )
        u_spu_valid_1
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_valid        (stage0_valid      ), 

                .m_valid        (stage1_valid      )
            );


    // --------------------------------------------------
    //  output
    // --------------------------------------------------

    assign m_data0[8*0 +: 8] = stage1_data0_0;
    assign m_data0[8*1 +: 8] = stage1_data0_1;
    assign m_data0[8*2 +: 8] = stage1_data0_2;
    assign m_data0[8*3 +: 8] = stage1_data0_3;
    assign m_data0[8*4 +: 8] = stage1_data0_4;
    assign m_data0[8*5 +: 8] = stage1_data0_5;
    assign m_data0[8*6 +: 8] = stage1_data0_6;
    assign m_data0[8*7 +: 8] = stage1_data0_7;

    assign m_data1 = '0;

    assign m_valid = stage1_valid;

endmodule


`default_nettype wire

