

`timescale 1ns / 1ps
`default_nettype none


module tb_main
        #(
            parameter           DEVICE     = "RTL"   ,   // デバイス名
            parameter           SIMULATION = "true"  ,   // シミュレーション
            parameter           DEBUG      = "false"     // デバッグ
        )
        (
            input   var logic       reset       ,
            input   var logic       clk         
        );

    // -----------------------------------------
    //  DUT top
    // -----------------------------------------

    localparam  int     INDEX_BITS = 10                     ;
    localparam  type    index_t    = logic [INDEX_BITS-1:0] ;
    localparam  int     DATA_BITS  = 2                      ;
    localparam  type    data_t     = logic [DATA_BITS-1:0]  ;
    localparam  int     STRB_BITS  = (DATA_BITS + 7) / 8    ;
    localparam  type    strb_t     = logic [STRB_BITS-1:0]  ;

     logic       cke = 1'b1 ;

     logic       s_first    ;
     logic       s_last     ;
     index_t     s_index0   ;
     data_t      s_data0    ;
     strb_t      s_strb0    ;
     index_t     s_index1   ;
     data_t      s_data1    ;
     strb_t      s_strb1    ;
     logic       s_valid    ;

     logic       m_first    ;
     logic       m_last     ;
     index_t     m_index0   ;
     data_t      m_data0    ;
     strb_t      m_strb0    ;
     index_t     m_index1   ;
     data_t      m_data1    ;
     strb_t      m_strb1    ;
     logic       m_valid    ;

    stream_processing_unit
            #(
                .INDEX_BITS     (INDEX_BITS ),
                .index_t        (index_t    ),
                .DATA_BITS      (DATA_BITS  ),
                .data_t         (data_t     ),
                .STRB_BITS      (STRB_BITS  ),
                .strb_t         (strb_t     ),
                .DEVICE         (DEVICE     ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      )
            )
        u_stream_processing_unit
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_first        ,
                .s_last         ,
                .s_index0       ,
                .s_data0        ,
                .s_strb0        ,
                .s_index1       ,
                .s_data1        ,
                .s_strb1        ,
                .s_valid        ,

                .m_first        ,
                .m_last         ,
                .m_index0       ,
                .m_data0        ,
                .m_strb0        ,
                .m_index1       ,
                .m_data1        ,
                .m_strb1        ,
                .m_valid         
            );

    
    
    
    // -----------------------------------------
    //  test bench
    // -----------------------------------------

    localparam int DATA_SIZE = 288;

    logic  [9:0]   test_data [0:DATA_SIZE-1];

    initial begin
        $readmemb("../input_data.txt", test_data);
    end

    int     cycle;
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_valid <= 0;
            cycle   <= 0;
        end
        else begin
            s_valid <= ($urandom_range(0, 580) < 500);
            cycle   <= cycle + int'(s_valid);
        end
    end

    assign s_first  = s_valid ? test_data[cycle % DATA_SIZE][3]   : 'x;
    assign s_last   = s_valid ? test_data[cycle % DATA_SIZE][2]   : 'x;
    assign s_index0 = s_valid ? index_t'(cycle % DATA_SIZE)       : 'x;
    assign s_data0  = s_valid ? test_data[cycle % DATA_SIZE][1:0] : 'x;
    assign s_strb0  = s_valid ? 1'b1                              : 'x;
    assign s_index1 = 'x;
    assign s_data1  = 'x;
    assign s_strb1  = 'x;

    // 出力
    int     log_fp;
    initial begin
        log_fp = $fopen("output_log.txt", "w");
    end

    int     output_count = 0;
    always_ff @(posedge clk) begin
        if ( !reset ) begin
            if ( m_valid ) begin
                $fwrite(log_fp, "%b_%b_%02b\n", m_first, m_last, m_data0);
                if ( m_last ) begin
                    output_count = output_count + 1;
                    if ( output_count > 10 ) begin
                        $finish;
                    end
                end
            end
        end
    end

endmodule


`default_nettype wire


// end of file
