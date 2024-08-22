`timescale 1ns / 1ps
`default_nettype none


// ストリームプロセッシングユニットのサンプル
module stream_processing_unit
        #(
            parameter int  DATA_BITS = 64
        )
        (
            // system
            input   var logic                       reset,      // リセット
            input   var logic                       clk,        // クロック
            input   var logic                       cke,        // クロックイネーブル

            // input port
            input   var logic   [DATA_BITS-1:0]     s_data0,    // source0
            input   var logic   [DATA_BITS-1:0]     s_data1,    // source1
            input   var logic                       s_valid,    // データ有効

            // output port
            output  var logic   [DATA_BITS-1:0]     m_data0,    // destination0
            output  var logic   [DATA_BITS-1:0]     m_data1,    // destination1
            output  var logic                       m_valid     // データ有効
        );


    // 演算単位定義 (ここでは INT8 とする)
    localparam  int     CALC_BITS    = 8;
    localparam  type    calc_t       = logic signed [CALC_BITS-1:0];

    // 演算エレメントの並列/直列数
    localparam  int     PARALLEL_LEN = DATA_BITS / CALC_BITS;  // 並列数
    localparam  int     SERIAL_LEN   = 256;                    // 直列数

    // 並列データ型定義
    localparam  type    data_t     = calc_t [PARALLEL_LEN-1:0];


    // 演算エレメントを直並列に並べる
    data_t                      calc_data0    [SERIAL_LEN:0];
    data_t                      calc_data1    [SERIAL_LEN:0];
    logic   [PARALLEL_LEN-1:0]  calc_valid    [SERIAL_LEN:0];

    // input
    assign calc_data0[0] = s_data0;
    assign calc_data1[0] = s_data1;
    assign calc_valid[0] = {PARALLEL_LEN{s_valid}};

    for ( genvar i = 0; i < SERIAL_LEN; i++ ) begin : serial_calc
        for ( genvar j = 0; j < PARALLEL_LEN; j++ ) begin : parallel_calc

            // 演算エレメント
            spu_calc_element
                    #(
                        .DATA_BITS      (CALC_BITS              ),
                        .data_t         (calc_t                 )
                    )
                u_spu_calc_element
                    (
                        .reset           ,
                        .clk             ,
                        .cke             ,

                        .s_data0         (calc_data0[i][j]      ),
                        .s_data1         (calc_data1[i][j]      ),
                        .s_valid         (calc_valid[i][j]      ),

                        .m_data0         (calc_data0[i+1][j]    ),
                        .m_data1         (calc_data1[i+1][j]    ),
                        .m_valid         (calc_valid[i+1][j]    )
                    );
        end
    end

    // output
    assign m_data0 = calc_data0[SERIAL_LEN];
    assign m_data1 = calc_data1[SERIAL_LEN];
    assign m_valid = calc_valid[SERIAL_LEN][0];

endmodule


`default_nettype wire

