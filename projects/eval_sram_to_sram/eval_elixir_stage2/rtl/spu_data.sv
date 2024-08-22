
`timescale 1ns / 1ps
`default_nettype none

// dataのパイプライン化
module spu_data
        #(
            parameter int  LATENCY   = 1,
            parameter int  DATA_BITS = 8
        )
        (
            input   var logic                   reset       ,
            input   var logic                   clk         ,
            input   var logic                   cke         ,

            input   var logic   [DATA_BITS-1:0] s_data      ,

            output  var logic   [DATA_BITS-1:0] m_data      
        );

    // LATENCY が負の値なら合成時エラーにする
    initial begin
        if ( LATENCY < 0 ) begin
            $error("Error: LATENCY must be positive value.");
            $finish;
        end
    end

    // パイプライン遅延
    logic   [DATA_BITS-1:0] stage_data  [0:LATENCY];
    assign stage_data[0] = s_data;

    for ( genvar i = 0; i < LATENCY; i++ ) begin : stage
        always_ff @( posedge clk ) begin
            if ( cke ) begin
                stage_data[i+1] <= stage_data[i];
            end
        end
    end

    assign m_data = stage_data[LATENCY];

endmodule


`default_nettype wire

