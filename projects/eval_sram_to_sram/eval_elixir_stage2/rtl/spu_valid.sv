
`timescale 1ns / 1ps
`default_nettype none

// valid信号のパイプライン化
module spu_valid
        #(
            parameter int  LATENCY = 1
        )
        (
            input   var logic       reset       ,
            input   var logic       clk         ,
            input   var logic       cke         ,

            input   var logic       s_valid     ,

            output  var logic       m_valid     
        );

    // LATENCY が負の値なら合成時エラーにする
    initial begin
        if ( LATENCY < 0 ) begin
            $error("Error: LATENCY must be positive value.");
            $finish;
        end
    end

    // パイプライン遅延
    logic       stage_valid [0:LATENCY];
    assign stage_valid[0] = s_valid;

    for ( genvar i = 0; i < LATENCY; i++ ) begin : stage
        always_ff @( posedge clk ) begin
            if ( reset ) begin
                stage_valid[i+1] <= 1'b0;
            end
            else if ( cke ) begin
                stage_valid[i+1] <= stage_valid[i];
            end
        end
    end

    assign m_valid = stage_valid[LATENCY];

endmodule


`default_nettype wire

