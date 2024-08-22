
`timescale 1ns / 1ps
`default_nettype none


module sample_add
            (
//                input   var logic           cin     ,
                input   var logic   [7:0]   din0    ,
                input   var logic   [7:0]   din1    ,
                output  var logic   [7:0]   dout    
            );

    assign dout = din0 + din1;// + cin;

endmodule


`default_nettype wire

