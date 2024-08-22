
`timescale 1ns / 1ps
`default_nettype none


module spu_es1_op_synth
            (
                input   var logic           reset   ,
                input   var logic           clk     ,

                input   var logic   [0:0]   din     ,
                output  var logic   [0:0]   dout    
            );

    parameter           DEVICE     = "ULTRASCALE_PLUS"  ;   // デバイス名
    parameter           SIMULATION = "false"            ;   // シミュレーション
    parameter           DEBUG      = "false"            ;   // デバッグ

    logic   cke = 1'b1;



    (* DONT_TOUCH = "true" *)   logic   [1023:0]    reg_ins;
                                logic   [1023:0]    sig_outs;
    assign dout = ^sig_outs;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            reg_ins <= '0;
        end
        else begin
            reg_ins <= 1024'({reg_ins, din});
        end
    end


    elixirchip_es1_spu_op_mem_sp_warapper
        u_elixirchip_es1_spu_op_mem_sp_warapper
            (
                .reset   ,
                .clk     ,
                .cke     ,
                
                .din     (reg_ins [0]   ),
                .dout    (sig_outs[0]   )
            );


    /*
    elixirchip_es1_spu_op_mem_warapper
        u_elixirchip_es1_spu_op_mem_warapper
            (
                .reset   ,
                .clk     ,
                .cke     ,
                
                .din     (reg_ins [0]   ),
                .dout    (sig_outs[0]   )
            );
    */


endmodule


`default_nettype wire

