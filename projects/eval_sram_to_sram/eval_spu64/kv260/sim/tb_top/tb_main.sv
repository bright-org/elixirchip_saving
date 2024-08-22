

`timescale 1ns / 1ps
`default_nettype none


// 以降は Verilator で C++ のテストドライバも使えるように時間待ちを書かない
module tb_main
        #(
            parameter   WB_ADR_WIDTH = 37,
            parameter   WB_DAT_WIDTH = 64,
            parameter   WB_SEL_WIDTH = (WB_DAT_WIDTH / 8)
        )
        (
            input   var logic                       reset,
            input   var logic                       clk300,
            input   var logic                       clk500,
    
            input   var logic   [WB_ADR_WIDTH-1:0]  s_wb_adr_i,
            output  var logic   [WB_DAT_WIDTH-1:0]  s_wb_dat_o,
            input   var logic   [WB_DAT_WIDTH-1:0]  s_wb_dat_i,
            input   var logic   [WB_SEL_WIDTH-1:0]  s_wb_sel_i,
            input   var logic                       s_wb_we_i,
            input   var logic                       s_wb_stb_i,
            output  var logic                       s_wb_ack_o
        );

    // -----------------------------------------
    //  top
    // -----------------------------------------
    
    eval_sram_to_sram_spu_kv260
        u_top
            (
                .fan_en     ()
            );
    
    // Zynq のスタブの中にクロックとバスアクセスを接続
    always_comb force u_top.u_design_1.reset  = reset;
    always_comb force u_top.u_design_1.clk300 = clk300;
    always_comb force u_top.u_design_1.clk500 = clk500;

    always_comb force u_top.u_design_1.wb_adr_i = s_wb_adr_i;
    always_comb force u_top.u_design_1.wb_dat_i = s_wb_dat_i;
    always_comb force u_top.u_design_1.wb_sel_i = s_wb_sel_i;
    always_comb force u_top.u_design_1.wb_we_i  = s_wb_we_i;
    always_comb force u_top.u_design_1.wb_stb_i = s_wb_stb_i;

    assign s_wb_dat_o = u_top.u_design_1.wb_dat_o;
    assign s_wb_ack_o = u_top.u_design_1.wb_ack_o;
    

endmodule


`default_nettype wire


// end of file
