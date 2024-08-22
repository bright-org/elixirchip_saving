
`timescale 1ns / 1ps
`default_nettype none


module eval_sram_to_sram_any_main
        #(
            parameter int  AXI4L_ADDR_BITS = 40,
            parameter int  AXI4L_DATA_BITS = 64,
            parameter int  AXI4L_STRB_BITS = AXI4L_DATA_BITS / 8
        )
        (
            input   var logic                           core_reset      ,
            input   var logic                           core_clk        ,

            input   var logic   [0:0]                   s_axi4l_aresetn ,
            input   var logic                           s_axi4l_aclk    ,
            input   var logic   [AXI4L_ADDR_BITS-1:0]   s_axi4l_awaddr  ,
            input   var logic   [2:0]                   s_axi4l_awprot  ,
            input   var logic                           s_axi4l_awvalid ,
            output  var logic                           s_axi4l_awready ,
            input   var logic   [AXI4L_DATA_BITS-1:0]   s_axi4l_wdata   ,
            input   var logic   [AXI4L_STRB_BITS-1:0]   s_axi4l_wstrb   ,
            input   var logic                           s_axi4l_wvalid  ,
            output  var logic                           s_axi4l_wready  ,
            output  var logic   [1:0]                   s_axi4l_bresp   ,
            output  var logic                           s_axi4l_bvalid  ,
            input   var logic                           s_axi4l_bready  ,
            input   var logic   [AXI4L_ADDR_BITS-1:0]   s_axi4l_araddr  ,
            input   var logic   [2:0]                   s_axi4l_arprot  ,
            input   var logic                           s_axi4l_arvalid ,
            output  var logic                           s_axi4l_arready ,
            output  var logic   [AXI4L_DATA_BITS-1:0]   s_axi4l_rdata   ,
            output  var logic   [1:0]                   s_axi4l_rresp   ,
            output  var logic                           s_axi4l_rvalid  ,
            input   var logic                           s_axi4l_rready  
        );

    // AXI4L => WISHBONE
    localparam  WB_ADR_BITS = AXI4L_ADDR_BITS - $clog2(AXI4L_STRB_BITS);
    localparam  WB_DAT_BITS = AXI4L_DATA_BITS;
    localparam  WB_SEL_BITS = AXI4L_STRB_BITS;
    
    logic                           wb_rst_i;
    logic                           wb_clk_i;
    logic   [WB_ADR_BITS-1:0]       wb_adr_i;
    logic   [WB_DAT_BITS-1:0]       wb_dat_o;
    logic   [WB_DAT_BITS-1:0]       wb_dat_i;
    logic   [WB_SEL_BITS-1:0]       wb_sel_i;
    logic                           wb_we_i ;
    logic                           wb_stb_i;
    logic                           wb_ack_o;
    
    jelly_axi4l_to_wishbone
            #(
                .AXI4L_ADDR_WIDTH   (AXI4L_ADDR_BITS        ),
                .AXI4L_DATA_SIZE    ($clog2(AXI4L_STRB_BITS))     // 0:8bit, 1:16bit, 2:32bit ...
            )
        i_axi4l_to_wishbone
            (
                .s_axi4l_aresetn    (s_axi4l_aresetn        ),
                .s_axi4l_aclk       (s_axi4l_aclk           ),
                .s_axi4l_awaddr     (s_axi4l_awaddr         ),
                .s_axi4l_awprot     (s_axi4l_awprot         ),
                .s_axi4l_awvalid    (s_axi4l_awvalid        ),
                .s_axi4l_awready    (s_axi4l_awready        ),
                .s_axi4l_wstrb      (s_axi4l_wstrb          ),
                .s_axi4l_wdata      (s_axi4l_wdata          ),
                .s_axi4l_wvalid     (s_axi4l_wvalid         ),
                .s_axi4l_wready     (s_axi4l_wready         ),
                .s_axi4l_bresp      (s_axi4l_bresp          ),
                .s_axi4l_bvalid     (s_axi4l_bvalid         ),
                .s_axi4l_bready     (s_axi4l_bready         ),
                .s_axi4l_araddr     (s_axi4l_araddr         ),
                .s_axi4l_arprot     (s_axi4l_arprot         ),
                .s_axi4l_arvalid    (s_axi4l_arvalid        ),
                .s_axi4l_arready    (s_axi4l_arready        ),
                .s_axi4l_rdata      (s_axi4l_rdata          ),
                .s_axi4l_rresp      (s_axi4l_rresp          ),
                .s_axi4l_rvalid     (s_axi4l_rvalid         ),
                .s_axi4l_rready     (s_axi4l_rready         ),
                
                .m_wb_rst_o         (wb_rst_i               ),
                .m_wb_clk_o         (wb_clk_i               ),
                .m_wb_adr_o         (wb_adr_i               ),
                .m_wb_dat_i         (wb_dat_o               ),
                .m_wb_dat_o         (wb_dat_i               ),
                .m_wb_sel_o         (wb_sel_i               ),
                .m_wb_we_o          (wb_we_i                ),
                .m_wb_stb_o         (wb_stb_i               ),
                .m_wb_ack_i         (wb_ack_o               )
            );
    

    sram_to_sram_any
            #(
                .MEM_ADDR_BITS      (10             ),
                .MEM_DATA_BITS      (512            ),
                .MEM_RAM_TYPE       ("block"        ),
                .WB_ADR_BITS        (15             ),
                .WB_DAT_BITS        (64             )
            )
        u_sram_to_sram_any
            (
                .core_reset         (core_reset     ),
                .core_clk           (core_clk       ),
                .s_wb_rst_i         (wb_rst_i       ),
                .s_wb_clk_i         (wb_clk_i       ),
                .s_wb_adr_i         (wb_adr_i[14:0] ),
                .s_wb_dat_i         (wb_dat_i       ),
                .s_wb_dat_o         (wb_dat_o       ),
                .s_wb_we_i          (wb_we_i        ),
                .s_wb_sel_i         (wb_sel_i       ),
                .s_wb_stb_i         (wb_stb_i       ),
                .s_wb_ack_o         (wb_ack_o       )
            );



endmodule

`default_nettype wire

