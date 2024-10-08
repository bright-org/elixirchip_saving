`timescale 1 ps / 1 ps

module design_1
   (fan_en,
    core_clk,
    core_reset,
    m_axi4l_aclk,
    m_axi4l_araddr,
    m_axi4l_aresetn,
    m_axi4l_arprot,
    m_axi4l_arready,
    m_axi4l_arvalid,
    m_axi4l_awaddr,
    m_axi4l_awprot,
    m_axi4l_awready,
    m_axi4l_awvalid,
    m_axi4l_bready,
    m_axi4l_bresp,
    m_axi4l_bvalid,
    m_axi4l_rdata,
    m_axi4l_rready,
    m_axi4l_rresp,
    m_axi4l_rvalid,
    m_axi4l_wdata,
    m_axi4l_wready,
    m_axi4l_wstrb,
    m_axi4l_wvalid);
  output fan_en;
  output core_clk;
  output [0:0]core_reset;
  output m_axi4l_aclk;
  output [39:0]m_axi4l_araddr;
  output [0:0]m_axi4l_aresetn;
  output [2:0]m_axi4l_arprot;
  input m_axi4l_arready;
  output m_axi4l_arvalid;
  output [39:0]m_axi4l_awaddr;
  output [2:0]m_axi4l_awprot;
  input m_axi4l_awready;
  output m_axi4l_awvalid;
  output m_axi4l_bready;
  input [1:0]m_axi4l_bresp;
  input m_axi4l_bvalid;
  input [63:0]m_axi4l_rdata;
  output m_axi4l_rready;
  input [1:0]m_axi4l_rresp;
  input m_axi4l_rvalid;
  output [63:0]m_axi4l_wdata;
  input m_axi4l_wready;
  output [7:0]m_axi4l_wstrb;
  output m_axi4l_wvalid;

  wire fan_en;
  wire core_clk;
  wire [0:0]core_reset;
  wire m_axi4l_aclk;
  wire [39:0]m_axi4l_araddr;
  wire [0:0]m_axi4l_aresetn;
  wire [2:0]m_axi4l_arprot;
  wire m_axi4l_arready;
  wire m_axi4l_arvalid;
  wire [39:0]m_axi4l_awaddr;
  wire [2:0]m_axi4l_awprot;
  wire m_axi4l_awready;
  wire m_axi4l_awvalid;
  wire m_axi4l_bready;
  wire [1:0]m_axi4l_bresp;
  wire m_axi4l_bvalid;
  wire [63:0]m_axi4l_rdata;
  wire m_axi4l_rready;
  wire [1:0]m_axi4l_rresp;
  wire m_axi4l_rvalid;
  wire [63:0]m_axi4l_wdata;
  wire m_axi4l_wready;
  wire [7:0]m_axi4l_wstrb;
  wire m_axi4l_wvalid;



    // テストベンチから force する前提の信号
    reg             reset           /*verilator public_flat*/;
    reg             clk300          /*verilator public_flat*/;
    reg             clk500          /*verilator public_flat*/;

    reg     [36:0]  wb_adr_i        /*verilator public_flat*/;
    reg     [63:0]  wb_dat_o        /*verilator public_flat*/;
    reg     [63:0]  wb_dat_i        /*verilator public_flat*/;
    reg     [7:0]   wb_sel_i        /*verilator public_flat*/;
    reg             wb_we_i         /*verilator public_flat*/;
    reg             wb_stb_i        /*verilator public_flat*/;
    reg             wb_ack_o        /*verilator public_flat*/;
    
    assign core_reset            = reset;
    assign core_clk              = clk500;
//    assign m_axi4l_aresetn    = ~reset;
//    assign m_axi4l_aclk       = clk300;
    
    jelly_wishbone_to_axi4l
            #(
                .WB_ADR_WIDTH           (37 ),
                .WB_DAT_SIZE            (3  )     // 0:8bit, 1:16bit, 2:32bit ...
            )
        i_wishbone_to_axi4l_peri
            (
                .s_wb_rst_i             (reset              ),
                .s_wb_clk_i             (clk300             ),
                .s_wb_adr_i             (wb_adr_i           ),
                .s_wb_dat_o             (wb_dat_o           ),
                .s_wb_dat_i             (wb_dat_i           ),
                .s_wb_sel_i             (wb_sel_i           ),
                .s_wb_we_i              (wb_we_i            ),
                .s_wb_stb_i             (wb_stb_i           ),
                .s_wb_ack_o             (wb_ack_o           ),

                .m_axi4l_aresetn        (m_axi4l_aresetn    ),
                .m_axi4l_aclk           (m_axi4l_aclk       ),
                .m_axi4l_awaddr         (m_axi4l_awaddr     ),
                .m_axi4l_awprot         (m_axi4l_awprot     ),
                .m_axi4l_awvalid        (m_axi4l_awvalid    ),
                .m_axi4l_awready        (m_axi4l_awready    ),
                .m_axi4l_wstrb          (m_axi4l_wstrb      ),
                .m_axi4l_wdata          (m_axi4l_wdata      ),
                .m_axi4l_wvalid         (m_axi4l_wvalid     ),
                .m_axi4l_wready         (m_axi4l_wready     ),
                .m_axi4l_bresp          (m_axi4l_bresp      ),
                .m_axi4l_bvalid         (m_axi4l_bvalid     ),
                .m_axi4l_bready         (m_axi4l_bready     ),
                .m_axi4l_araddr         (m_axi4l_araddr     ),
                .m_axi4l_arprot         (m_axi4l_arprot     ),
                .m_axi4l_arvalid        (m_axi4l_arvalid    ),
                .m_axi4l_arready        (m_axi4l_arready    ),
                .m_axi4l_rdata          (m_axi4l_rdata      ),
                .m_axi4l_rresp          (m_axi4l_rresp      ),
                .m_axi4l_rvalid         (m_axi4l_rvalid     ),
                .m_axi4l_rready         (m_axi4l_rready     )
            );
    


endmodule
