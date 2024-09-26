
`timescale 1ns / 1ps
`default_nettype none


// ボード依存のトップネット(KR260用)
module eval_sram_to_sram_spu_kr260
        #(
            parameter   DEVICE          = "ULTRASCALE_PLUS" ,   // デバイス名
            parameter   SIMULATION      = "false"           ,   // シミュレーション
            parameter   DEBUG           = "false"               // デバッグ
        )
        (
            output  var logic    fan_en
        );


    localparam int  AXI4L_ADDR_BITS = 40;
    localparam int  AXI4L_DATA_BITS = 64;
    localparam int  AXI4L_STRB_BITS = AXI4L_DATA_BITS / 8;

    logic                           core_reset      ;
    logic                           core_clk        ;

    logic   [0:0]                   axi4l_aresetn   ;
    logic                           axi4l_aclk      ;
    logic   [AXI4L_ADDR_BITS-1:0]   axi4l_awaddr    ;
    logic   [2:0]                   axi4l_awprot    ;
    logic                           axi4l_awvalid   ;
    logic                           axi4l_awready   ;
    logic   [AXI4L_DATA_BITS-1:0]   axi4l_wdata     ;
    logic   [AXI4L_STRB_BITS-1:0]   axi4l_wstrb     ;
    logic                           axi4l_wvalid    ;
    logic                           axi4l_wready    ;
    logic   [1:0]                   axi4l_bresp     ;
    logic                           axi4l_bvalid    ;
    logic                           axi4l_bready    ;
    logic   [AXI4L_ADDR_BITS-1:0]   axi4l_araddr    ;
    logic   [2:0]                   axi4l_arprot    ;
    logic                           axi4l_arvalid   ;
    logic                           axi4l_arready   ;
    logic   [AXI4L_DATA_BITS-1:0]   axi4l_rdata     ;
    logic   [1:0]                   axi4l_rresp     ;
    logic                           axi4l_rvalid    ;
    logic                           axi4l_rready    ;

    design_1
        u_design_1
            (
                .fan_en,
                
                .core_reset,
                .core_clk,

                .m_axi4l_aresetn    (axi4l_aresetn      ),
                .m_axi4l_aclk       (axi4l_aclk         ),
                .m_axi4l_awaddr     (axi4l_awaddr       ),
                .m_axi4l_awprot     (axi4l_awprot       ),
                .m_axi4l_awvalid    (axi4l_awvalid      ),
                .m_axi4l_awready    (axi4l_awready      ),
                .m_axi4l_wdata      (axi4l_wdata        ),
                .m_axi4l_wstrb      (axi4l_wstrb        ),
                .m_axi4l_wvalid     (axi4l_wvalid       ),
                .m_axi4l_wready     (axi4l_wready       ),
                .m_axi4l_bresp      (axi4l_bresp        ),
                .m_axi4l_bvalid     (axi4l_bvalid       ),
                .m_axi4l_bready     (axi4l_bready       ),
                .m_axi4l_araddr     (axi4l_araddr       ),
                .m_axi4l_arprot     (axi4l_arprot       ),
                .m_axi4l_arvalid    (axi4l_arvalid      ),
                .m_axi4l_arready    (axi4l_arready      ),
                .m_axi4l_rdata      (axi4l_rdata        ),
                .m_axi4l_rresp      (axi4l_rresp        ),
                .m_axi4l_rvalid     (axi4l_rvalid       ),
                .m_axi4l_rready     (axi4l_rready       )
            );


    // main
    eval_sram_to_sram_spu_main
            #(
                .AXI4L_ADDR_BITS    (AXI4L_ADDR_BITS    ),
                .AXI4L_DATA_BITS    (AXI4L_DATA_BITS    ),
                .DEVICE             (DEVICE             ),
                .SIMULATION         (SIMULATION         ),
                .DEBUG              (DEBUG              )

            )
        u_eval_sram_to_sram_spu_main
            (
                .core_reset         (core_reset         ),
                .core_clk           (core_clk           ),
                
                .s_axi4l_aresetn    (axi4l_aresetn      ),
                .s_axi4l_aclk       (axi4l_aclk         ),
                .s_axi4l_awaddr     (axi4l_awaddr       ),
                .s_axi4l_awprot     (axi4l_awprot       ),
                .s_axi4l_awvalid    (axi4l_awvalid      ),
                .s_axi4l_awready    (axi4l_awready      ),
                .s_axi4l_wdata      (axi4l_wdata        ),
                .s_axi4l_wstrb      (axi4l_wstrb        ),
                .s_axi4l_wvalid     (axi4l_wvalid       ),
                .s_axi4l_wready     (axi4l_wready       ),
                .s_axi4l_bresp      (axi4l_bresp        ),
                .s_axi4l_bvalid     (axi4l_bvalid       ),
                .s_axi4l_bready     (axi4l_bready       ),
                .s_axi4l_araddr     (axi4l_araddr       ),
                .s_axi4l_arprot     (axi4l_arprot       ),
                .s_axi4l_arvalid    (axi4l_arvalid      ),
                .s_axi4l_arready    (axi4l_arready      ),
                .s_axi4l_rdata      (axi4l_rdata        ),
                .s_axi4l_rresp      (axi4l_rresp        ),
                .s_axi4l_rvalid     (axi4l_rvalid       ),
                .s_axi4l_rready     (axi4l_rready       )
        );


endmodule

`default_nettype wire

