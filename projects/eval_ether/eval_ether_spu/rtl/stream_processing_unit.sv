`timescale 1ns / 1ps
`default_nettype none


// ストリームプロセッシングユニット
module stream_processing_unit
        #(
            parameter   int     INDEX_BITS       = 11                               ,   // 添え字幅
            parameter   type    index_t          = logic [INDEX_BITS-1:0]           ,
            parameter   int     DATA_BITS        = 2                                ,   // データ幅
            parameter   type    data_t           = logic [DATA_BITS-1:0]            ,
            parameter   int     STRB_BITS        = (DATA_BITS + 7) / 8              ,   // ストローブ幅
            parameter   type    strb_t           = logic [STRB_BITS-1:0]            ,
            parameter   int     AXI4_ID_BITS     = 6                                ,
            parameter   int     AXI4_ADDR_BITS   = 49                               ,
            parameter   int     AXI4_DATA_BITS   = 512                              ,
            localparam  int     AXI4_STRB_BITS   = AXI4_DATA_BITS / 8               ,
            localparam  int     AXI4_LEN_BITS    = 8                                ,
            localparam  int     AXI4_SIZE_BITS   = 3                                ,
            localparam  int     AXI4_BURST_BITS  = 2                                ,
            localparam  int     AXI4_LOCK_BITS   = 1                                ,
            localparam  int     AXI4_CACHE_BITS  = 4                                ,
            localparam  int     AXI4_PROT_BITS   = 3                                ,
            localparam  int     AXI4_QOS_BITS    = 4                                ,
            localparam  int     AXI4_REGION_BITS = 4                                ,
            localparam  int     AXI4_RESP_BITS   = 2                                ,
            localparam  type    axi4_id_t        = logic   [AXI4_ID_BITS    -1:0]   ,
            localparam  type    axi4_addr_t      = logic   [AXI4_ADDR_BITS  -1:0]   ,
            localparam  type    axi4_len_t       = logic   [AXI4_LEN_BITS   -1:0]   ,
            localparam  type    axi4_size_t      = logic   [AXI4_SIZE_BITS  -1:0]   ,
            localparam  type    axi4_burst_t     = logic   [AXI4_BURST_BITS -1:0]   ,
            localparam  type    axi4_lock_t      = logic   [AXI4_LOCK_BITS  -1:0]   ,
            localparam  type    axi4_cache_t     = logic   [AXI4_CACHE_BITS -1:0]   ,
            localparam  type    axi4_prot_t      = logic   [AXI4_PROT_BITS  -1:0]   ,
            localparam  type    axi4_qos_t       = logic   [AXI4_QOS_BITS   -1:0]   ,
            localparam  type    axi4_region_t    = logic   [AXI4_REGION_BITS-1:0]   ,
            localparam  type    axi4_data_t      = logic   [AXI4_DATA_BITS  -1:0]   ,
            localparam  type    axi4_strb_t      = logic   [AXI4_STRB_BITS  -1:0]   ,
            localparam  type    axi4_resp_t      = logic   [AXI4_RESP_BITS  -1:0]   ,
            parameter           DEVICE           = "RTL"                            ,   // デバイス名
            parameter           SIMULATION       = "false"                          ,   // シミュレーション
            parameter           DEBUG            = "false"                              // デバッグ
        )
        (
            // system
            input   var logic           reset           ,   // リセット
            input   var logic           clk             ,   // クロック
            input   var logic           cke             ,   // クロックイネーブル

            // input port
            input   var logic           s_first         ,   // パケット先頭
            input   var logic           s_last          ,   // パケット末尾
            input   var index_t         s_index0        ,   // 配列の添え字0
            input   var data_t          s_data0         ,   // source0
            input   var strb_t          s_strb0         ,   // storobe0
            input   var index_t         s_index1        ,   // 配列の添え字1
            input   var data_t          s_data1         ,   // source1
            input   var strb_t          s_strb1         ,   // storobe1
            input   var logic           s_valid         ,   // データ有効

            // output port
            output  var logic           m_first         ,   // パケット先頭
            output  var logic           m_last          ,   // パケット末尾
            output  var index_t         m_index0        ,   // 配列の添え字
            output  var data_t          m_data0         ,   // destination0
            output  var strb_t          m_strb0         ,   // storobe0
            output  var index_t         m_index1        ,   // 配列の添え字
            output  var data_t          m_data1         ,   // destination1
            output  var strb_t          m_strb1         ,   // storobe1
            output  var logic           m_valid         ,   // データ有効

            // AXI4 manager port
            output  var axi4_id_t       m_axi4_awid     ,
            output  var axi4_addr_t     m_axi4_awaddr   ,
            output  var axi4_len_t      m_axi4_awlen    ,
            output  var axi4_size_t     m_axi4_awsize   ,
            output  var axi4_burst_t    m_axi4_awburst  ,
            output  var axi4_lock_t     m_axi4_awlock   ,
            output  var axi4_cache_t    m_axi4_awcache  ,
            output  var axi4_prot_t     m_axi4_awprot   ,
            output  var axi4_qos_t      m_axi4_awqos    ,
            output  var axi4_region_t   m_axi4_awregion ,
            output  var logic           m_axi4_awvalid  ,
            input   var logic           m_axi4_awready  ,
            output  var axi4_data_t     m_axi4_wdata    ,
            output  var axi4_strb_t     m_axi4_wstrb    ,
            output  var logic           m_axi4_wlast    ,
            output  var logic           m_axi4_wvalid   ,
            input   var logic           m_axi4_wready   ,
            input   var axi4_id_t       m_axi4_bid      ,
            input   var axi4_resp_t     m_axi4_bresp    ,
            input   var logic           m_axi4_bvalid   ,
            output  var logic           m_axi4_bready   ,
            output  var axi4_id_t       m_axi4_arid     ,
            output  var axi4_addr_t     m_axi4_araddr   ,
            output  var axi4_len_t      m_axi4_arlen    ,
            output  var axi4_size_t     m_axi4_arsize   ,
            output  var axi4_burst_t    m_axi4_arburst  ,
            output  var axi4_lock_t     m_axi4_arlock   ,
            output  var axi4_cache_t    m_axi4_arcache  ,
            output  var axi4_prot_t     m_axi4_arprot   ,
            output  var axi4_qos_t      m_axi4_arqos    ,
            output  var axi4_region_t   m_axi4_arregion ,
            output  var logic           m_axi4_arvalid  ,
            input   var logic           m_axi4_arready  ,
            input   var axi4_id_t       m_axi4_rid      ,
            input   var axi4_data_t     m_axi4_rdata    ,
            input   var axi4_resp_t     m_axi4_rresp    ,
            input   var logic           m_axi4_rlast    ,
            input   var logic           m_axi4_rvalid   ,
            output  var logic           m_axi4_rready   
        );
    
    
    // ----------------------------------------------------------------
    //  Stage-0
    // ----------------------------------------------------------------

    localparam int  ST0_LATENCY = 1;
    
    logic   [0:0]   st0_first;
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY        (ST0_LATENCY    ),
                .DATA_BITS      (1              ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_op_nop_st0_first
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         (s_first        ),
                .s_clear        (1'b0           ),
                .s_valid        (1'b1           ),

                .m_data         (st0_first      )
            );
    
    logic   [0:0]   st0_last;
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY        (ST0_LATENCY    ),
                .DATA_BITS      (1              ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_op_nop_st0_last
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         (s_last         ),
                .s_clear        (1'b0           ),
                .s_valid        (1'b1           ),

                .m_data         (st0_last       )
            );
    
    logic   [1:0]   st0_data;
    elixirchip_es1_spu_op_add
            #(
                .LATENCY        (ST0_LATENCY    ),
                .DATA_BITS      (2              ),
                .DEVICE         (DEVICE         ),
                .IMMEDIATE_CARRY(1'b1           ),
                .IMMEDIATE_DATA0(1'b0           ),
                .IMMEDIATE_DATA1(1'b1           ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_op_add_st0
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_carry        (1'b0           ),
                .s_data0        (s_data0        ),
                .s_data1        (2'd1           ),
                .s_clear        (1'b0           ),
                .s_valid        (1'b1           ),

                .m_carry        (               ),
                .m_msb_c        (               ),
                .m_data         (st0_data       )
            );
    
    logic   st0_valid;
    elixirchip_es1_spu_ctl_valid
            #(
                .LATENCY        (ST0_LATENCY    ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_ctl_valid_st0
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_valid        (s_valid        ),

                .m_valid        (st0_valid      )
            );
    
    
    // ----------------------------------------------------------------
    //  Stage-1
    // ----------------------------------------------------------------

    localparam int  ST1_LATENCY = 2;
    
    logic   [0:0]   st1_first;
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY        (ST1_LATENCY    ),
                .DATA_BITS      (1              ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_op_nop_st1_first
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         (st0_first      ),
                .s_clear        (1'b0           ),
                .s_valid        (1'b1           ),

                .m_data         (st1_first      )
            );
    
    logic   [0:0]   st1_last;
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY        (ST1_LATENCY    ),
                .DATA_BITS      (1              ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_op_nop_st1_last
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         (st0_last       ),
                .s_clear        (1'b0           ),
                .s_valid        (1'b1           ),

                .m_data         (st1_last       )
            );
    
    logic   [1:0]   st1_data;
    elixirchip_es1_spu_op_sub
            #(
                .LATENCY        (ST1_LATENCY    ),
                .DATA_BITS      (2              ),
                .DEVICE         (DEVICE         ),
                .IMMEDIATE_CARRY(1'b1           ),
                .IMMEDIATE_DATA0(1'b0           ),
                .IMMEDIATE_DATA1(1'b1           ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_op_add_st1
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_carry        (1'b1           ),
                .s_data0        (st0_data       ),
                .s_data1        (2'd1           ),
                .s_clear        (1'b0           ),
                .s_valid        (1'b1           ),

                .m_carry        (               ),
                .m_msb_c        (               ),
                .m_data         (st1_data       )
            );
    
    logic   st1_valid;
    elixirchip_es1_spu_ctl_valid
            #(
                .LATENCY        (ST1_LATENCY    ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )     
            )
        u_ctl_valid_st1
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_valid        (st0_valid      ),

                .m_valid        (st1_valid      )
            );
    
    
    // ----------------------------------------------------------------
    //  Output
    // ----------------------------------------------------------------
            
    assign  m_first  = st1_first    ;
    assign  m_last   = st1_last     ;
    assign  m_index0 = '0           ;
    assign  m_data0  = st1_data     ;
    assign  m_strb0  = '1           ;
    assign  m_index1 = '0           ;
    assign  m_data1  = '0           ;
    assign  m_strb1  = '0           ;
    assign  m_valid  = st1_valid    ;
     
    
    // ----------------------------------------------------------------
    //  AXI4 manager
    // ----------------------------------------------------------------

    assign  m_axi4_awid     = '0;
    assign  m_axi4_awaddr   = '0;
    assign  m_axi4_awlen    = '0;
    assign  m_axi4_awsize   = '0;
    assign  m_axi4_awburst  = '0;
    assign  m_axi4_awlock   = '0;
    assign  m_axi4_awcache  = '0;
    assign  m_axi4_awprot   = '0;
    assign  m_axi4_awqos    = '0;
    assign  m_axi4_awregion = '0;
    assign  m_axi4_awvalid  = '0;
    assign  m_axi4_wdata    = '0;
    assign  m_axi4_wstrb    = '0;
    assign  m_axi4_wlast    = '0;
    assign  m_axi4_wvalid   = '0;
    assign  m_axi4_bready   = '0;
    assign  m_axi4_arid     = '0;
    assign  m_axi4_araddr   = '0;
    assign  m_axi4_arlen    = '0;
    assign  m_axi4_arsize   = '0;
    assign  m_axi4_arburst  = '0;
    assign  m_axi4_arlock   = '0;
    assign  m_axi4_arcache  = '0;
    assign  m_axi4_arprot   = '0;
    assign  m_axi4_arqos    = '0;
    assign  m_axi4_arregion = '0;
    assign  m_axi4_arvalid  = '0;
    assign  m_axi4_rready   = '0;

endmodule


`default_nettype wire

