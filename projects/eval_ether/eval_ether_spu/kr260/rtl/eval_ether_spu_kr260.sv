
`timescale 1ns / 1ps
`default_nettype none


module eval_ether_spu_kr260
        #(
            parameter   DEVICE     = "ULTRASCALE_PLUS"  ,   // デバイス名
            parameter   SIMULATION = "false"            ,   // シミュレーション
            parameter   DEBUG      = "true"                 // デバッグ
        )
        (
            output  var logic           fan_en         ,

            // clock
            input  var logic            in_clk25a       ,
            input  var logic            in_clk25b       ,

            // LED
            output var logic    [1:0]   led             ,

            // Ether0
            output var logic            rgmii0_reset_n  ,
            output var logic            rgmii0_mdc      ,
            inout  tri logic            rgmii0_mdio     ,
            output var logic            rgmii0_gtx_clk  ,
            output var logic            rgmii0_tx_ctrl  ,
            output var logic    [3:0]   rgmii0_tx_d     ,
            input  var logic            rgmii0_rx_clk   ,
            input  var logic            rgmii0_rx_ctrl  ,
            input  var logic    [3:0]   rgmii0_rx_d     ,
            input  var logic    [2:0]   rgmii0_led      ,

            // Ether1
            output var logic            rgmii1_reset_n  ,
            output var logic            rgmii1_mdc      ,
            inout  tri logic            rgmii1_mdio     ,
            output var logic            rgmii1_gtx_clk  ,
            output var logic            rgmii1_tx_ctrl  ,
            output var logic    [3:0]   rgmii1_tx_d     ,
            input  var logic            rgmii1_rx_clk   ,
            input  var logic            rgmii1_rx_ctrl  ,
            input  var logic    [3:0]   rgmii1_rx_d     ,
            input  var logic    [2:0]   rgmii1_led      
        );

    // リセット
    var logic           in_reset;
    var logic   [7:0]   reset_counter = '1;
    always_ff @(posedge in_clk25a ) begin
        if ( reset_counter > 0 ) begin
            reset_counter <= reset_counter - 1'b1;
            in_reset      <= 1'b1;
        end
        else begin
            in_reset      <= 1'b0;
        end
    end


    logic   ether_reset     ;
    logic   ether_clk       ;

    logic   core_reset      ;
    logic   core_clk        ;

    logic   ref_reset       ;
    logic   ref_clk         ;

    design_1
        u_design_1
            (
                .fan_en         ,

                .in_reset       (in_reset   ),
                .in_clk25       (in_clk25b  ),

                .ether_reset    (ether_reset),
                .ether_clk      (ether_clk  ),

                .core_reset     (core_reset ),
                .core_clk       (core_clk   )
            );


    // ------------------------------
    //  Giga-Ether
    // ------------------------------

    localparam  int     DATA_BITS  = 2                      ;
    localparam  type    data_t     = logic [DATA_BITS-1:0]  ;

    //  Ether0
    logic   rgmii0_tx_reset ;
    logic   rgmii0_tx_clk   ;
    assign rgmii0_tx_reset = ether_reset;
    assign rgmii0_tx_clk   = ether_clk;

    logic   rgmii0_rx_reset ;
    jelly_reset u_reset_ether0_rx
        (
            .clk        (rgmii0_rx_clk  ),
            .in_reset   (in_reset       ),
            .out_reset  (rgmii0_rx_reset)
        );
    
    assign rgmii0_reset_n = ~ether_reset;
    assign rgmii0_mdc     = 1'b0;
    assign rgmii0_mdio    = 1'bz;
    ODDRE1
            #(
                .IS_C_INVERTED  (1'b0           ),
                .IS_D1_INVERTED (1'b0           ),
                .IS_D2_INVERTED (1'b0           ),
                .SIM_DEVICE     (DEVICE         ),
                .SRVAL          (1'b0           )
            )
        u_oddre1_tx_rgmii0_tx_clk
            (
                .Q              (rgmii0_gtx_clk ),
                .C              (rgmii0_tx_clk  ),
                .D1             (1'b1           ),
                .D2             (1'b0           ),
                .SR             (1'b0           )
            );

    logic           ether0_tx_last  ;
    data_t          ether0_tx_data  ;
    logic           ether0_tx_valid ;
    logic           ether0_rx_last  ;
    data_t          ether0_rx_data  ;
    logic           ether0_rx_valid ;
    ether_if
            #(
                .DATA_BITS          (DATA_BITS          ),
                .DEVICE             (DEVICE             ),
                .SIMULATION         (SIMULATION         ),
                .DEBUG              (DEBUG              )
            )
        u_ether_if_0
            (
                .reset              (core_reset         ),
                .clk                (core_clk           ),
                .s_tx_last          (ether0_tx_last     ),
                .s_tx_data          (ether0_tx_data     ),
                .s_tx_valid         (ether0_tx_valid    ),
                .s_tx_ready         (                   ),
                .m_rx_last          (ether0_rx_last     ),
                .m_rx_data          (ether0_rx_data     ),
                .m_rx_valid         (ether0_rx_valid    ),

                .rgmii_tx_reset     (rgmii0_tx_reset    ),
                .rgmii_tx_clk       (rgmii0_tx_clk      ),
                .rgmii_tx_ctrl      (rgmii0_tx_ctrl     ),
                .rgmii_tx_d         (rgmii0_tx_d        ),
                .rgmii_rx_reset     (rgmii0_rx_reset    ),
                .rgmii_rx_clk       (rgmii0_rx_clk      ),
                .rgmii_rx_ctrl      (rgmii0_rx_ctrl     ),
                .rgmii_rx_d         (rgmii0_rx_d        )
            );


    //  Ether1
    logic   rgmii1_tx_reset ;
    logic   rgmii1_tx_clk   ;
    assign rgmii1_tx_reset = ether_reset;
    assign rgmii1_tx_clk   = ether_clk;

    logic   rgmii1_rx_reset ;
    jelly_reset u_reset_ether1_rx
        (
            .clk        (rgmii1_rx_clk  ),
            .in_reset   (in_reset       ),
            .out_reset  (rgmii1_rx_reset)
        );
    
    assign rgmii1_reset_n = ~ether_reset;
    assign rgmii1_mdc     = 1'b0;
    assign rgmii1_mdio    = 1'bz;
    ODDRE1
            #(
                .IS_C_INVERTED  (1'b0           ),
                .IS_D1_INVERTED (1'b0           ),
                .IS_D2_INVERTED (1'b0           ),
                .SIM_DEVICE     (DEVICE         ),
                .SRVAL          (1'b0           )
            )
        u_oddre1_tx_rgmii1_tx_clk
            (
                .Q              (rgmii1_gtx_clk ),
                .C              (rgmii1_tx_clk  ),
                .D1             (1'b1           ),
                .D2             (1'b0           ),
                .SR             (1'b0           )
            );
    
    logic           ether1_tx_last  ;
    data_t          ether1_tx_data  ;
    logic           ether1_tx_valid ;
    logic           ether1_rx_last  ;
    data_t          ether1_rx_data  ;
    logic           ether1_rx_valid ;
    ether_if
            #(
                .DATA_BITS          (DATA_BITS          ),
                .DEVICE             (DEVICE             ),
                .SIMULATION         (SIMULATION         ),
                .DEBUG              (DEBUG              )
            )
        u_ether_if_1
            (
                .reset              (core_reset         ),
                .clk                (core_clk           ),
                .s_tx_last          (ether1_tx_last     ),
                .s_tx_data          (ether1_tx_data     ),
                .s_tx_valid         (ether1_tx_valid    ),
                .s_tx_ready         (                   ),
                .m_rx_last          (ether1_rx_last     ),
                .m_rx_data          (ether1_rx_data     ),
                .m_rx_valid         (ether1_rx_valid    ),

                .rgmii_tx_reset     (rgmii1_tx_reset    ),
                .rgmii_tx_clk       (rgmii1_tx_clk      ),
                .rgmii_tx_ctrl      (rgmii1_tx_ctrl     ),
                .rgmii_tx_d         (rgmii1_tx_d        ),
                .rgmii_rx_reset     (rgmii1_rx_reset    ),
                .rgmii_rx_clk       (rgmii1_rx_clk      ),
                .rgmii_rx_ctrl      (rgmii1_rx_ctrl     ),
                .rgmii_rx_d         (rgmii1_rx_d        )
            );
    
    
    // ------------------------------
    //  connection
    // ------------------------------

    // first生成
    logic   ether0_rx_first;
    always_ff @(posedge core_clk) begin
        if ( core_reset ) begin
            ether0_rx_first <= 1'b1;
        end
        else begin
            if ( ether0_rx_valid ) begin
                ether0_rx_first <= ether0_rx_last;
            end
        end
    end

    // ストリームプロセッシングユニット
    localparam  int     INDEX_BITS = 10                     ;   // 添え字幅
    localparam  type    index_t    = logic [INDEX_BITS-1:0] ;
    localparam  int     STRB_BITS  = (DATA_BITS + 7) / 8    ;   // ストローブ幅
    localparam  type    strb_t     = logic [STRB_BITS-1:0]  ;

    logic       spu_first   ;   // パケット先頭
    logic       spu_last    ;   // パケット末尾
    index_t     spu_index0  ;   // 配列の添え字0
    data_t      spu_data0   ;   // source0
    strb_t      spu_strb0   ;   // storobe0
    index_t     spu_index1  ;   // 配列の添え字1
    data_t      spu_data1   ;   // source1
    strb_t      spu_strb1   ;   // storobe1
    logic       spu_valid   ;   // データ有効
    always_ff @(posedge core_clk) begin
        if ( core_reset ) begin
            spu_first   <= '0;
            spu_last    <= '0;
            spu_index0  <= 'x;
            spu_data0   <= 'x;
            spu_strb0   <= 'x;
            spu_index1  <= 'x;
            spu_data1   <= 'x;
            spu_strb1   <= 'x;
            spu_valid   <= 1'b0;
        end
        else begin
            if ( ether0_rx_first ) begin
                spu_index0 <= '0;
                spu_index1 <= '0;
            end
            else if ( spu_valid ) begin
                spu_index0 <= spu_index0 + 1'b1;
                spu_index1 <= spu_index1 + 1'b1;
                if ( spu_last ) begin
                    spu_index0 <= 'x;
                    spu_index1 <= 'x;
                end
            end
            spu_first   <= ether0_rx_valid & ether0_rx_first;
            spu_last    <= ether0_rx_valid & ether0_rx_last;
            spu_data0   <= ether0_rx_data;
            spu_strb0   <= '1;
            spu_data1   <= '0;
            spu_strb1   <= '0;
            spu_valid   <= ether0_rx_valid;
        end
    end

    // AXI4 manager port
    localparam  int     AXI4_ID_BITS     = 6                                ;
    localparam  int     AXI4_ADDR_BITS   = 10                               ;
    localparam  int     AXI4_DATA_BITS   = 128                              ;
    localparam  int     AXI4_STRB_BITS   = AXI4_DATA_BITS / 8               ;
    localparam  int     AXI4_LEN_BITS    = 8                                ;
    localparam  int     AXI4_SIZE_BITS   = 3                                ;
    localparam  int     AXI4_BURST_BITS  = 2                                ;
    localparam  int     AXI4_LOCK_BITS   = 1                                ;
    localparam  int     AXI4_CACHE_BITS  = 4                                ;
    localparam  int     AXI4_PROT_BITS   = 3                                ;
    localparam  int     AXI4_QOS_BITS    = 4                                ;
    localparam  int     AXI4_REGION_BITS = 4                                ;
    localparam  int     AXI4_RESP_BITS   = 2                                ;
    localparam  type    axi4_id_t        = logic   [AXI4_ID_BITS    -1:0]   ;
    localparam  type    axi4_addr_t      = logic   [AXI4_ADDR_BITS  -1:0]   ;
    localparam  type    axi4_len_t       = logic   [AXI4_LEN_BITS   -1:0]   ;
    localparam  type    axi4_size_t      = logic   [AXI4_SIZE_BITS  -1:0]   ;
    localparam  type    axi4_burst_t     = logic   [AXI4_BURST_BITS -1:0]   ;
    localparam  type    axi4_lock_t      = logic   [AXI4_LOCK_BITS  -1:0]   ;
    localparam  type    axi4_cache_t     = logic   [AXI4_CACHE_BITS -1:0]   ;
    localparam  type    axi4_prot_t      = logic   [AXI4_PROT_BITS  -1:0]   ;
    localparam  type    axi4_qos_t       = logic   [AXI4_QOS_BITS   -1:0]   ;
    localparam  type    axi4_region_t    = logic   [AXI4_REGION_BITS-1:0]   ;
    localparam  type    axi4_data_t      = logic   [AXI4_DATA_BITS  -1:0]   ;
    localparam  type    axi4_strb_t      = logic   [AXI4_STRB_BITS  -1:0]   ;
    localparam  type    axi4_resp_t      = logic   [AXI4_RESP_BITS  -1:0]   ;
    axi4_id_t       m_axi4_awid     ;
    axi4_addr_t     m_axi4_awaddr   ;
    axi4_len_t      m_axi4_awlen    ;
    axi4_size_t     m_axi4_awsize   ;
    axi4_burst_t    m_axi4_awburst  ;
    axi4_lock_t     m_axi4_awlock   ;
    axi4_cache_t    m_axi4_awcache  ;
    axi4_prot_t     m_axi4_awprot   ;
    axi4_qos_t      m_axi4_awqos    ;
    axi4_region_t   m_axi4_awregion ;
    logic           m_axi4_awvalid  ;
    logic           m_axi4_awready  ;
    axi4_data_t     m_axi4_wdata    ;
    axi4_strb_t     m_axi4_wstrb    ;
    logic           m_axi4_wlast    ;
    logic           m_axi4_wvalid   ;
    logic           m_axi4_wready   ;
    axi4_id_t       m_axi4_bid      ;
    axi4_resp_t     m_axi4_bresp    ;
    logic           m_axi4_bvalid   ;
    logic           m_axi4_bready   ;
    axi4_id_t       m_axi4_arid     ;
    axi4_addr_t     m_axi4_araddr   ;
    axi4_len_t      m_axi4_arlen    ;
    axi4_size_t     m_axi4_arsize   ;
    axi4_burst_t    m_axi4_arburst  ;
    axi4_lock_t     m_axi4_arlock   ;
    axi4_cache_t    m_axi4_arcache  ;
    axi4_prot_t     m_axi4_arprot   ;
    axi4_qos_t      m_axi4_arqos    ;
    axi4_region_t   m_axi4_arregion ;
    logic           m_axi4_arvalid  ;
    logic           m_axi4_arready  ;
    axi4_id_t       m_axi4_rid      ;
    axi4_data_t     m_axi4_rdata    ;
    axi4_resp_t     m_axi4_rresp    ;
    logic           m_axi4_rlast    ;
    logic           m_axi4_rvalid   ;
    logic           m_axi4_rready   ;

    stream_processing_unit
            #(
                .INDEX_BITS     (INDEX_BITS     ),
                .index_t        (index_t        ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         ),
                .STRB_BITS      (STRB_BITS      ),
                .strb_t         (strb_t         ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_stream_processing_unit
            (
                .reset          (core_reset     ),
                .clk            (core_clk       ),
                .cke            (1'b1           ),

                .s_first        (spu_first      ),
                .s_last         (spu_last       ),
                .s_index0       (spu_index0     ),
                .s_data0        (spu_data0      ),
                .s_strb0        (spu_strb0      ),
                .s_index1       (spu_index1     ),
                .s_data1        (spu_data1      ),
                .s_strb1        (spu_strb1      ),
                .s_valid        (spu_valid      ),

                .m_first        (               ),
                .m_last         (ether0_tx_last ),
                .m_index0       (               ),
                .m_data0        (ether0_tx_data ),
                .m_strb0        (               ),
                .m_index1       (               ),
                .m_data1        (               ),
                .m_strb1        (               ),
                .m_valid        (ether0_tx_valid) 
            );

    // ether1
    always_ff @(posedge core_clk) begin
        ether1_tx_last  <= ether1_rx_last;
        ether1_tx_data  <= ether1_rx_data;
        ether1_tx_valid <= ether1_rx_valid;
    end


    // ------------------------------
    //  LED
    // ------------------------------

    // 受信クロックの確認
    logic [24:0] rgmii0_rx_clk_counter;
    always_ff @( posedge rgmii0_rx_clk ) begin
        if ( rgmii0_rx_reset ) begin
            rgmii0_rx_clk_counter <= '0;
        end
        else begin
            rgmii0_rx_clk_counter <= rgmii0_rx_clk_counter + 1'b1;
        end
    end

    logic [24:0] rgmii1_rx_clk_counter;
    always_ff @( posedge rgmii1_rx_clk ) begin
        if ( rgmii1_rx_reset ) begin
            rgmii1_rx_clk_counter <= '0;
        end
        else begin
            rgmii1_rx_clk_counter <= rgmii1_rx_clk_counter + 1'b1;
        end
    end

    assign led[0] = rgmii0_rx_clk_counter[24];
    assign led[1] = rgmii1_rx_clk_counter[24];

endmodule


`default_nettype wire

