`timescale 1ns / 1ps
`default_nettype none


// Ether Interface
module ether_if
        #(
            parameter   int     DATA_BITS  = 2                      ,
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,
            parameter           DEVICE     = "ULTRASCALE_PLUS"      ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input  var logic            reset           ,
            input  var logic            clk             ,

            input  var logic            s_tx_last       ,
            input  var data_t           s_tx_data       ,
            input  var logic            s_tx_valid      ,
            output var logic            s_tx_ready      ,

            output var logic            m_rx_last       ,
            output var data_t           m_rx_data       ,
            output var logic            m_rx_valid      ,


            input  var logic            rgmii_tx_reset  ,
            input  var logic            rgmii_tx_clk    ,
            output var logic            rgmii_tx_ctrl   ,
            output var logic    [3:0]   rgmii_tx_d      ,

            input  var logic            rgmii_rx_reset  ,
            input  var logic            rgmii_rx_clk    ,
            input  var logic            rgmii_rx_ctrl   ,
            input  var logic    [3:0]   rgmii_rx_d     
        );

    // ---------------------------------------------------------
    //  RGMII Interface
    // ---------------------------------------------------------

    logic           ether_tx_reset  ;
    logic           ether_tx_clk    ;
    logic           ether_tx_last   ;
    logic   [7:0]   ether_tx_data   ;
    logic           ether_tx_valid  ;
    logic           ether_tx_ready  ;
    assign ether_tx_reset = rgmii_tx_reset;
    assign ether_tx_clk   = rgmii_tx_clk;

    logic           ether_rx_reset  ;
    logic           ether_rx_clk    ;
    logic           ether_rx_last   ;
    logic   [7:0]   ether_rx_data   ;
    logic           ether_rx_valid  ;
    assign ether_rx_reset = rgmii_rx_reset;
    assign ether_rx_clk   = rgmii_rx_clk;

    rgmii_if
            #(
                .DEVICE         (DEVICE                             ),
                .SIMULATION     (SIMULATION                         ),
                .DEBUG          (DEBUG                              )
            )
        u_rgmii_if
            (
                .tx_reset       (ether_tx_reset                     ),
                .tx_clk         (ether_tx_clk                       ),
                .s_tx_error     (ether_tx_valid & ether_tx_ready    ),
                .s_tx_data      (ether_tx_valid & ether_tx_ready ? ether_tx_data : '0),
                .s_tx_valid     (ether_tx_valid & ether_tx_ready    ),

                .rx_reset       (ether_rx_reset                     ),
                .rx_clk         (ether_rx_clk                       ),
                .m_rx_error     (                                   ),
                .m_rx_last      (ether_rx_last                      ),
                .m_rx_data      (ether_rx_data                      ),
                .m_rx_valid     (ether_rx_valid                     ),

                .rgmii_tx_ctrl  (rgmii_tx_ctrl                      ),
                .rgmii_tx_d     (rgmii_tx_d                         ),
                .rgmii_rx_ctrl  (rgmii_rx_ctrl                      ),
                .rgmii_rx_d     (rgmii_rx_d                         )
            );


    // ---------------------------------------------------------
    //  TX
    // ---------------------------------------------------------

    // width convert
    logic           core_tx_last    ;
    logic   [7:0]   core_tx_data    ;
    logic           core_tx_valid   ;
    logic           core_tx_ready   ;

    if ( $bits(data_t) != 8 ) begin :tx_cnv
        jelly2_stream_width_convert
                #(
                    .UNIT_WIDTH     ($bits(data_t)  ),
                    .S_NUM          (1              ),
                    .M_NUM          (8/$bits(data_t)),
                    .HAS_FIRST      (0              ),
                    .HAS_LAST       (1              ),
                    .HAS_STRB       (0              ),
                    .HAS_KEEP       (0              ),
                    .S_REGS         (1              ),
                    .M_REGS         (1              )
                )
            u_stream_width_convert_tx
                (
                    .reset,
                    .clk,
                    .cke            (1'b1           ),
                    
                    .endian         (1'b0           ),
                    .padding        ('0             ),
                    
                    .s_align_s      ('0             ),
                    .s_align_m      ('0             ),
                    .s_first        ('0             ),
                    .s_last         (s_tx_last      ), 
                    .s_data         (s_tx_data      ),
                    .s_strb         ('0             ),
                    .s_keep         ('0             ),
                    .s_user_f       ('0             ),
                    .s_user_l       ('0             ),
                    .s_valid        (s_tx_valid     ),
                    .s_ready        (s_tx_ready     ),
                    
                    .m_first        (               ),
                    .m_last         (core_tx_last   ),
                    .m_data         (core_tx_data   ),
                    .m_strb         (               ),
                    .m_keep         (               ),
                    .m_user_f       (               ),
                    .m_user_l       (               ),
                    .m_valid        (core_tx_valid  ),
                    .m_ready        (core_tx_ready  )
                );
    end
    else begin : tx_bypass
        assign core_tx_last  = s_tx_last;
        assign core_tx_data  = s_tx_data;
        assign core_tx_valid = s_tx_valid;
        assign s_tx_ready  = core_tx_ready;
    end


    // Convert to ether_tx_colck
    jelly2_fifo_async_fwtf
            #(
                .DATA_WIDTH     (9              ),
                .PTR_WIDTH      (5              ),
                .DOUT_REGS      (0              ),
                .RAM_TYPE       ("distributed"  ),
                .S_REGS         (0              ),
                .M_REGS         (1              )
            )
        u_fifo_async_fwtf_tx
            (
                .s_reset        (reset          ),
                .s_clk          (clk            ),
                .s_cke          (1'b1           ),
                .s_data         ({
                                    core_tx_last,
                                    core_tx_data
                                }),
                .s_valid        (core_tx_valid  ),
                .s_ready        (core_tx_ready  ),
                .s_free_count   (),
                
                .m_reset        (ether_tx_reset ),
                .m_clk          (ether_tx_clk   ),
                .m_cke          (1'b1           ),
                .m_data         ({
                                    ether_tx_last,
                                    ether_tx_data
                                }),
                .m_valid        (ether_tx_valid ),
                .m_ready        (ether_tx_ready ),
                .m_data_count   (               )
            );
    
    // クロック差吸収の為に溜める
    logic   [1:0]   ether_tx_count;
    always_ff @(posedge ether_tx_clk) begin
        if ( ether_tx_reset ) begin
            ether_tx_count <= '0;
            ether_tx_ready <= 1'b0;
        end
        else begin
            if ( ether_tx_last && ether_tx_valid && ether_tx_ready ) begin
                ether_tx_ready <= 1'b0;
                ether_tx_count <= '0;
            end
            else begin
                ether_tx_count <= ether_tx_count + ether_tx_valid;
                if ( ether_tx_count >= 2'd2 ) begin
                    ether_tx_ready <= 1'b1;
                end
            end
        end
    end


    // ---------------------------------------------------------
    //  RX
    // ---------------------------------------------------------

    // Convert to core colck
    (* mark_debug = DEBUG *)    logic           core_rx_last    ;
    (* mark_debug = DEBUG *)    logic   [7:0]   core_rx_data    ;
    (* mark_debug = DEBUG *)    logic           core_rx_valid   ;
    (* mark_debug = DEBUG *)    logic           core_rx_ready   ;
    jelly2_fifo_async_fwtf
            #(
                .DATA_WIDTH     (9              ),
                .PTR_WIDTH      (5              ),
                .DOUT_REGS      (0              ),
                .RAM_TYPE       ("distributed"  ),
                .S_REGS         (0              ),
                .M_REGS         (1              )
            )
        u_fifo_async_fwtf_rx
            (
                .s_reset        (ether_rx_reset ),
                .s_clk          (ether_rx_clk  ),
                .s_cke          (1'b1           ),
                .s_data         ({
                                    ether_rx_last,
                                    ether_rx_data
                                }),
                .s_valid        (ether_rx_valid ),
                .s_ready        (               ),
                .s_free_count   (),
                
                .m_reset        (reset          ),
                .m_clk          (clk            ),
                .m_cke          (1'b1           ),
                .m_data         ({
                                    core_rx_last,
                                    core_rx_data
                                }),
                .m_valid        (core_rx_valid  ),
                .m_ready        (core_rx_ready  ),
                .m_data_count   (               )
            );

    if ( $bits(data_t) != 8 ) begin :rx_cnv
        // width convert
        jelly2_stream_width_convert
                #(
                    .UNIT_WIDTH     ($bits(data_t)  ),
                    .S_NUM          (8/$bits(data_t)),
                    .M_NUM          (1              ),
                    .HAS_FIRST      (0              ),
                    .HAS_LAST       (1              ),
                    .HAS_STRB       (0              ),
                    .HAS_KEEP       (0              ),
                    .S_REGS         (1              ),
                    .M_REGS         (1              )
                )
            u_stream_width_convert_rx
                (
                    .reset,
                    .clk,
                    .cke            (1'b1           ),
                    
                    .endian         (1'b0           ),
                    .padding        ('0             ),
                    
                    .s_align_s      ('0             ),
                    .s_align_m      ('0             ),
                    .s_first        ('0             ),
                    .s_last         (core_rx_last   ), 
                    .s_data         (core_rx_data   ),
                    .s_strb         ('0             ),
                    .s_keep         ('0             ),
                    .s_user_f       ('0             ),
                    .s_user_l       ('0             ),
                    .s_valid        (core_rx_valid  ),
                    .s_ready        (core_rx_ready  ),
                    
                    .m_first        (               ),
                    .m_last         (m_rx_last      ),
                    .m_data         (m_rx_data      ),
                    .m_strb         (               ),
                    .m_keep         (               ),
                    .m_user_f       (               ),
                    .m_user_l       (               ),
                    .m_valid        (m_rx_valid     ),
                    .m_ready        (1'b1           )
                );
    end
    else begin : rx_bypass
        assign m_rx_last  = core_rx_last;
        assign m_rx_data  = core_rx_data;
        assign m_rx_valid = core_rx_valid;
        assign core_rx_ready  = 1'b1;
    end
    
endmodule


`default_nettype wire

