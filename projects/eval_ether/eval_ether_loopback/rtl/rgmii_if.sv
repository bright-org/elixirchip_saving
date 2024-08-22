`timescale 1ns / 1ps
`default_nettype none

module rgmii_if
        #(
            parameter           DEVICE     = "ULTRASCALE_PLUS"  ,   // デバイス名
            parameter           SIMULATION = "false"            ,   // シミュレーション
            parameter           DEBUG      = "false"                // デバッグ
        )
        (
            input  var logic            tx_reset        ,
            input  var logic            tx_clk          ,
            input  var logic            s_tx_error      ,
            input  var logic    [7:0]   s_tx_data       ,
            input  var logic            s_tx_valid      ,

            input  var logic            rx_reset        ,
            input  var logic            rx_clk          ,
            output var logic            m_rx_error      ,
            output var logic            m_rx_last       ,
            output var logic    [7:0]   m_rx_data       ,
            output var logic            m_rx_valid      ,

            output var logic            rgmii_tx_ctrl   ,
            output var logic    [3:0]   rgmii_tx_d      ,
            input  var logic            rgmii_rx_ctrl   ,
            input  var logic    [3:0]   rgmii_rx_d     
        );

    // tx
    localparam  TX_IS_C_INVERTED = 1'b0;
    ODDRE1
            #(
                .IS_C_INVERTED  (TX_IS_C_INVERTED   ),
                .IS_D1_INVERTED (1'b0               ),
                .IS_D2_INVERTED (1'b0               ),
                .SIM_DEVICE     (DEVICE             ),
                .SRVAL          (1'b0               )
            )
        u_oddre1_tx_d 
            (
                .Q              (rgmii_tx_ctrl      ),
                .C              (tx_clk             ),
                .D1             (s_tx_valid         ),
                .D2             (s_tx_error         ),
                .SR             (tx_reset           )
            );    
    for ( genvar i = 0; i < 4; i++ ) begin : tx_oddre1
        ODDRE1
                #(
                    .IS_C_INVERTED  (TX_IS_C_INVERTED   ),
                    .IS_D1_INVERTED (1'b0               ),
                    .IS_D2_INVERTED (1'b0               ),
                    .SIM_DEVICE     (DEVICE             ),
                    .SRVAL          (1'b0               )
                )
            u_oddre1_tx_d 
                (
                    .Q              (rgmii_tx_d[i]      ),
                    .C              (tx_clk             ),
                    .D1             (s_tx_data[i+0]     ),
                    .D2             (s_tx_data[i+4]     ),
                    .SR             (tx_reset           )
                );
    end


    // RX
    logic   [1:0]     rx_ctl;
    logic   [7:0]     rx_d  ;
    localparam RX_DDR_CLK_EDGE = "SAME_EDGE_PIPELINED";
//  localparam RX_DDR_CLK_EDGE   = "SAME_EDGE";
    localparam RX_IS_CB_INVERTED = 1'b1;
    localparam RX_IS_C_INVERTED  = 1'b0;
    IDDRE1
            #(
                .DDR_CLK_EDGE   (RX_DDR_CLK_EDGE    ),
                .IS_CB_INVERTED (RX_IS_CB_INVERTED  ),
                .IS_C_INVERTED  (RX_IS_C_INVERTED   ) 
            )
        u_iddre1_rx_ctl
            (
                .Q1             (rx_ctl[0]          ),
                .Q2             (rx_ctl[1]          ),
                .C              (rx_clk             ),  
                .CB             (rx_clk             ),
                .D              (rgmii_rx_ctrl      ),  
                .R              (rx_reset           )   
            );
    
    for ( genvar i = 0; i < 4; i++ ) begin : rx_iddre1
        IDDRE1
                #(
                    .DDR_CLK_EDGE   (RX_DDR_CLK_EDGE    ),
                    .IS_CB_INVERTED (RX_IS_CB_INVERTED  ),
                    .IS_C_INVERTED  (RX_IS_C_INVERTED   ) 
                )
            u_iddre1_rx_d
                (
                    .Q1             (rx_d[i+0]          ),
                    .Q2             (rx_d[i+4]          ),
                    .C              (rx_clk             ),  
                    .CB             (rx_clk             ),
                    .D              (rgmii_rx_d[i]      ),  
                    .R              (rx_reset           )   
                );
    end
    
    always_ff @(posedge rx_clk) begin
        if ( rx_reset ) begin
            m_rx_error <= 1'b0;
            m_rx_data  <= '0;
            m_rx_valid <= 1'b0;
        end
        else begin
            m_rx_error <= rx_ctl[1];
            m_rx_data  <= rx_d;
            m_rx_valid <= rx_ctl[0];
        end
    end
    assign m_rx_last = ~rx_ctl[0];

    // debug
    if ( DEBUG == "true" ) begin : debug
        (* mark_debug = DEBUG *)    logic   [1:0]     dbg_tx_ctl;
        (* mark_debug = DEBUG *)    logic   [7:0]     dbg_tx_d  ;
        always_ff @(posedge tx_clk) begin
            dbg_tx_ctl <= {s_tx_error, s_tx_valid};
            dbg_tx_d   <= s_tx_data;
        end

        (* mark_debug = DEBUG *)    logic   [1:0]     dbg_rx_ctl;
        (* mark_debug = DEBUG *)    logic   [7:0]     dbg_rx_d  ;
        always_ff @(posedge rx_clk) begin
            dbg_rx_ctl <= rx_ctl ;
            dbg_rx_d   <= rx_d   ;
        end
    end

endmodule


`default_nettype wire

