
`timescale 1ns / 1ps
`default_nettype none


// ボード依存のトップネット(KR260用)
module eval_ether_bridge_kr260
        #(
//          parameter   MODE       = "test_pattern"     ,
            parameter   MODE       = "bridge"           ,
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

    if ( MODE == "test_pattern" ) begin : pattern
        logic   [11:0]   ether0_cycle;
        always_ff @(posedge core_clk) begin
            if ( core_reset ) begin
                ether0_cycle <= 0;
            end
            else begin
                ether0_cycle <= ether0_cycle + 1;
            end
        end

        logic           reg_last;
        logic   [1:0]   reg_data;
        logic           reg_valid;
        always_ff @(posedge core_clk) begin
            if ( core_reset ) begin
                reg_last  <= '0;
                reg_data  <= '0;
                reg_valid <= '0;
            end
            else begin
                reg_last  <= ether0_cycle[10:0] == '1;
                reg_valid <= ether0_cycle[11];
                reg_data  <= ether0_cycle[10:0] <= 30 ? 2'b01 :
                             ether0_cycle[10:0] == 31 ? 2'b11 :
                             ether0_cycle[3:2];
            end
        end

        assign ether0_tx_last  = reg_last   ;
        assign ether0_tx_data  = reg_data   ;
        assign ether0_tx_valid = reg_valid  ;

        assign ether1_tx_last  = ether1_rx_last;
        assign ether1_tx_data  = ether1_rx_data;
        assign ether1_tx_valid = ether1_rx_valid;

        (* mark_debug = "true" *)   logic       dbg_core_rx0_last;
        (* mark_debug = "true" *)   logic [1:0] dbg_core_rx0_data;
        (* mark_debug = "true" *)   logic       dbg_core_rx0_valid;
        (* mark_debug = "true" *)   logic       dbg_core_rx1_last;
        (* mark_debug = "true" *)   logic [1:0] dbg_core_rx1_data;
        (* mark_debug = "true" *)   logic       dbg_core_rx1_valid;
        always_ff @(posedge core_clk) begin
            dbg_core_rx0_last  <= ether0_rx_last;
            dbg_core_rx0_data  <= ether0_rx_data;
            dbg_core_rx0_valid <= ether0_rx_valid;
            dbg_core_rx1_last  <= ether1_rx_last;
            dbg_core_rx1_data  <= ether1_rx_data;
            dbg_core_rx1_valid <= ether1_rx_valid;
        end
    end
    else begin : bridge
        always_ff @(posedge core_clk) begin
            ether0_tx_last  <= ether1_rx_last;
            ether0_tx_data  <= ether1_rx_data;
            ether0_tx_valid <= ether1_rx_valid;
        end

        always_ff @(posedge core_clk) begin
            ether1_tx_last  <= ether0_rx_last;
            ether1_tx_data  <= ether0_rx_data;
            ether1_tx_valid <= ether0_rx_valid;
        end

        (* mark_debug = "true" *)   logic       dbg_core_rx0_last;
        (* mark_debug = "true" *)   data_t      dbg_core_rx0_data;
        (* mark_debug = "true" *)   logic       dbg_core_rx0_valid;
        (* mark_debug = "true" *)   logic       dbg_core_rx1_last;
        (* mark_debug = "true" *)   data_t      dbg_core_rx1_data;
        (* mark_debug = "true" *)   logic       dbg_core_rx1_valid;
        always_ff @(posedge core_clk) begin
            dbg_core_rx0_last  <= ether0_rx_last;
            dbg_core_rx0_data  <= ether0_rx_data;
            dbg_core_rx0_valid <= ether0_rx_valid;
            dbg_core_rx1_last  <= ether1_rx_last;
            dbg_core_rx1_data  <= ether1_rx_data;
            dbg_core_rx1_valid <= ether1_rx_valid;
        end
    end

    // SPU的信号観測
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

                                logic   spu_clk;
    (* mark_debug = "true" *)   logic   spu_first;
    (* mark_debug = "true" *)   logic   spu_last;
    (* mark_debug = "true" *)   data_t  spu_data;
    (* mark_debug = "true" *)   logic   spu_valid;
    assign spu_clk    = core_clk;
    assign spu_first  = spu_valid ? ether0_rx_first : '0;
    assign spu_last   = spu_valid ? ether0_rx_last  : '0;
    assign spu_data   = spu_valid ? ether0_rx_data  : '0;
    assign spu_valid  = ether0_rx_valid;



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

