
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_acc
        #(
            parameter   int         LATENCY        = 1                          ,   // レイテンシ指定
            parameter   int         S_DATA_BITS    = 8                          ,   // s_data0 幅指定
            parameter   type        s_data_t       = logic    [S_DATA_BITS-1:0] ,   // s_data0 型指定(オプション)
            parameter   int         M_DATA_BITS    = 8                          ,   // m_data 幅指定
            parameter   type        m_data_t       = logic    [M_DATA_BITS-1:0] ,   // m_data 型指定(オプション)
            parameter   m_data_t    CLEAR_DATA     = '0                         ,   // m_data クリア値
            parameter   logic       CLEAR_CARRY    = '0                         ,   // m_carryクリア値
            parameter   bit         IMMEDIATE_DATA = 1'b0                       ,   // s_data0 が即値の場合に1にする(オプション)
            parameter               DEVICE         = "RTL"                      ,   // デバイス名
            parameter               SIMULATION     = "false"                    ,   // シミュレーション
            parameter               DEBUG          = "false"                        // デバッグ
        )
        (
            input   var logic           reset       ,   // 同期リセット(制論理)
            input   var logic           clk         ,   // クロック
            input   var logic           cke         ,   // クロックイネーブル

            input   var logic           s_sub       ,   // 1の時にアキュミュレータの演算を加算ではなく減算にする
            input   var logic           s_carry     ,   // キャリー入力 (sub 時は 0 でボローあり)
            input   var s_data_t        s_data      ,   // 入力データ
            input   var logic           s_clear     ,   // クリア
            input   var logic           s_valid     ,   // 1の時有効データ

            output  var logic           m_carry     ,   // キャリー
            output  var m_data_t        m_data          // 出力データ
        );

    // stage 0
    logic       st0_carry   ;
    m_data_t    st0_data    ;

    if ( $bits(m_data_t) > 3 
          && ( string'(DEVICE) == "SPARTAN6"
            || string'(DEVICE) == "VIRTEX6"
            || string'(DEVICE) == "7SERIES"
            || string'(DEVICE) == "ULTRASCALE"
            || string'(DEVICE) == "ULTRASCALE_PLUS"
            || string'(DEVICE) == "ULTRASCALE_PLUS_ES1"
            || string'(DEVICE) == "ULTRASCALE_PLUS_ES2")) begin : xilinx

        logic     carry8_cin  ;
        m_data_t  carry8_sin  ;
        m_data_t  carry8_din  ;
        m_data_t  carry8_dout ;
        m_data_t  carry8_cout ;
        elixirchip_es1_xilinx_carry8
                #(
                    .DATA_BITS  ($bits(m_data_t)),
                    .data_t     (m_data_t       ),
                    .DEVICE     (DEVICE         ),
                    .SIMULATION (SIMULATION     ),
                    .DEBUG      (DEBUG          )
                )
            u_elixirchip_es1_xilinx_carry8
                (
                    .cin        (carry8_cin     ),
                    .sin        (carry8_sin     ),
                    .din        (carry8_din     ),
                    .dout       (carry8_dout    ),
                    .cout       (carry8_cout    )
                );
        assign carry8_cin = s_carry;
        assign carry8_din = st0_data;
        always_comb begin
            case ( s_sub )
            1'b0: carry8_sin = st0_data ^  m_data_t'(s_data);
            1'b1: carry8_sin = st0_data ^ ~m_data_t'(s_data);
            endcase
        end
        always_ff @( posedge clk ) begin
            if ( reset || s_clear ) begin
                st0_carry <= CLEAR_CARRY    ;
                st0_data  <= CLEAR_DATA     ;
            end
            else if ( cke ) begin
                if ( s_valid ) begin
                    st0_carry <= carry8_cout[$bits(m_data_t) - 1];
                    st0_data  <= carry8_dout;
                end
            end
        end
    end
    else begin : rtl
        always_ff @( posedge clk ) begin
            if ( reset || s_clear ) begin
                st0_carry <= CLEAR_CARRY    ;
                st0_data  <= CLEAR_DATA     ;
            end
            else if ( cke ) begin
                if ( s_valid ) begin
                    if ( s_sub ) begin
                        {st0_carry, st0_data} <= {1'b0, st0_data} + {1'b0, ~m_data_t'(s_data)} + m_data_t'(s_carry);
                    end
                    else begin
                        {st0_carry, st0_data} <= {1'b0, st0_data} + {1'b0,  m_data_t'(s_data)} + m_data_t'(s_carry);
                    end
                end
            end
        end
    end

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY - 1                ),
                .DATA_BITS  ($bits({m_carry, m_data})   ),
                .DEVICE     (DEVICE                     ),
                .SIMULATION (SIMULATION                 ),
                .DEBUG      (DEBUG                      )
            )
        u_additional_latency
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     ({st0_carry, st0_data}      ),
                .s_clear    (1'b0                       ),
                .s_valid    (1'b1                       ),

                .m_data     ({m_carry,   m_data  }      )
            );

endmodule


`default_nettype wire

