
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_sub
        #(
            parameter   int     LATENCY         = 1                     ,   // レイテンシ指定
            parameter   int     DATA_BITS       = 8                     ,   // データ幅指定
            parameter   type    data_t          = logic [DATA_BITS-1:0] ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA      = 'x                    ,   // m_data クリア値
            parameter   logic   CLEAR_CARRY     = 'x                    ,   // m_carryクリア値
            parameter   logic   CLEAR_MSB_C     = 'x                    ,   // m_msb_c クリア値
            parameter   bit     IMMEDIATE_CARRY = 1'b1                  ,   // s_carry が即値の場合に1にする
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                  ,   // s_data0 が即値の場合に1にする
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                  ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE          = "RTL"                 ,   // デバイス名
            parameter           SIMULATION      = "false"               ,   // シミュレーション
            parameter           DEBUG           = "false"                   // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var logic           s_carry ,   // キャリー入力
            input   var data_t          s_data0 ,   // 入力データ0
            input   var data_t          s_data1 ,   // 入力データ1
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var data_t          m_data  ,   // 出力データ
            output  var logic           m_carry ,   // キャリー出力
            output  var logic           m_msb_c     // 最上位ビットのキャリー出力
        );

    // パラメータチェック
    localparam  int     LATENCY1 = LATENCY > 0 ? LATENCY : 1;
    initial begin
        assert ( LATENCY >= 0 ) else begin $error("Illegal Latency"); end
        assert ( DATA_BITS <= 8 * (2 ** LATENCY1) ) else begin $warning("Not recommended latency"); end
    end

    // パラメータ
    localparam  int     CALC_BITS = 1 + $bits(data_t);
    localparam  type    calc_t    = logic [CALC_BITS-1:0];

    // 演算
    data_t  st0_data    ;
    logic   st0_msb_c   ;
    logic   st0_carry   ;
    logic   st0_clear   ;
    logic   st0_valid   ;

    if ( $bits(data_t) > 4 
          && ( string'(DEVICE) == "SPARTAN6"
            || string'(DEVICE) == "VIRTEX6"
            || string'(DEVICE) == "7SERIES"
            || string'(DEVICE) == "ULTRASCALE"
            || string'(DEVICE) == "ULTRASCALE_PLUS"
            || string'(DEVICE) == "ULTRASCALE_PLUS_ES1"
            || string'(DEVICE) == "ULTRASCALE_PLUS_ES2")) begin : xilinx

        logic   carry8_cin  ;
        data_t  carry8_sin  ;
        data_t  carry8_din  ;
        data_t  carry8_dout ;
        data_t  carry8_cout ;
        elixirchip_es1_xilinx_carry8
                #(
                    .DATA_BITS  ($bits(data_t)  ),
                    .data_t     (data_t         ),
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
        assign carry8_din = s_data0;
        assign carry8_sin = s_data0 ^ ~s_data1;
        assign st0_data   = carry8_dout;
        assign st0_carry  = carry8_cout[$bits(data_t) - 1];
        assign st0_msb_c  = carry8_cout[$bits(data_t) - 2];
    end
    else begin : rtl
        data_t  s_data1_n   ;
        assign s_data1_n = ~s_data1;    // bit反転

        if ( DATA_BITS > 1 ) begin : multibit
            assign {st0_msb_c, st0_data[$bits(st0_data)-2:0]} = {1'b0, s_data0[$bits(s_data0)-2:0]} + {1'b0, s_data1_n[$bits(s_data1_n)-2:0]} + data_t'(s_carry);
            assign {st0_carry, st0_data[$bits(st0_data)-1]}   = s_data0[$bits(s_data0)-1] + s_data1_n[$bits(s_data1_n)-1] + st0_msb_c;
        end
        else begin : onebit_adder
            assign st0_msb_c = s_carry;
            assign {st0_carry, st0_data} = calc_t'(s_data0) + calc_t'(s_data1_n) + calc_t'(s_carry);
        end
    end
    assign st0_clear = s_clear;
    assign st0_valid = s_valid;

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY        ),
                .DATA_BITS  ($bits(m_data)  ),
                .CLEAR_DATA (CLEAR_DATA     ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          )
            )
        u_additional_latency_data
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (st0_data       ),
                .s_clear    (st0_clear      ),
                .s_valid    (st0_valid      ),

                .m_data     (m_data         )
            );

    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY        ),
                .DATA_BITS  ($bits(m_msb_c) ),
                .CLEAR_DATA (CLEAR_MSB_C    ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          )
            )
        u_additional_latency_msb_c
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (st0_msb_c      ),
                .s_clear    (st0_clear      ),
                .s_valid    (st0_valid      ),

                .m_data     (m_msb_c        )
            );

    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY        ),
                .DATA_BITS  ($bits(m_carry) ),
                .CLEAR_DATA (CLEAR_CARRY    ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          )
            )
        u_additional_latency_carry
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (st0_carry      ),
                .s_clear    (st0_clear      ),
                .s_valid    (st0_valid      ),

                .m_data     (m_carry        )
            );


endmodule


`default_nettype wire

