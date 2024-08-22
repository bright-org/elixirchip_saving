
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_match
        #(
            parameter   int     LATENCY         = 1                             ,   // レイテンシ指定
            parameter   int     DATA_BITS       = 8                             ,   // データ幅指定
            parameter   type    data_t          = logic signed [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   logic   CLEAR_DATA      = 'x                            ,   // m_data クリア値
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                          ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                          ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE          = "RTL"                         ,   // デバイス名
            parameter           SIMULATION      = "false"                       ,   // シミュレーション
            parameter           DEBUG           = "false"                           // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var data_t          s_data0 ,   // 入力データ0
            input   var data_t          s_data1 ,   // 入力データ1
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var logic           m_data      // 出力データ(一致したら1)
        );

    logic  st0_data;
    logic  st0_clear;
    logic  st0_valid;

    if ( $bits(data_t) > 3 && $bits(data_t) <= 24*4
           && !IMMEDIATE_DATA0 && !IMMEDIATE_DATA1
           && (string'(DEVICE) == "ULTRASCALE"
            || string'(DEVICE) == "ULTRASCALE_PLUS"
            || string'(DEVICE) == "ULTRASCALE_PLUS_ES1"
            || string'(DEVICE) == "ULTRASCALE_PLUS_ES2")  ) begin : carry8

        localparam  int     CARRY_BITS = (DATA_BITS + 3) / 3;
        localparam  type    carry_t    = logic [CARRY_BITS-1:0];

        // CARRY8
        logic           carry_cin;
        carry_t         carry_sin;
        carry_t         carry_din;
        carry_t         carry_dout;
        carry_t         carry_cout;
        elixirchip_es1_xilinx_carry8
                #(
                    .DATA_BITS      ($bits(carry_t) ),
                    .data_t         (carry_t        ),
                    .DEVICE         (DEVICE         ),
                    .SIMULATION     (SIMULATION     ),
                    .DEBUG          (DEBUG          )
                )
            u_elixirchip_es1_xilinx_carry8
                (
                    .cin            (carry_cin      ),
                    .sin            (carry_sin      ),
                    .din            (carry_din      ),
                    .dout           (carry_dout     ),
                    .cout           (carry_cout     )
                );

        always_comb begin
            carry_cin = 1'b1;
            carry_sin  = '1;
            carry_din = '0;
            for ( int i = 0; i < $bits(data_t); i++ ) begin
                if ( s_data0[i] != s_data1[i] ) begin
                    carry_sin[i/3] = 1'b0;
                end
            end
        end
        assign st0_data = carry_cout[CARRY_BITS-1];
    end
    else begin : rtl
        // 演算
        assign st0_data = (s_data0 == s_data1);
    end
    assign st0_clear = s_clear;
    assign st0_valid = s_valid;

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY            ),
                .DATA_BITS  ($bits(m_data)      ),
                .CLEAR_DATA (CLEAR_DATA         ),
                .DEVICE     (DEVICE             ),
                .SIMULATION (SIMULATION         ),
                .DEBUG      (DEBUG              )
            )
        u_additional_latency
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_data     (st0_data           ),
                .s_clear    (st0_clear          ),
                .s_valid    (st0_valid          ),

                .m_data     (m_data             )
            );

endmodule


`default_nettype wire

