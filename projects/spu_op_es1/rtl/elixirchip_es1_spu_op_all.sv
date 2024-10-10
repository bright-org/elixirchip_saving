
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_all
        #(
            parameter   int     LATENCY    = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 36                     ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   logic   CLEAR_DATA = 'x                     ,   // m_data クリア値
            parameter   bit     USE_CLEAR  = 1'b0                   ,   // s_clear 信号を使う場合に1にする
            parameter   bit     USE_VALID  = 1'b0                   ,   // s_valid 信号を使う場合に1にする
            parameter           DEVICE     = "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var data_t          s_data  ,   // 入力データ
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var logic           m_data      // 出力データ
        );
    
    // パラメータチェック
    localparam LATENCY1 = LATENCY > 0 ? LATENCY : 1;
    initial begin
        assert ( LATENCY >= 0               ) else begin $error("Illegal Latency"); end
        assert ( (DATA_BITS <= 6 ** LATENCY1)
              || (DATA_BITS <= 6*8 * LATENCY1) ) else begin $warning("Not recommended latency"); end
    end

    if ( LATENCY > 0 && DATA_BITS < 6 ** LATENCY ) begin : cascade
        // カスケード演算
        data_t  stage_data  [LATENCY:0];
        logic   stage_clear [LATENCY:0];
        logic   stage_valid [LATENCY:0];
        assign stage_data [0] = s_data;
        assign stage_clear[0] = s_clear;
        assign stage_valid[0] = s_valid;
        always_ff @( posedge clk ) begin
            if ( cke ) begin
                for ( int stage = 1; stage <= LATENCY; stage++ ) begin
                    automatic data_t tmp;
                    tmp = '1;
                    for ( int i = 0; i < $bits(data_t); i++ ) begin
                        tmp[i / 6] = tmp[i / 6] & stage_data[stage-1][i];
                    end
                    if ( stage == LATENCY ) begin
                        if ( stage_clear[stage-1] ) begin
                            stage_data[stage] <= {$bits(data_t){CLEAR_DATA}};
                        end
                        else if ( stage_valid[stage-1] ) begin
                            stage_data[stage] <= tmp;
                        end
                    end
                    else begin
                        stage_data[stage] <= tmp;
                    end
                    stage_clear[stage] <= stage_clear[stage-1];
                    stage_valid[stage] <= stage_valid[stage-1];
                end
            end
        end
        assign m_data = stage_data[LATENCY][0];
    end
    else begin : simple
        // 演算
        logic  st0_data;
        logic  st0_clear;
        logic  st0_valid;

        if ( DATA_BITS > 6
            && (string'(DEVICE) == "ULTRASCALE"
                || string'(DEVICE) == "ULTRASCALE_PLUS"
                || string'(DEVICE) == "ULTRASCALE_PLUS_ES1"
                || string'(DEVICE) == "ULTRASCALE_PLUS_ES2")  ) begin : carry8

            localparam  int     CARRY_BITS = (DATA_BITS + 5) / 6;
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
                carry_sin = '1;
                carry_din = '0;
                for ( int i = 0; i < $bits(s_data); i++ ) begin
                    if ( !s_data[i] ) begin
                        carry_sin[i / 6] = 1'b0;
                    end
                end
            end
            assign st0_data = carry_cout[CARRY_BITS-1];
        end
        else begin : rtl
            // 演算
            assign st0_data = &s_data;
        end

        assign st0_clear = s_clear;
        assign st0_valid = s_valid;

        // パイプライン遅延追加
        elixirchip_es1_spu_op_nop
                #(
                    .LATENCY    (LATENCY    ),
                    .DATA_BITS  (1          ),
                    .CLEAR_DATA (CLEAR_DATA ),
                    .DEVICE     (DEVICE     ),
                    .SIMULATION (SIMULATION ),
                    .DEBUG      (DEBUG      )
                )
            u_additional_latency
                (
                    .reset      ,
                    .clk        ,
                    .cke        ,

                    .s_data     (st0_data   ),
                    .s_clear    (st0_clear  ),
                    .s_valid    (st0_valid  ),

                    .m_data     (m_data     )
                );
    end

endmodule


`default_nettype wire

