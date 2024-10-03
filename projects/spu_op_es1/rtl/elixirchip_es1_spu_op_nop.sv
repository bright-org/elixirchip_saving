
`timescale 1ns / 1ps
`default_nettype none

module elixirchip_es1_spu_op_nop
        #(
            parameter   int     LATENCY     = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS   = 8                      ,   // データ幅指定
            parameter   type    data_t      = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA  = 'x                     ,   // クリア値
            parameter   bit     USE_CLEAR   = 1'b0                   ,   // s_clear 信号を使う場合に1にする
            parameter   bit     USE_VALID   = 1'b0                   ,   // s_valid 信号を使う場合に1にする
            parameter           DEVICE      = "RTL"                  ,   // デバイス名
            parameter           SIMULATION  = "false"                ,   // シミュレーション
            parameter           DEBUG       = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var data_t          s_data  ,   // 入力データ
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            output  var data_t          m_data      // 出力データ
        );

    // LATENCY が負の値なら合成時エラーにする
    initial begin
        assert ( LATENCY >= 0 ) else begin $error("Illegal Latency"); end
    end

    // パイプライン遅延
    data_t  stage_data  [0:LATENCY];
    logic   stage_clear [0:LATENCY];
    logic   stage_valid [0:LATENCY];

    assign stage_data [0] = s_data  ;
    assign stage_clear[0] = s_clear ;
    assign stage_valid[0] = s_valid ;

    for ( genvar i = 1; i <= LATENCY; i++ ) begin : stage
        if ( i < LATENCY ) begin : sr
            always_ff @( posedge clk ) begin
                if ( reset ) begin
                    stage_valid[i] <= 1'bx;
                end
                else if ( cke ) begin
                    stage_valid[i] <= stage_valid[i-1];
                end
            end
            always_ff @( posedge clk ) begin
                if ( cke ) begin
                    stage_clear[i] <= stage_clear[i-1];
                    stage_data [i] <= stage_data [i-1];
                end
            end
        end
        else begin : ff
            if ( string'(DEVICE) == "SPARTAN6"
                    || string'(DEVICE) == "VIRTEX6"
                    || string'(DEVICE) == "7SERIES"
                    || string'(DEVICE) == "ULTRASCALE"
                    || string'(DEVICE) == "ULTRASCALE_PLUS"
                    || string'(DEVICE) == "ULTRASCALE_PLUS_ES1"
                    || string'(DEVICE) == "ULTRASCALE_PLUS_ES2") begin : xilinx
                elixirchip_es1_xilinx_flipflops
                        #(
                            .BYPASS         (1'b0                   ),
                            .DATA_BITS      (DATA_BITS              ),
                            .data_t         (data_t                 ),
                            .RESET_VALUE    (CLEAR_DATA             ),
                            .DEVICE         (DEVICE                 ),
                            .SIMULATION     (SIMULATION             ),
                            .DEBUG          (DEBUG                  )
                        )
                    u_elixirchip_es1_xilinx_flipflops
                        (
                            .reset          (cke && stage_clear[i-1]),
                            .clk            ,
                            .cke            (cke && stage_valid[i-1]),
                            
                            .din            (stage_data[i-1]        ),
                            .dout           (stage_data[i]          )
                        );
            end
            else begin : rtl
                always_ff @( posedge clk ) begin
                    if ( cke ) begin
                        if ( stage_clear[i-1] ) begin
                            stage_data [i] <= CLEAR_DATA;
                        end
                        else if ( stage_valid[i-1] ) begin
                            stage_data [i] <= stage_data [i-1];
                        end
                    end
                end
            end
        end
    end

    assign m_data = stage_data[LATENCY];

endmodule

`default_nettype wire

