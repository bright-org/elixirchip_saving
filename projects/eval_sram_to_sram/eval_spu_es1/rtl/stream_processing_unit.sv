`timescale 1ns / 1ps
`default_nettype none


// ストリームプロセッシングユニットのサンプル
module stream_processing_unit
        #(
            parameter int  DATA_BITS  = 64          ,   // データ幅
            parameter      DEVICE     = "RTL"       ,   // デバイス名
            parameter      SIMULATION = "false"     ,   // シミュレーション
            parameter      DEBUG      = "false"         // デバッグ
        )
        (
            // system
            input   var logic                       reset   ,   // リセット
            input   var logic                       clk     ,   // クロック
            input   var logic                       cke     ,   // クロックイネーブル

            // input port
            input   var logic   [DATA_BITS-1:0]     s_data0 ,   // source0
            input   var logic   [DATA_BITS-1:0]     s_data1 ,   // source1
            input   var logic                       s_valid ,   // データ有効

            // output port
            output  var logic   [DATA_BITS-1:0]     m_data0 ,   // destination0
            output  var logic   [DATA_BITS-1:0]     m_data1 ,   // destination1
            output  var logic                       m_valid     // データ有効
        );

    
    // 演算エレメントの単位定義 (ここでは INT8 とする)
    localparam  int     ELEMENT_BITS  = 8;
    localparam  type    element_t     = logic signed [ELEMENT_BITS-1:0];

    // 演算エレメントの並列/直列数
    localparam  int     PARALLEL_LEN = DATA_BITS / ELEMENT_BITS;    // 並列数
    localparam  int     SERIAL_LEN   = 256;                         // 直列数


    // 各ステージの信号を直並列に並べる
    element_t   [PARALLEL_LEN-1:0]  stage_s_data0   [SERIAL_LEN-1:0];
    element_t   [PARALLEL_LEN-1:0]  stage_s_data1   [SERIAL_LEN-1:0];
    logic                           stage_s_valid   [SERIAL_LEN-1:0];
    element_t   [PARALLEL_LEN-1:0]  stage_m_data0   [SERIAL_LEN-1:0];
    element_t   [PARALLEL_LEN-1:0]  stage_m_data1   [SERIAL_LEN-1:0];
    logic                           stage_m_valid   [SERIAL_LEN-1:0];

    // ステージ0 の入力に SPU の input を接続
    assign stage_s_data0[0] = s_data0;
    assign stage_s_data1[0] = s_data1;
    assign stage_s_valid[0] = s_valid;

    // 前のステージの出力を次のステージの入力に接続
    for ( genvar i = 1; i < SERIAL_LEN; i++ ) begin : stage_loop
        assign stage_s_data0[i] = stage_m_data0[i-1];
        assign stage_s_data1[i] = stage_m_data1[i-1];
        assign stage_s_valid[i] = stage_m_valid[i-1];
    end

    // 演算パイプラインを構築
    for ( genvar i = 0; i < SERIAL_LEN; i++ ) begin : serial_loop
        for ( genvar j = 0; j < PARALLEL_LEN; j++ ) begin : parallel_loop

            localparam LATENCY = 3;  // 8bit 乗算を行う為 3 とする

            /*
            // 乗算
            elixirchip_es1_spu_op_mul
                    #(
                        .LATENCY            (LATENCY            ),
                        .S_DATA0_BITS       (ELEMENT_BITS       ),
                        .S_DATA1_BITS       (ELEMENT_BITS       ),
                        .M_DATA_BITS        (ELEMENT_BITS       ),
                        .DATA_SHIFT         (0                  ),
                        .CLEAR_DATA         ('x                 ),
                        .IMMEDIATE_DATA0    (1'b0               ),
                        .IMMEDIATE_DATA1    (1'b0               ),
                        .DEVICE             (DEVICE             ),
                        .SIMULATION         (SIMULATION         ),
                        .DEBUG              (DEBUG              )
                    )
                u_elixirchip_es1_spu_op_mul
                    (
                        .reset              ,
                        .clk                ,
                        .cke                ,

                        .s_data0            (stage_s_data0[i][j]),
                        .s_data1            (stage_s_data1[i][j]),
                        .s_clear            (1'b0               ),
                        .s_valid            (1'b1               ),
                        
                        .m_data             (stage_m_data0[i][j]) 
                    );
            */
        mul_s8s8s8
            u_mul_s8s8s8
                (
                    .reset      ,
                    .clk        ,
//                  .cke        ,

                    .s_data0    (stage_s_data0[i][j]),
                    .s_data1    (stage_s_data1[i][j]),
                    .m_data     (stage_m_data0[i][j])
                );


            /*
            // 別途生成した3段パイプラインの INT8 乗算
            mul_s8s8_lo8_p3
                u_mul_s8s8_lo8_p3
                    (
                        .CLK    (clk                    ),
                        .CE     (cke                    ),
                        .A      (stage_s_data0[i][j]    ),
                        .B      (stage_s_data1[i][j]    ),
                        .P      (stage_m_data0[i][j]    )
                    );
            */

            // 加算
            elixirchip_es1_spu_op_add
                    #(
                        .LATENCY            (LATENCY            ),
                        .DATA_BITS          (ELEMENT_BITS       ),
                        .CLEAR_DATA         ('x                 ),
                        .CLEAR_CARRY        ('x                 ),
                        .CLEAR_MSB_C        ('x                 ),
                        .IMMEDIATE_CARRY    (1'b1               ),
                        .IMMEDIATE_DATA0    (1'b0               ),
                        .IMMEDIATE_DATA1    (1'b0               ),
                        .DEVICE             ("RTL"              ),
                        .SIMULATION         ("false"            ),
                        .DEBUG              ("false"            )
                    )
                u_elixirchip_es1_spu_op_add
                    (
                        .reset              ,
                        .clk                ,
                        .cke                ,

                        .s_carry            (1'b0               ), 
                        .s_data0            (stage_s_data0[i][j]),
                        .s_data1            (stage_s_data1[i][j]),
                        .s_clear            (1'b0               ), 
                        .s_valid            (1'b1               ), 

                        .m_data             (stage_m_data1[i][j]),
                        .m_carry            (                   ),
                        .m_msb_c            (                   ) 
                    );

            // valid 信号の伝搬
            elixirchip_es1_spu_ctl_valid
                    #(
                        .LATENCY            (LATENCY            ),
                        .DEVICE             (DEVICE             ),
                        .SIMULATION         (SIMULATION         ),
                        .DEBUG              (DEBUG              )
                    )
                u_elixirchip_es1_spu_ctl_valid
                    (
                        .reset              ,
                        .clk                ,
                        .cke                ,

                        .s_valid            (stage_s_valid[i]   ),

                        .m_valid            (stage_m_valid[i]   )
                    );
        end
    end

    // ステージ0 の出力を SPU の output に接続
    assign m_data0 = stage_m_data0[SERIAL_LEN-1];
    assign m_data1 = stage_m_data1[SERIAL_LEN-1];
    assign m_valid = stage_m_valid[SERIAL_LEN-1];

endmodule


`default_nettype wire

