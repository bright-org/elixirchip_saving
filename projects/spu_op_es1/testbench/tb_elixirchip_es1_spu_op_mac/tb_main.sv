

`timescale 1ns / 1ps
`default_nettype none


// 以降は Verilator で C++ のテストドライバも使えるように時間待ちを書かない
module tb_main
        (
            input   var logic                       reset   ,
            input   var logic                       clk     
        );


    int     cycle;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            cycle <= 0;
        end
        else begin
            cycle <= cycle + 1;
            if ( cycle >= 3000 ) begin
                // シミュレーション終了
                automatic int fp = $fopen("simulation_completed.log", "w");
                $fclose(fp);
                $display("Simulation Completed");
                $finish(0);
            end
        end
    end


`ifdef __VERILATOR__
    localparam  DEVICE     = "RTL"              ;   // デバイス名
`else
    localparam  DEVICE     = "ULTRASCALE_PLUS"  ;   // デバイス名
`endif
    localparam  SIMULATION = "true"             ;   // シミュレーション
    localparam  DEBUG      = "false"            ;   // デバッグ


    // -----------------------------------------
    //  SVAを使った parameter別検証
    // -----------------------------------------
    
    for ( genvar LATENCY = 3; LATENCY <= 4; LATENCY++ ) begin : latency
        for ( genvar S_DATA0_BITS = 32; S_DATA0_BITS <= 64; S_DATA0_BITS *= 2 ) begin : data0_bits
            for ( genvar S_DATA1_BITS = 8; S_DATA1_BITS <= 32; S_DATA1_BITS *= 2 ) begin : data1_bits
                for ( genvar M_DATA_BITS = 8; M_DATA_BITS <= 64; M_DATA_BITS *= 2 ) begin : m_data_bits
                    tb_elixirchip_es1_spu_op_mac
                            #(
                                .LATENCY        (LATENCY                    ),
                                .S_DATA0_BITS   (S_DATA0_BITS               ),
                                .S_DATA1_BITS   (S_DATA1_BITS               ),
                                .M_DATA_BITS    (M_DATA_BITS                ),
                                .DEVICE         (DEVICE                     ),
                                .SIMULATION     (SIMULATION                 ),
                                .DEBUG          (DEBUG                      )
                            )
                        u_tb_elixirchip_es1_spu_op_mac
                            (
                                .reset          ,
                                .clk            
                            );
                end
            end
        end
    end

    // SVA bind (verilator でも使えるようにモジュール名でバインド)
    bind elixirchip_es1_spu_op_mac sva_elixirchip_es1_spu_op_mac
            #(
                .LATENCY        (LATENCY        ),
                .S_DATA0_BITS   (S_DATA0_BITS   ),
                .S_DATA1_BITS   (S_DATA1_BITS   ),
                .M_DATA_BITS    (M_DATA_BITS    ),
                .IMMEDIATE_DATA0     (IMMEDIATE_DATA0     ),
                .IMMEDIATE_DATA1     (IMMEDIATE_DATA1     ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_sva
            (
                .*
            );
    

    // -----------------------------------------
    //  typical な個別検証
    // -----------------------------------------

    localparam  int     LATENCY      = 3                                ;   // レイテンシ指定
    localparam  int     S_DATA0_BITS = 8                                ;   // s_data0 幅指定
    localparam  type    s_data0_t    = logic signed [S_DATA0_BITS-1:0]  ;   // s_data0 型指定(オプション)
    localparam  int     S_DATA1_BITS = 9                                ;   // s_data1 幅指定
    localparam  type    s_data1_t    = logic signed [S_DATA1_BITS-1:0]  ;   // s_data1 型指定(オプション)
    localparam  int     M_DATA_BITS  = 10                               ;   // m_data 幅指定
    localparam  type    m_data_t     = logic signed [M_DATA_BITS-1:0]   ;   // m_data 型指定(オプション)
    localparam  bit     IMMEDIATE_DATA0 = 1'b0                               ;   // s_data0 が即値の場合に1にする(オプション)
    localparam  bit     IMMEDIATE_DATA1 = 1'b0                               ;   // s_data1 が即値の場合に1にする

    typedef struct {
        logic       cke     ;   // クロックイネーブル
        logic       s_set   ;   // 1の時にアキュミュレータは積算せずに新しい値をセット
        logic       s_sub   ;   // 1の時にアキュミュレータの演算を加算ではなく減算にする
        s_data0_t   s_data0 ;   // 入力データ0
        s_data1_t   s_data1 ;   // 入力データ1
        logic       s_valid ;   // 1の時有効データ
    } input_signals_t;

    typedef struct {
        m_data_t    m_data  ;   // 出力データ
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_set: 1'b1, s_sub: 1'b0, s_data0: s_data0_t'( 2), s_data1: s_data1_t'( 3), s_valid: 1'b1},    //  0: 2 * 3 = 6 (set)
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b0, s_data0: s_data0_t'( 3), s_data1: s_data1_t'( 4), s_valid: 1'b1},    //  1: 6 + 3 * 4 = 18
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b1, s_data0: s_data0_t'( 1), s_data1: s_data1_t'( 2), s_valid: 1'b1},    //  2: 18 - 1 * 2 = 16
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b0, s_data0: s_data0_t'( 0), s_data1: s_data1_t'( 3), s_valid: 1'b1},    //  3: 16 + 0 * 3 = 16
        '{cke: 1'b1, s_set: 1'b1, s_sub: 1'b0, s_data0: s_data0_t'( 3), s_data1: s_data1_t'( 3), s_valid: 1'b1},    //  4: 3 * 3 = 9 (set)
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b0, s_data0: s_data0_t'( 2), s_data1: s_data1_t'( 2), s_valid: 1'b1},    //  5: 9 + 2 * 2 = 13
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b0, s_data0: s_data0_t'(-2), s_data1: s_data1_t'( 3), s_valid: 1'b1},    //  6: 13 + (-2) * 3 = 7
        '{cke: 1'b0, s_set: 1'b0, s_sub: 1'b0, s_data0: s_data0_t'( 4), s_data1: s_data1_t'(-2), s_valid: 1'b1},    //  cke = 0
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b0, s_data0: s_data0_t'( 4), s_data1: s_data1_t'(-2), s_valid: 1'b1},    //  7: 7 + 4 * (-2) = -1
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b0, s_data0: s_data0_t'(99), s_data1: s_data1_t'(88), s_valid: 1'b0},    //  8: keep :  -1
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b1, s_data0: s_data0_t'( 4), s_data1: s_data1_t'( 2), s_valid: 1'b1},    //  9: -1 - 4 * 2 = -9
        '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b1, s_data0: s_data0_t'(-9), s_data1: s_data1_t'( 3), s_valid: 1'b1}     // 10: -9 - (-9) * 3 = 18
    };
    
    output_signals_t expected_table [] = '{
        '{m_data: m_data_t'(   6)},  // 0
        '{m_data: m_data_t'(  18)},  // 1
        '{m_data: m_data_t'(  16)},  // 2
        '{m_data: m_data_t'(  16)},  // 3
        '{m_data: m_data_t'(   9)},  // 4
        '{m_data: m_data_t'(  13)},  // 5
        '{m_data: m_data_t'(   7)},  // 6
        '{m_data: m_data_t'(  -1)},  // 7
        '{m_data: m_data_t'(  -1)},  // 8
        '{m_data: m_data_t'(  -9)},  // 9
        '{m_data: m_data_t'(  18)}   // 10
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_set: 1'b0, s_sub: 1'b0, s_data0: '0, s_data1: '0, s_valid: 1'b0};
    output_signals_t    out_sig;

    elixirchip_es1_spu_op_mac
            #(
                .LATENCY        (LATENCY        ),
                .S_DATA0_BITS   (S_DATA0_BITS   ),
                .s_data0_t      (s_data0_t      ),
                .S_DATA1_BITS   (S_DATA1_BITS   ),
                .s_data1_t      (s_data1_t      ),
                .M_DATA_BITS    (M_DATA_BITS    ),
                .m_data_t       (m_data_t       ),
                .IMMEDIATE_DATA0     (1'b0           ),
                .IMMEDIATE_DATA1     (1'b0           ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          ) 
            )
        u_elixirchip_es1_spu_op_mac
            (
                .reset          ,
                .clk            ,
                .cke            (in_sig.cke      ),

                .s_set          (in_sig.s_set    ),
                .s_sub          (in_sig.s_sub    ),
                .s_data0        (in_sig.s_data0  ),
                .s_data1        (in_sig.s_data1  ),
                .s_valid        (in_sig.s_valid  ),

                .m_data         (out_sig.m_data  ) 
            );

    int     input_no = 0;
    int     output_no = 0;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            input_no  <= 0;
            output_no <= -LATENCY - 1;
        end
        else begin
            if ( input_no < input_table.size() ) begin
                in_sig <= input_table[input_no];
            end

            if ( output_no >= 0 &&  output_no < expected_table.size() ) begin
                if ( out_sig.m_data != expected_table[output_no].m_data ) begin
                    $display("ERROR: output_no=%0d m_data=%h expected=%h", output_no, out_sig.m_data, expected_table[output_no].m_data);
                    $finish;
                end
            end
            
            input_no  <= input_no + 1;
            if ( in_sig.cke ) begin
                output_no <= output_no + 1;
                if ( output_no == expected_table.size() - 1 ) begin
                    $display("Single test passed");
                end
            end
        end
    end

endmodule


`default_nettype wire


// end of file
