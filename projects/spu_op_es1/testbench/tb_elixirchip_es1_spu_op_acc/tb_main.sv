

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
    
    for ( genvar LATENCY = 1; LATENCY <= 3; LATENCY++ ) begin : latency
        for ( genvar S_DATA_BITS = 1; S_DATA_BITS <= 16; S_DATA_BITS += 1 ) begin : s_data_bits
            for ( genvar M_DATA_BITS = S_DATA_BITS; M_DATA_BITS <= 32; M_DATA_BITS += 8 ) begin : m_data_bits
                tb_elixirchip_es1_spu_op_acc
                        #(
                            .LATENCY        (LATENCY                    ),
                            .S_DATA_BITS    (S_DATA_BITS                ),
                            .M_DATA_BITS    (M_DATA_BITS                ),
                            .DEVICE         (DEVICE                     ),
                            .SIMULATION     (SIMULATION                 ),
                            .DEBUG          (DEBUG                      )
                        )
                    u_tb_elixirchip_es1_spu_op_acc
                        (
                            .reset          ,
                            .clk            
                        );
            end
        end
    end

    // SVA bind (verilator でも使えるようにモジュール名でバインド)
    bind elixirchip_es1_spu_op_acc sva_elixirchip_es1_spu_op_acc
            #(
                .LATENCY        (LATENCY        ),
                .S_DATA_BITS    (S_DATA_BITS    ),
                .M_DATA_BITS    (M_DATA_BITS    ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .CLEAR_CARRY    (CLEAR_CARRY    ),
                .IMMEDIATE_DATA      (IMMEDIATE_DATA      ),
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

    localparam  int         LATENCY      = 3                            ;   // レイテンシ指定
    localparam  int         S_DATA_BITS  = 8                            ;   // s_data 幅指定
    localparam  type        s_data_t     = logic [S_DATA_BITS-1:0]      ;   // s_data 型指定(オプション)
    localparam  int         M_DATA_BITS  = 10                           ;   // m_data 幅指定
    localparam  type        m_data_t     = logic [M_DATA_BITS-1:0]      ;   // m_data 型指定(オプション)
    localparam  m_data_t    CLEAR_DATA   = 123                          ;   // m_data クリア値
    localparam  logic       CLEAR_CARRY  = 1'b0                         ;   // m_carryクリア値
    localparam  bit         IMMEDIATE_DATA1   = 1'b0                         ;   // s_data が即値の場合に1にする

    typedef struct {
        logic       cke         ;   // クロックイネーブル
        logic       s_sub       ;   // 1の時にアキュミュレータの演算を加算ではなく減算にする
        logic       s_carry     ;   // キャリー
        s_data_t    s_data      ;   // 入力データ0
        logic       s_clear     ;   // クリア
        logic       s_valid     ;   // 1の時有効データ
    } input_signals_t;

    typedef struct {
        logic       m_carry ;   // 1の時有効データ
        m_data_t    m_data  ;   // 出力データ
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b1, s_data: s_data_t'(  2), s_clear: 1'b1, s_valid: 1'b1},    //  0: 123 (clear)
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'(  5), s_clear: 1'b0, s_valid: 1'b1},    //  1: 123 + 5 = 128
        '{cke: 1'b1, s_sub: 1'b1, s_carry: 1'b1, s_data: s_data_t'(  1), s_clear: 1'b0, s_valid: 1'b1},    //  2: 128 - 1 = 127
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'(  0), s_clear: 1'b0, s_valid: 1'b1},    //  3: 127 + 0 = 127
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b1, s_data: s_data_t'( 99), s_clear: 1'b1, s_valid: 1'b1},    //  4: 123 (clear)
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'(  2), s_clear: 1'b0, s_valid: 1'b1},    //  5: 123 + 2 = 125
        '{cke: 1'b1, s_sub: 1'b1, s_carry: 1'b1, s_data: s_data_t'(  2), s_clear: 1'b0, s_valid: 1'b1},    //  6: 125 - 2 = 123
        '{cke: 1'b0, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'(  4), s_clear: 1'b0, s_valid: 1'b1},    //  cke = 0
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'(  4), s_clear: 1'b0, s_valid: 1'b1},    //  7: 123 + 4 = 127
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'( 99), s_clear: 1'b0, s_valid: 1'b0},    //  8: keep :  127
        '{cke: 1'b1, s_sub: 1'b1, s_carry: 1'b1, s_data: s_data_t'(  4), s_clear: 1'b0, s_valid: 1'b1},    //  9: 127 - 4 = 123
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'(  9), s_clear: 1'b0, s_valid: 1'b1},    // 10: 123 + 9 = 132
        '{cke: 1'b1, s_sub: 1'b0, s_carry: 1'b0, s_data: s_data_t'(255), s_clear: 1'b0, s_valid: 1'b1}     // 11: 132 + 255 = 387
    };
    
    output_signals_t expected_table [] = '{
        '{m_carry: 1'b0, m_data: m_data_t'( 123)},  // 0
        '{m_carry: 1'b0, m_data: m_data_t'( 128)},  // 1
        '{m_carry: 1'b1, m_data: m_data_t'( 127)},  // 2
        '{m_carry: 1'b0, m_data: m_data_t'( 127)},  // 3
        '{m_carry: 1'b0, m_data: m_data_t'( 123)},  // 4
        '{m_carry: 1'b0, m_data: m_data_t'( 125)},  // 5
        '{m_carry: 1'b1, m_data: m_data_t'( 123)},  // 6
        '{m_carry: 1'b0, m_data: m_data_t'( 127)},  // 7
        '{m_carry: 1'b0, m_data: m_data_t'( 127)},  // 8
        '{m_carry: 1'b1, m_data: m_data_t'( 123)},  // 9
        '{m_carry: 1'b0, m_data: m_data_t'( 132)},  // 10
        '{m_carry: 1'b0, m_data: m_data_t'( 387)}   // 11
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_sub: 1'b0, s_carry: '0, s_data: '0, s_clear: 1'b0, s_valid: 1'b0};
    output_signals_t    out_sig;

    elixirchip_es1_spu_op_acc
            #(
                .LATENCY        (LATENCY            ),
                .S_DATA_BITS    (S_DATA_BITS        ),
                .s_data_t       (s_data_t           ),
                .M_DATA_BITS    (M_DATA_BITS        ),
                .m_data_t       (m_data_t           ),
                .CLEAR_DATA     (CLEAR_DATA         ),
                .CLEAR_CARRY    (CLEAR_CARRY        ),
                .IMMEDIATE_DATA      (1'b0               ),
                .DEVICE         (DEVICE             ),
                .SIMULATION     (SIMULATION         ),
                .DEBUG          (DEBUG              ) 
            )
        u_elixirchip_es1_spu_op_acc
            (
                .reset          ,
                .clk            ,
                .cke            (in_sig.cke         ),

                .s_sub          (in_sig.s_sub       ),
                .s_carry        (in_sig.s_carry     ),
                .s_data         (in_sig.s_data      ),
                .s_clear        (in_sig.s_clear     ),
                .s_valid        (in_sig.s_valid     ),

                .m_carry        (out_sig.m_carry    ),
                .m_data         (out_sig.m_data     ) 
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
                    if ( out_sig.m_carry !== expected_table[output_no].m_carry || out_sig.m_data !== expected_table[output_no].m_data ) begin
                    $display("ERROR: output_no=%0d m_carry=%b m_data=%h expected=%h", output_no,  out_sig.m_carry, out_sig.m_data, expected_table[output_no].m_data);
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
