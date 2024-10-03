

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
    
    for ( genvar LATENCY = 0; LATENCY <= 3; LATENCY++ ) begin : latency
        for ( genvar DATA_BITS = 1; DATA_BITS <= 8 * (2 ** LATENCY); DATA_BITS *= 2 ) begin : data_bits
            tb_elixirchip_es1_spu_op_add
                    #(
                        .LATENCY        (LATENCY    ),
                        .DATA_BITS      (DATA_BITS  ),
                        .DEVICE         (DEVICE     ),
                        .SIMULATION     (SIMULATION ),
                        .DEBUG          (DEBUG      )
                    )
                u_tb_elixirchip_es1_spu_op_add
                    (
                        .reset          ,
                        .clk            
                    );
        end
    end
    
    // SVA bind  (インスタンスへの bind は verilator が未対応)
    bind elixirchip_es1_spu_op_add sva_elixirchip_es1_spu_op_add
            #(
                .LATENCY            (LATENCY    ),
                .DATA_BITS          (DATA_BITS  ),
                .IMMEDIATE_CARRY    (1'b1       ),
                .IMMEDIATE_DATA0    (1'b0       ),
                .IMMEDIATE_DATA1    (1'b0       ),
                .CLEAR_DATA         (CLEAR_DATA ),
                .CLEAR_CARRY        (CLEAR_CARRY),
                .CLEAR_MSB_C        (CLEAR_MSB_C),
                .DEVICE             (DEVICE     ),
                .SIMULATION         (SIMULATION ),
                .DEBUG              (DEBUG      ) 
            )
        u_sva
            (
                .*
            );
    

    // -----------------------------------------
    //  typical な個別検証
    // -----------------------------------------

    localparam  int     LATENCY     = 3                       ;   // レイテンシ指定
    localparam  int     DATA_BITS   = 8                       ;   // データ幅指定
    localparam  type    data_t      = logic [DATA_BITS-1:0]   ;   // データ型指定(オプション)
    localparam  data_t  CLEAR_DATA  = 123                     ;   // クリア値
    localparam  logic   CLEAR_CARRY = 1'b0                    ;   // クリア値
    localparam  logic   CLEAR_MSB_C = 1'b1                    ;   // クリア値
    localparam  bit     IMMEDIATE_CARRY  = 1'b1                    ;   // s_carry が即値の場合に1にする
    localparam  bit     IMMEDIATE_DATA0  = 1'b0                    ;   // s_data0 が即値の場合に1にする
    localparam  bit     IMMEDIATE_DATA1  = 1'b0                    ;   // s_data1 が即値の場合に1にする
    typedef struct {
        logic   cke     ;   // クロックイネーブル
        logic   s_carry ;   // キャリー入力
        data_t  s_data0 ;   // 入力データ0
        data_t  s_data1 ;   // 入力データ1
        logic   s_clear ;   // クリア
        logic   s_valid ;   // 信号有効
    } input_signals_t;

    typedef struct {
        data_t  m_data  ;   // 出力データ
        logic   m_carry ;   // キャリー出力
        logic   m_msb_c ;   // MSB キャリー出力
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(   0), s_data1: data_t'(   0), s_clear: 1'b0, s_valid: 1'b1},    // 0 : => 0
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(   0), s_data1: data_t'( 255), s_clear: 1'b0, s_valid: 1'b1},    // 1 : => 255
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'( 255), s_data1: data_t'(   0), s_clear: 1'b0, s_valid: 1'b1},    // 2 : => 255
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'( 255), s_data1: data_t'( 255), s_clear: 1'b0, s_valid: 1'b1},    // 3 : => 254 (carry)
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(   5), s_data1: data_t'(   3), s_clear: 1'b0, s_valid: 1'b1},    // 4 : => 8
        '{cke: 1'b0, s_carry: 1'b0, s_data0: data_t'(  10), s_data1: data_t'(  12), s_clear: 1'b0, s_valid: 1'b1},    // cke=0 keep
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(  10), s_data1: data_t'(  12), s_clear: 1'b0, s_valid: 1'b1},    // 5 : => 22
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(  56), s_data1: data_t'( 200), s_clear: 1'b0, s_valid: 1'b1},    // 6 : => 0   (carry)

        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(-128), s_data1: data_t'(-128), s_clear: 1'b0, s_valid: 1'b1},    // 7 : => 0  (carry)
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(-128), s_data1: data_t'( 127), s_clear: 1'b0, s_valid: 1'b1},    // 8 : => -1
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'( 127), s_data1: data_t'(-128), s_clear: 1'b0, s_valid: 1'b1},    // 9 : => -1
        '{cke: 1'b0, s_carry: 1'b0, s_data0: data_t'( 127), s_data1: data_t'( 127), s_clear: 1'b0, s_valid: 1'b1},    // cke=0 keep
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'( 127), s_data1: data_t'( 127), s_clear: 1'b0, s_valid: 1'b1},    // 10 : => 254
        '{cke: 1'b1, s_carry: 1'b0, s_data0: data_t'(  10), s_data1: data_t'(  -5), s_clear: 1'b0, s_valid: 1'b1},    // 11 : =>  5 (carry)

        '{cke: 1'b1, s_carry: 1'b1, s_data0: data_t'(   0), s_data1: data_t'(   0), s_clear: 1'b0, s_valid: 1'b1},    // 12 : => 1
        '{cke: 1'b1, s_carry: 1'b1, s_data0: data_t'(   5), s_data1: data_t'(   3), s_clear: 1'b0, s_valid: 1'b1},    // 13 : => 9
        '{cke: 1'b1, s_carry: 1'b1, s_data0: data_t'( 200), s_data1: data_t'(  56), s_clear: 1'b0, s_valid: 1'b1},    // 14 : => 1 (carry)

        '{cke: 1'b1, s_carry: 1'b1, s_data0: data_t'(  99), s_data1: data_t'(   0), s_clear: 1'b1, s_valid: 1'b1},    // 15
        '{cke: 1'b1, s_carry: 1'b1, s_data0: data_t'(  88), s_data1: data_t'(   3), s_clear: 1'b0, s_valid: 1'b0}     // 16
    };
    
    output_signals_t expected_table [] = '{
        '{m_data: data_t'(   0), m_msb_c: 1'b0, m_carry: 1'b0},  // 0
        '{m_data: data_t'( 255), m_msb_c: 1'b0, m_carry: 1'b0},  // 1
        '{m_data: data_t'( 255), m_msb_c: 1'b0, m_carry: 1'b0},  // 2
        '{m_data: data_t'( 254), m_msb_c: 1'b1, m_carry: 1'b1},  // 3
        '{m_data: data_t'(   8), m_msb_c: 1'b0, m_carry: 1'b0},  // 4
        '{m_data: data_t'(  22), m_msb_c: 1'b0, m_carry: 1'b0},  // 5
        '{m_data: data_t'(   0), m_msb_c: 1'b1, m_carry: 1'b1},  // 6

        '{m_data: data_t'(   0), m_msb_c: 1'b0, m_carry: 1'b1},  // 7
        '{m_data: data_t'(  -1), m_msb_c: 1'b0, m_carry: 1'b0},  // 8
        '{m_data: data_t'(  -1), m_msb_c: 1'b0, m_carry: 1'b0},  // 9
        '{m_data: data_t'( 254), m_msb_c: 1'b1, m_carry: 1'b0},  // 10
        '{m_data: data_t'(   5), m_msb_c: 1'b1, m_carry: 1'b1},  // 11

        '{m_data: data_t'(   1), m_msb_c: 1'b0, m_carry: 1'b0},  // 12
        '{m_data: data_t'(   9), m_msb_c: 1'b0, m_carry: 1'b0},  // 13
        '{m_data: data_t'(   1), m_msb_c: 1'b1, m_carry: 1'b1},  // 14

        '{m_data: data_t'( 123), m_msb_c: 1'b1, m_carry: 1'b0},  // 15
        '{m_data: data_t'( 123), m_msb_c: 1'b1, m_carry: 1'b0}   // 16
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_carry: 1'b1, s_data0: data_t'(0), s_data1: data_t'(0), s_clear: 1'b0, s_valid: 1'b1};
    output_signals_t    out_sig;

    elixirchip_es1_spu_op_add
            #(
                .LATENCY            (LATENCY    ),
                .DATA_BITS          (DATA_BITS  ),
                .data_t             (data_t     ),
                .IMMEDIATE_CARRY    (1'b1       ),
                .IMMEDIATE_DATA0    (1'b0       ),
                .IMMEDIATE_DATA1    (1'b0       ),
                .CLEAR_DATA         (CLEAR_DATA ),
                .CLEAR_CARRY        (CLEAR_CARRY),
                .CLEAR_MSB_C        (CLEAR_MSB_C),
                .USE_CLEAR          (1'b1       ),
                .USE_VALID          (1'b1       ),
                .DEVICE             (DEVICE     ),
                .SIMULATION         (SIMULATION ),
                .DEBUG              (DEBUG      ) 
            )
        u_elixirchip_es1_spu_op_add
            (
                .reset   ,
                .clk     ,
                .cke     (in_sig.cke      ),

                .s_carry (in_sig.s_carry  ),
                .s_data0 (in_sig.s_data0  ),
                .s_data1 (in_sig.s_data1  ),
                .s_clear (in_sig.s_clear  ),
                .s_valid (in_sig.s_valid  ),

                .m_carry (out_sig.m_carry ),
                .m_msb_c (out_sig.m_msb_c ),
                .m_data  (out_sig.m_data  ) 
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
                if ( out_sig.m_msb_c != expected_table[output_no].m_msb_c ) begin
                    $display("ERROR: output_no=%0d m_msb_c=%h expected=%h", output_no, out_sig.m_msb_c, expected_table[output_no].m_msb_c);
                    $finish;
                end
                if ( out_sig.m_carry != expected_table[output_no].m_carry ) begin
                    $display("ERROR: output_no=%0d m_carry=%h expected=%h", output_no, out_sig.m_carry, expected_table[output_no].m_carry);
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
