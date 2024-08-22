

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
            if ( cycle >= 1000 ) begin
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
    //  typical な個別検証
    // -----------------------------------------

    for ( genvar LATENCY = 0; LATENCY <= 3; LATENCY++ ) begin : latency
        for ( genvar DATA_BITS = 1; DATA_BITS <= 8; DATA_BITS += 8 ) begin : data_bits
            tb_elixirchip_es1_spu_op_sel_lt
                    #(
                        .LATENCY        (LATENCY    ),
                        .DATA_BITS      (DATA_BITS  ),
                        .DEVICE         (DEVICE     ),
                        .SIMULATION     (SIMULATION ),
                        .DEBUG          (DEBUG      )
                    )
                u_tb_elixirchip_es1_spu_op_sel_lt
                    (
                        .reset          ,
                        .clk            
                    );
        end
    end
    
    // SVA bind  (インスタンスへの bind は verilator が未対応)
    bind elixirchip_es1_spu_op_sel_lt sva_elixirchip_es1_spu_op_sel_lt
            #(
                .LATENCY        (LATENCY    ),
                .DATA_BITS      (DATA_BITS  ),
                .CLEAR_DATA     (CLEAR_DATA ),
                .IMMEDIATE_DATA0     (1'b0       ),
                .IMMEDIATE_DATA1     (1'b0       ),
                .DEVICE         (DEVICE     ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      ) 
            )
        u_sva
            (
                .*
            );


    // -----------------------------------------
    //  typical な個別検証
    // -----------------------------------------

    localparam  int     LATENCY    = 3                       ;   // レイテンシ指定
    localparam  int     DATA_BITS  = 8                       ;   // データ幅指定
    localparam  type    data_t     = logic [DATA_BITS-1:0]   ;   // データ型指定(オプション)
    localparam  data_t  CLEAR_DATA = 123                     ;   // クリア値
    localparam  bit     IMMEDIATE_DATA0 = 1'b0                    ;   // s_data0 が即値の場合に1にする
    localparam  bit     IMMEDIATE_DATA1 = 1'b0                    ;   // s_data1 が即値の場合に1にする

    typedef struct {
        logic           cke     ;   // クロックイネーブル
        logic           s_carry ;   // キャリーの入力
        logic           s_msb_c ;   // MSBキャリーの入力
        logic           s_sign  ;   // 符号の入力
        data_t          s_data0 ;   // 入力データ0
        data_t          s_data1 ;   // 入力データ1
        logic           s_clear ;   // クリア
        logic           s_valid ;   // 信号有効
    } input_signals_t;

    typedef struct {
        data_t  m_data  ;   // 出力データ
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_carry: 1'b0, s_msb_c: 1'b0, s_sign: 1'b0, s_data0: 8'h00, s_data1: 8'h01, s_clear: 1'b0, s_valid: 1'b1}, // 0
        '{cke: 1'b1, s_carry: 1'b0, s_msb_c: 1'b0, s_sign: 1'b1, s_data0: 8'h10, s_data1: 8'h11, s_clear: 1'b0, s_valid: 1'b1}, // 1
        '{cke: 1'b1, s_carry: 1'b0, s_msb_c: 1'b1, s_sign: 1'b0, s_data0: 8'h20, s_data1: 8'h21, s_clear: 1'b0, s_valid: 1'b1}, // 2
        '{cke: 1'b1, s_carry: 1'b0, s_msb_c: 1'b1, s_sign: 1'b1, s_data0: 8'h30, s_data1: 8'h31, s_clear: 1'b0, s_valid: 1'b1}, // 3
        '{cke: 1'b1, s_carry: 1'b1, s_msb_c: 1'b0, s_sign: 1'b0, s_data0: 8'h40, s_data1: 8'h41, s_clear: 1'b0, s_valid: 1'b1}, // 4
        '{cke: 1'b0, s_carry: 1'b1, s_msb_c: 1'b0, s_sign: 1'b0, s_data0: 8'h40, s_data1: 8'h41, s_clear: 1'b0, s_valid: 1'b1}, // cke=0 keep
        '{cke: 1'b1, s_carry: 1'b1, s_msb_c: 1'b0, s_sign: 1'b1, s_data0: 8'h50, s_data1: 8'h51, s_clear: 1'b0, s_valid: 1'b1}, // 5
        '{cke: 1'b1, s_carry: 1'b1, s_msb_c: 1'b1, s_sign: 1'b0, s_data0: 8'h60, s_data1: 8'h61, s_clear: 1'b0, s_valid: 1'b1}, // 6
        '{cke: 1'b1, s_carry: 1'b1, s_msb_c: 1'b1, s_sign: 1'b1, s_data0: 8'h70, s_data1: 8'h71, s_clear: 1'b0, s_valid: 1'b1}, // 7
        '{cke: 1'b1, s_carry: 1'b0, s_msb_c: 1'b0, s_sign: 1'b0, s_data0: 8'h80, s_data1: 8'h81, s_clear: 1'b1, s_valid: 1'b1}, // 8 : clear
        '{cke: 1'b1, s_carry: 1'b1, s_msb_c: 1'b0, s_sign: 1'b0, s_data0: 8'h90, s_data1: 8'h91, s_clear: 1'b0, s_valid: 1'b0}  // 9 : valid=0
    };
    
    output_signals_t expected_table [] = '{
        '{m_data: 8'h00},    // 0
        '{m_data: 8'h11},    // 1
        '{m_data: 8'h21},    // 2
        '{m_data: 8'h30},    // 3
        '{m_data: 8'h41},    // 4
        '{m_data: 8'h50},    // 5
        '{m_data: 8'h60},    // 6
        '{m_data: 8'h71},    // 7
        '{m_data: 8'd123},   // 8
        '{m_data: 8'd123}    // 9
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_carry: 1'b1, s_msb_c: 1'b0, s_sign: 1'b0, s_data0: '0, s_data1: '0, s_clear: 1'b0, s_valid: 1'b0};
    output_signals_t    out_sig;

    elixirchip_es1_spu_op_sel_lt
            #(
                .LATENCY        (LATENCY    ),
                .DATA_BITS      (DATA_BITS  ),
                .data_t         (data_t     ),
                .CLEAR_DATA     (CLEAR_DATA ),
                .IMMEDIATE_DATA0     (1'b0       ),
                .IMMEDIATE_DATA1     (1'b0       ),
                .DEVICE         (DEVICE     ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      ) 
            )
        u_elixirchip_es1_spu_op_sel
            (
                .reset      ,
                .clk        ,
                .cke        (in_sig.cke     ),

                .s_carry    (in_sig.s_carry ),
                .s_msb_c    (in_sig.s_msb_c ),
                .s_sign     (in_sig.s_sign  ),
                .s_data0    (in_sig.s_data0 ),
                .s_data1    (in_sig.s_data1 ),
                .s_clear    (in_sig.s_clear ),
                .s_valid    (in_sig.s_valid ),

                .m_data     (out_sig.m_data ) 
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
