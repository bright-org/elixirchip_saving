

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
    //  SVAを使った parameter別検証
    // -----------------------------------------

    for ( genvar LATENCY = 0; LATENCY <= 3; LATENCY++ ) begin : latency
        for ( genvar DATA_BITS = 2; DATA_BITS <= 32; DATA_BITS++ ) begin : data_bits
            tb_elixirchip_es1_spu_op_sra
                    #(
                        .LATENCY        (LATENCY    ),
                        .DATA_BITS      (DATA_BITS  ),
                        .DEVICE         (DEVICE     ),
                        .SIMULATION     (SIMULATION ),
                        .DEBUG          (DEBUG      )
                    )
                u_tb_elixirchip_es1_spu_op_sra
                    (
                        .reset          ,
                        .clk            
                    );
        end
    end
    
    // SVA bind  (インスタンスへの bind は verilator が未対応)
    bind elixirchip_es1_spu_op_sra sva_elixirchip_es1_spu_op_sra
            #(
                .LATENCY            (LATENCY        ),
                .DATA_BITS          (DATA_BITS      ),
                .MAX_SHIFT          (MAX_SHIFT      ),
                .SHIFT_BITS         (SHIFT_BITS     ),
                .CLEAR_DATA         (CLEAR_DATA     ),
                .IMMEDIATE_SHIFT    (IMMEDIATE_SHIFT),
                .IMMEDIATE_DATA     (IMMEDIATE_DATA ),
                .DEVICE             (DEVICE         ),
                .SIMULATION         (SIMULATION     ),
                .DEBUG              (DEBUG          )
            )
        u_sva
            (
                .*
            );




    // -----------------------------------------
    //  typical な個別検証
    // -----------------------------------------

    localparam  int     LATENCY         = 3                         ;   // レイテンシ指定
    localparam  int     DATA_BITS       = 32                        ;   // データ幅指定
    localparam  type    data_t          = logic [DATA_BITS-1:0]     ;   // データ型指定(オプション)
    localparam  int     MAX_SHIFT       = DATA_BITS                 ;   // 最大シフト量
    localparam  int     SHIFT_BITS      = $clog2(MAX_SHIFT)         ;   // シフト量幅
    localparam  type    shift_t         = logic [SHIFT_BITS-1:0]    ;   // シフト量型指定
    localparam  data_t  CLEAR_DATA      = 123                       ;   // クリア値
    localparam  bit     IMMEDIATE_SHIFT = 1'b0                      ;   // s_shift が即値の場合に1にする(オプション)
    localparam  bit     IMMEDIATE_DATA  = 1'b0                      ;   // s_data  が即値の場合に1にする(オプション)

    typedef struct {
        logic   cke     ;   // クロックイネーブル
        shift_t s_shift ;   // キャリー入力
        data_t  s_data  ;   // 入力データ
        logic   s_clear ;   // クリア
        logic   s_valid ;   // 信号有効
    } input_signals_t;

    typedef struct {
        data_t  m_data  ;   // 出力データ
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_shift: 5'd0,  s_data: 32'h12345678, s_clear: 1'b0, s_valid: 1'b1}, // 0
        '{cke: 1'b1, s_shift: 5'd31, s_data: 32'h87654321, s_clear: 1'b0, s_valid: 1'b1}, // 1
        '{cke: 1'b1, s_shift: 5'd31, s_data: 32'h12345678, s_clear: 1'b0, s_valid: 1'b1}, // 2
        '{cke: 1'b1, s_shift: 5'd0,  s_data: 32'h87654321, s_clear: 1'b0, s_valid: 1'b1}, // 3
        '{cke: 1'b1, s_shift: 5'd4,  s_data: 32'h12345678, s_clear: 1'b0, s_valid: 1'b1}, // 4
        '{cke: 1'b0, s_shift: 5'd8,  s_data: 32'h87654321, s_clear: 1'b0, s_valid: 1'b1}, // keep
        '{cke: 1'b1, s_shift: 5'd8,  s_data: 32'h87654321, s_clear: 1'b0, s_valid: 1'b1}, // 5
        '{cke: 1'b1, s_shift: 5'd16, s_data: 32'h12345678, s_clear: 1'b0, s_valid: 1'b1}, // 6
        '{cke: 1'b1, s_shift: 5'd24, s_data: 32'h87654321, s_clear: 1'b0, s_valid: 1'b1}, // 7
        '{cke: 1'b1, s_shift: 5'd16, s_data: 32'h99999999, s_clear: 1'b1, s_valid: 1'b1},   // 8
        '{cke: 1'b1, s_shift: 5'd17, s_data: 32'h88888888, s_clear: 1'b0, s_valid: 1'b0}    // 9
};
    
    output_signals_t expected_table [] = '{
        '{m_data: 32'h12345678}, // 0
        '{m_data: 32'hffffffff}, // 1
        '{m_data: 32'h00000000}, // 2
        '{m_data: 32'h87654321}, // 3
        '{m_data: 32'h01234567}, // 4
        '{m_data: 32'hff876543}, // 5
        '{m_data: 32'h00001234}, // 6
        '{m_data: 32'hffffff87}, // 7
        '{m_data: 32'd123},      // 8
        '{m_data: 32'd123}       // 9
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_shift: '0, s_data: '0, s_clear: 1'b0, s_valid: 1'b1};
    output_signals_t    out_sig;

    elixirchip_es1_spu_op_sra
            #(
                .LATENCY        (LATENCY        ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .IMMEDIATE_SHIFT(1'b0           ),
                .IMMEDIATE_DATA (1'b0           ),
                .USE_CLEAR      (1'b1           ),
                .USE_VALID      (1'b1           ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          ) 
            )
        u_elixirchip_es1_spu_op_sra
            (
                .reset          ,
                .clk            ,
                .cke            (in_sig.cke    ),

                .s_shift        (in_sig.s_shift),
                .s_data         (in_sig.s_data ),
                .s_clear        (in_sig.s_clear),
                .s_valid        (in_sig.s_valid),

                .m_data         (out_sig.m_data) 
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
