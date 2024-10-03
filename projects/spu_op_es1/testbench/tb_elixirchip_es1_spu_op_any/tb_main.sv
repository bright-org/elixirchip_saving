

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
        for ( genvar DATA_BITS = 1; DATA_BITS <= 64; DATA_BITS++ ) begin : data_bits
            tb_elixirchip_es1_spu_op_any
                    #(
                        .LATENCY        (LATENCY    ),
                        .DATA_BITS      (DATA_BITS  ),
                        .DEVICE         (DEVICE     ),
                        .SIMULATION     (SIMULATION ),
                        .DEBUG          (DEBUG      )
                    )
                u_tb_elixirchip_es1_spu_op_any
                    (
                        .reset          ,
                        .clk            
                    );
        end
    end


    // SVA bind
    bind elixirchip_es1_spu_op_any sva_elixirchip_es1_spu_op_any
            #(
                .LATENCY        (LATENCY    ),
                .DATA_BITS      (DATA_BITS  ),
                .CLEAR_DATA     (CLEAR_DATA ),
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

`ifndef __VERILATOR__

    localparam  int     LATENCY    = 3                      ;   // レイテンシ指定
    localparam  int     DATA_BITS  = 8                      ;   // データ幅指定
    localparam  type    data_t     = logic [DATA_BITS-1:0]  ;   // データ型指定(オプション)
    localparam  logic   CLEAR_DATA = 1                      ;   // クリア値

    typedef struct {
        logic   cke     ;   // クロックイネーブル
        data_t  s_data  ;   // 入力データ
        logic   s_clear ;   // クリア
        logic   s_valid ;   // 信号有効
    } input_signals_t;

    typedef struct {
        logic   m_data  ;   // 出力データ
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_data: data_t'(8'h00), s_clear: 1'b0, s_valid: 1'b1},    // 0: 0
        '{cke: 1'b1, s_data: data_t'(8'h10), s_clear: 1'b0, s_valid: 1'b1},    // 1: 1
        '{cke: 1'b1, s_data: data_t'(8'ha5), s_clear: 1'b0, s_valid: 1'b1},    // 2: 1
        '{cke: 1'b1, s_data: data_t'(8'h5a), s_clear: 1'b0, s_valid: 1'b1},    // 3: 1
        '{cke: 1'b0, s_data: data_t'(8'hff), s_clear: 1'b0, s_valid: 1'b1},    // cke=0
        '{cke: 1'b1, s_data: data_t'(8'hff), s_clear: 1'b0, s_valid: 1'b1},    // 4: 1
        '{cke: 1'b0, s_data: data_t'(8'h00), s_clear: 1'b0, s_valid: 1'b1},    // cke=0
        '{cke: 1'b1, s_data: data_t'(8'h00), s_clear: 1'b0, s_valid: 1'b1},    // 5: 0
        '{cke: 1'b1, s_data: data_t'(8'h00), s_clear: 1'b1, s_valid: 1'b1},    // 6 : clear
        '{cke: 1'b1, s_data: data_t'(8'h00), s_clear: 1'b0, s_valid: 1'b0}     // 7 : valid=0
    };

    output_signals_t expected_table [] = '{
        '{m_data: 1'b0},    // 0
        '{m_data: 1'b1},    // 1
        '{m_data: 1'b1},    // 2
        '{m_data: 1'b1},    // 3
        '{m_data: 1'b1},    // 4
        '{m_data: 1'b0},    // 5
        '{m_data: 1'b1},    // 6
        '{m_data: 1'b1}     // 7
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_data: data_t'(0), s_clear: 1'b0, s_valid: 1'b0};
    output_signals_t    out_sig;

    elixirchip_es1_spu_op_any
            #(
                .LATENCY    (LATENCY        ),
                .DATA_BITS  (DATA_BITS      ),
                .data_t     (data_t         ),
                .CLEAR_DATA (CLEAR_DATA     ),
                .USE_CLEAR  (1'b1           ),
                .USE_VALID  (1'b1           ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          ) 
            )
        u_elixirchip_es1_spu_op_any
            (
                .reset      ,
                .clk        ,
                .cke        (in_sig.cke     ),
                .s_data     (in_sig.s_data  ),
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

`endif


endmodule


`default_nettype wire


// end of file
