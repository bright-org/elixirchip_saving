

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

    for ( genvar LATENCY = 0; LATENCY <= 16; LATENCY++ ) begin : latency
        tb_elixirchip_es1_spu_ctl_valid
                #(
                    .LATENCY        (LATENCY    ),
                    .DEVICE         (DEVICE     ),
                    .SIMULATION     (SIMULATION ),
                    .DEBUG          (DEBUG      )
                )
            u_tb_elixirchip_es1_spu_ctl_valid
                (
                    .reset          ,
                    .clk            
                );
    end
    
    // SVA bind  (インスタンスへの bind は verilator が未対応)
    bind elixirchip_es1_spu_ctl_valid sva_elixirchip_es1_spu_ctl_valid
            #(
                .LATENCY        (LATENCY    ),
                .DEVICE         (DEVICE     ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      ) 
            )
        u_sva
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_valid        ,
                
                .m_valid         
            );



    // -----------------------------------------
    //  typical な個別検証
    // -----------------------------------------

    localparam  int     LATENCY      = 3  ;   // レイテンシ指定

    typedef struct {
        logic       cke         ;   // クロックイネーブル
        logic       s_valid     ;   // 信号有効
    } input_signals_t;

    typedef struct {
        logic       m_valid ;   // 出力有効
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_valid: 1'b1},    //  0
        '{cke: 1'b1, s_valid: 1'b0},    //  1
        '{cke: 1'b1, s_valid: 1'b1},    //  2
        '{cke: 1'b1, s_valid: 1'b0},    //  3
        '{cke: 1'b1, s_valid: 1'b1},    //  4
        '{cke: 1'b1, s_valid: 1'b0},    //  5
        '{cke: 1'b1, s_valid: 1'b1},    //  6
        '{cke: 1'b0, s_valid: 1'b0},    //  cke=0
        '{cke: 1'b1, s_valid: 1'b0},    //  7
        '{cke: 1'b1, s_valid: 1'b1},    //  8
        '{cke: 1'b1, s_valid: 1'b0}     //  9
    };
    
    output_signals_t expected_table [] = '{
        '{m_valid: 1'b1},  // 0
        '{m_valid: 1'b0},  // 1
        '{m_valid: 1'b1},  // 2
        '{m_valid: 1'b0},  // 3
        '{m_valid: 1'b1},  // 4
        '{m_valid: 1'b0},  // 5
        '{m_valid: 1'b1},  // 6
        '{m_valid: 1'b0},  // 7
        '{m_valid: 1'b1},  // 8
        '{m_valid: 1'b0}   // 9
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_valid: 1'b0};
    output_signals_t    out_sig;

    elixirchip_es1_spu_ctl_valid
            #(
                .LATENCY        (LATENCY        ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          ) 
            )
        u_elixirchip_es1_spu_ctl_valid
            (
                .reset          ,
                .clk            ,
                .cke            (in_sig.cke      ),

                .s_valid        (in_sig.s_valid  ),

                .m_valid        (out_sig.m_valid ) 
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
                if ( out_sig.m_valid != expected_table[output_no].m_valid ) begin
                    $display("ERROR: output_no=%0d m_data=%h expected=%h", output_no, out_sig.m_valid, expected_table[output_no].m_valid);
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
