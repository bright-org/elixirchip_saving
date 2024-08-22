

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
        for ( genvar ADDR_BITS = 1; ADDR_BITS <= 16; ADDR_BITS *= 2 ) begin : s_wdata_bits
            for ( genvar DATA_BITS = 1; DATA_BITS <= 16; DATA_BITS *= 2 ) begin : s_wdata_bits
                tb_elixirchip_es1_spu_op_mem_sp
                        #(
                            .LATENCY        (LATENCY    ),
                            .DATA_BITS      (DATA_BITS  ),
                            .ADDR_BITS      (ADDR_BITS  ),
                            .DEVICE         (DEVICE     ),
                            .SIMULATION     (SIMULATION ),
                            .DEBUG          (DEBUG      )
                        )
                    u_tb_elixirchip_es1_spu_mem_sp
                        (
                            .reset          ,
                            .clk            
                        );
            end
        end
    end

    // SVA bind (verilator でも使えるようにモジュール名でバインド)
    bind elixirchip_es1_spu_op_mem_sp sva_elixirchip_es1_spu_op_mem_sp
            #(
                .LATENCY        (LATENCY        ),
                .DATA_BITS      (DATA_BITS      ),
                .ADDR_BITS      (ADDR_BITS      ),
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
    
    localparam  int     LATENCY    = 3                      ;   // レイテンシ指定
    localparam  int     DATA_BITS  = 8                      ;   // データ幅指定
    localparam  type    data_t     = logic [DATA_BITS-1:0]  ;   // データ型指定(オプション)
    localparam  int     ADDR_BITS  = 3                      ;   // アドレス幅指定
    localparam  type    addr_t     = logic [ADDR_BITS-1:0]  ;   // アドレス型指定(オプション)
    localparam  int     MEM_SIZE   = 2 ** ADDR_BITS         ;   // メモリサイズ
    localparam          MEM_TYPE   = "block"                ;   // メモリタイプ("block" or "distributed")      

    typedef struct {
        logic       cke         ;   // クロックイネーブル
        addr_t      s_addr      ;   // 1の時にアキュミュレータは積算せずに新しい値をセット
        data_t      s_wdata     ;   // s_set_value
        logic       s_wvalid    ;   // 1の時にアキュミュレータの演算を加算ではなく減算にする
    } input_signals_t;

    typedef struct {
        data_t      m_rdata     ;   // 出力データ
        logic       m_valid     ;   // 出力有効
    } output_signals_t;

    input_signals_t input_table [] = '{
        '{cke: 1'b1, s_addr: addr_t'(0), s_wdata: data_t'(8'h10), s_wvalid: 1'b1},   //  0
        '{cke: 1'b1, s_addr: addr_t'(1), s_wdata: data_t'(8'h11), s_wvalid: 1'b1},   //  1
        '{cke: 1'b1, s_addr: addr_t'(2), s_wdata: data_t'(8'h12), s_wvalid: 1'b1},   //  2
        '{cke: 1'b1, s_addr: addr_t'(3), s_wdata: data_t'(8'h13), s_wvalid: 1'b1},   //  3
        '{cke: 1'b1, s_addr: addr_t'(4), s_wdata: data_t'(8'h14), s_wvalid: 1'b1},   //  4
        '{cke: 1'b1, s_addr: addr_t'(5), s_wdata: data_t'(8'h15), s_wvalid: 1'b1},   //  5
        '{cke: 1'b0, s_addr: addr_t'(6), s_wdata: data_t'(8'h16), s_wvalid: 1'b1},   //  cke = 0
        '{cke: 1'b1, s_addr: addr_t'(6), s_wdata: data_t'(8'h16), s_wvalid: 1'b1},   //  6
        '{cke: 1'b1, s_addr: addr_t'(7), s_wdata: data_t'(8'h17), s_wvalid: 1'b1},   //  7

        '{cke: 1'b1, s_addr: addr_t'(0), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   //  8
        '{cke: 1'b1, s_addr: addr_t'(1), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   //  9
        '{cke: 1'b1, s_addr: addr_t'(2), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 10
        '{cke: 1'b1, s_addr: addr_t'(3), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 11
        '{cke: 1'b0, s_addr: addr_t'(4), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // cke = 0
        '{cke: 1'b1, s_addr: addr_t'(4), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 12
        '{cke: 1'b1, s_addr: addr_t'(5), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 13
        '{cke: 1'b1, s_addr: addr_t'(6), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 14
        '{cke: 1'b1, s_addr: addr_t'(7), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 15

        '{cke: 1'b1, s_addr: addr_t'(3), s_wdata: data_t'(8'h55), s_wvalid: 1'b1},   // 16
        '{cke: 1'b1, s_addr: addr_t'(5), s_wdata: data_t'(8'haa), s_wvalid: 1'b1},   // 17

        '{cke: 1'b1, s_addr: addr_t'(7), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 18
        '{cke: 1'b1, s_addr: addr_t'(6), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 19
        '{cke: 1'b1, s_addr: addr_t'(5), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 20
        '{cke: 1'b1, s_addr: addr_t'(4), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 21
        '{cke: 1'b0, s_addr: addr_t'(3), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // cke = 0
        '{cke: 1'b1, s_addr: addr_t'(3), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 22
        '{cke: 1'b1, s_addr: addr_t'(2), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 23
        '{cke: 1'b1, s_addr: addr_t'(1), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 24
        '{cke: 1'b1, s_addr: addr_t'(0), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 25

        '{cke: 1'b1, s_addr: addr_t'(5), s_wdata: data_t'(8'haa), s_wvalid: 1'b1},   // 26
        '{cke: 1'b1, s_addr: addr_t'(5), s_wdata: data_t'(8'h99), s_wvalid: 1'b0},   // 27
        '{cke: 1'b1, s_addr: addr_t'(3), s_wdata: data_t'(8'h55), s_wvalid: 1'b1},   // 28
        '{cke: 1'b1, s_addr: addr_t'(3), s_wdata: data_t'(8'h99), s_wvalid: 1'b0}    // 29
    };
    
    output_signals_t expected_table [] = '{
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 0
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 1
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 2
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 3
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 4
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 5
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 6
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 7

        '{m_rdata: data_t'(8'h10), m_valid: 1'b1},  // 8
        '{m_rdata: data_t'(8'h11), m_valid: 1'b1},  // 9
        '{m_rdata: data_t'(8'h12), m_valid: 1'b1},  // 10
        '{m_rdata: data_t'(8'h13), m_valid: 1'b1},  // 11
        '{m_rdata: data_t'(8'h14), m_valid: 1'b1},  // 12
        '{m_rdata: data_t'(8'h15), m_valid: 1'b1},  // 13
        '{m_rdata: data_t'(8'h16), m_valid: 1'b1},  // 14
        '{m_rdata: data_t'(8'h17), m_valid: 1'b1},  // 15
        
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 16
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 17

        '{m_rdata: data_t'(8'h17), m_valid: 1'b1},  // 18
        '{m_rdata: data_t'(8'h16), m_valid: 1'b1},  // 19
        '{m_rdata: data_t'(8'haa), m_valid: 1'b1},  // 20
        '{m_rdata: data_t'(8'h14), m_valid: 1'b1},  // 21
        '{m_rdata: data_t'(8'h55), m_valid: 1'b1},  // 22
        '{m_rdata: data_t'(8'h12), m_valid: 1'b1},  // 23
        '{m_rdata: data_t'(8'h11), m_valid: 1'b1},  // 24
        '{m_rdata: data_t'(8'h10), m_valid: 1'b1},  // 25

        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 26
        '{m_rdata: data_t'(8'haa), m_valid: 1'b1},  // 27
        '{m_rdata: data_t'(8'hxx), m_valid: 1'b0},  // 28
        '{m_rdata: data_t'(8'h55), m_valid: 1'b1}   // 29
    };

    input_signals_t     in_sig = '{cke: 1'b1, s_addr: '0, s_wdata: '0, s_wvalid: 1'b0};
    output_signals_t    out_sig;

    elixirchip_es1_spu_op_mem_sp
            #(
                .LATENCY        (LATENCY        ),
                .DATA_BITS      (DATA_BITS      ),
                .ADDR_BITS      (ADDR_BITS      ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          ) 
            )
        u_elixirchip_es1_spu_op_mem_sp
            (
                .reset          (reset          ),
                .clk            (clk            ),
                .cke            (in_sig.cke     ),
                .s_addr         (in_sig.s_addr  ),
                .s_wdata        (in_sig.s_wdata ),
                .s_wvalid       (in_sig.s_wvalid),
                .m_rdata        (out_sig.m_rdata) 
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
                if ( expected_table[output_no].m_valid ) begin
                     if ( out_sig.m_rdata != expected_table[output_no].m_rdata ) begin
                        $display("ERROR: output_no=%0d m_rdata=%h expected=%h", output_no, out_sig.m_rdata, expected_table[output_no].m_rdata);
                        $finish;
                    end
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
