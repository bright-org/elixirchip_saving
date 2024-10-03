

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_lut
        #(
            parameter   int                         LATENCY      = 1                        ,   // レイテンシ指定
            parameter   int                         TABLE_SIZE   = 64                       ,   // テーブルサイズ
            parameter   int                         ADDR_BITS    = $clog2(TABLE_SIZE)       ,   // アドレス幅
            parameter   type                        addr_t       = logic [ADDR_BITS-1:0]    ,   // データ型指定(オプション)
            parameter   int                         DATA_BITS    = 8                        ,   // データ幅指定
            parameter   type                        data_t       = logic [DATA_BITS-1:0]    ,   // データ型指定(オプション)
            parameter   data_t                      CLEAR_DATA   = 123                      ,   // m_data クリア値
//          parameter   data_t  [TABLE_SIZE-1:0]    TABLE_VALUES = '0                       ,   // テーブルデータ
            parameter                               DEVICE       = "RTL"                    ,   // デバイス名
            parameter                               SIMULATION   = "false"                  ,   // シミュレーション
            parameter                               DEBUG        = "false"                      // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk         // クロック
        );

    localparam  data_t  [63:0]    TABLE_VALUES = '{
        8'h00, 8'h01, 8'h02, 8'h03, 8'h04, 8'h05, 8'h06, 8'h07,
        8'h08, 8'h09, 8'h0a, 8'h0b, 8'h0c, 8'h0d, 8'h0e, 8'h0f,
        8'h10, 8'h11, 8'h12, 8'h13, 8'h14, 8'h15, 8'h16, 8'h17,
        8'h18, 8'h19, 8'h1a, 8'h1b, 8'h1c, 8'h1d, 8'h1e, 8'h1f,
        8'h20, 8'h21, 8'h22, 8'h23, 8'h24, 8'h25, 8'h26, 8'h27,
        8'h28, 8'h29, 8'h2a, 8'h2b, 8'h2c, 8'h2d, 8'h2e, 8'h2f,
        8'h30, 8'h31, 8'h32, 8'h33, 8'h34, 8'h35, 8'h36, 8'h37,
        8'h38, 8'h39, 8'h3a, 8'h3b, 8'h3c, 8'h3d, 8'h3e, 8'h3f
    };

    // ランダムにCKEを下げる
    logic           cke     ;
    always_ff @( negedge clk ) begin
        cke <= ($urandom_range(0, 9) != 0);
    end

    addr_t          s_addr  ;
    logic           s_clear ;
    logic           s_valid ;
    data_t          m_data  ;

    elixirchip_es1_spu_op_lut
            #(
                .LATENCY        (LATENCY        ),
                .TABLE_SIZE     (TABLE_SIZE     ),
                .ADDR_BITS      (ADDR_BITS      ),
                .addr_t         (addr_t         ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .TABLE_VALUES   (TABLE_VALUES   ),
                .USE_CLEAR      (1'b1           ),
                .USE_VALID      (1'b1           ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_lut
            (
                .*
            );


    // -----------------------------------------
    //  testbench
    // -----------------------------------------

    int     cycle = 0;
    always_ff @(posedge clk) begin
        if ( reset ) begin
            cycle <= 0;
        end
        else if ( cke ) begin
            cycle <= cycle + 1;
        end
    end

    int             sel0;
    logic   [1:0]   sel2;
    always_ff @(posedge clk) begin
        if ( cycle < 2048 ) begin
            // 前半は網羅テスト
            sel0    <= int'(cycle[2:0]);
            sel2    <=   2'(cycle[7:6]);
        end
        else begin
            // 後半はランダムテスト
            sel0    <= $urandom_range(0, 7);
            sel2    <= 2'($urandom_range(0, 3));
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_addr  <= '0;
            s_clear <= 1'b0;
            s_valid <= 1'b1;
        end
        else if ( cke ) begin
            case ( sel0 )
            0:          s_addr <= '0;                                                       // unsigned min ALL-0
            1:          s_addr <= '1;                                                       // unsigned max ALL-1
            3:          s_addr <=  addr_t'(2**($bits(addr_t)-1)  );                         // signed min
            4:          s_addr <=  addr_t'(2**($bits(addr_t)-1)-1);                         // signed max
            5:          s_addr <=  (addr_t'(1) << $urandom_range(0, $bits(addr_t)-1));      // one-hot
            6:          s_addr <= ~(addr_t'(1) << $urandom_range(0, $bits(addr_t)-1));      // one-hot(neg)
            default:    s_addr <= addr_t'($urandom());                                      // random
            endcase
            s_clear <= &sel2;
            s_valid <= sel2[0];
        end
    end
    
endmodule

`default_nettype wire

// end of file
