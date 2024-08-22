

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_mem
        #(
            parameter   int     WLATENCY   = 1                      ,   // 書き込みレイテンシ指定
            parameter   int     RLATENCY   = 1                      ,   // 読み出しレイテンシ指定
            parameter   int     DATA_BITS  = 8                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   int     ADDR_BITS  = 9                      ,   // アドレス幅指定
            parameter   type    addr_t     = logic [ADDR_BITS-1:0]  ,   // アドレス型指定(オプション)
            parameter   int     MEM_SIZE   = 2 ** ADDR_BITS         ,   // メモリサイズ
            parameter           MEM_TYPE   = "distributed"          ,   // メモリタイプ("block" or "distributed")      
            parameter           DEVICE     = "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk         // クロック
        );

    // ランダムにCKEを下げる
    logic           cke     = 1'b1;
    always_ff @( negedge clk ) begin
        cke <= $urandom_range(0, 9) != 0;
    end

    addr_t          s_waddr ;   // 書き込みアドレス
    data_t          s_wdata ;   // 書き込みデータ
    logic           s_wvalid;   // 書き込み有効

    addr_t          s_raddr ;   // 読み出しアドレス
    logic           s_rvalid;   // 読み出し有効
    data_t          m_rdata ;   // 読み出しデータ
 
    elixirchip_es1_spu_op_mem
            #(
                .WLATENCY       (WLATENCY       ),
                .RLATENCY       (RLATENCY       ),
                .DATA_BITS      (DATA_BITS      ),
                .ADDR_BITS      (ADDR_BITS      ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_mem
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_waddr        ,
                .s_wdata        ,
                .s_wvalid       ,

                .s_raddr        ,
                .s_rvalid       ,
                .m_rdata        
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

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_waddr  <= '0;
            s_wdata  <= '0;
            s_wvalid <= '0;
            s_raddr  <= '0;
            s_rvalid <= '0;
        end
        else if ( cke ) begin
            s_waddr  <= addr_t'($urandom());
            s_wdata  <= data_t'($urandom());
            s_wvalid <= 1'($urandom_range(0, 1));
            s_raddr  <= addr_t'($urandom());
            s_rvalid <= 1'($urandom_range(0, 1));
        end
    end

endmodule


`default_nettype wire


// end of file
