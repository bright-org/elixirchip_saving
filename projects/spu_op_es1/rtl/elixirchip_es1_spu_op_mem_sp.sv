
`timescale 1ns / 1ps
`default_nettype none

module elixirchip_es1_spu_op_mem_sp
        #(
            parameter   int     LATENCY    = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   int     ADDR_BITS  = 8                      ,   // アドレス幅指定
            parameter   type    addr_t     = logic [ADDR_BITS-1:0]  ,   // アドレス型指定(オプション)
            parameter   int     MEM_SIZE   = 2 ** ADDR_BITS         ,   // メモリサイズ
            parameter           MEM_TYPE   = "distributed"          ,   // メモリタイプ("block" or "distributed")      
            parameter           DEVICE     = "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var addr_t          s_addr  ,   // アドレス
            input   var data_t          s_wdata ,   // 書き込みデータ
            input   var logic           s_wvalid,   // 書き込み有効

            output  var data_t          m_rdata     // 読み出しデータ(書き込みしない時のみ)
        );


    // パラメータチェック
    initial begin
        assert ( LATENCY >= 1 ) else begin $error("Illegal Latency"); end
    end

    // メモリ
    (* ram_style = MEM_TYPE *)
    data_t  mem [0:MEM_SIZE-1];

    // 演算
    data_t  st0_rdata;
    always_ff @( posedge clk ) begin
        if ( cke ) begin
            if ( s_wvalid ) begin
                mem[s_addr] <= s_wdata;
            end
            else begin
                st0_rdata <= mem[s_addr];
            end
        end
    end

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (LATENCY - 1    ),
                .DATA_BITS  ($bits(m_rdata) ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          )
            )
        u_additional_latency
            (
                .reset      (1'b0           ),
                .clk        ,
                .cke        ,

                .s_data     (st0_rdata      ),
                .s_clear    (1'b0           ),
                .s_valid    (1'b1           ),

                .m_data     (m_rdata        )
            );
    
endmodule


`default_nettype wire

