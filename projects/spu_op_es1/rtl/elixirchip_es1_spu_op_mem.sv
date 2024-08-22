
`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_mem
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
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var addr_t          s_waddr ,   // 書き込みアドレス
            input   var data_t          s_wdata ,   // 書き込みデータ
            input   var logic           s_wvalid,   // 書き込み有効

            input   var addr_t          s_raddr ,   // 読み出しアドレス
            input   var logic           s_rvalid,   // 読み出し有効
            output  var data_t          m_rdata     // 読み出しデータ
        );

    // パラメータチェック
    initial begin
        assert ( WLATENCY >= 1 ) else begin $error("Illegal Latency"); end
        assert ( RLATENCY >= 1 ) else begin $error("Illegal Latency"); end
    end

    // 書き込みパイプライン遅延追加
    addr_t  wr_waddr    ;
    data_t  wr_wdata    ;
    logic   wr_wvalid   ;
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (WLATENCY - 1                   ),
                .DATA_BITS  ($bits({wr_waddr, wr_wdata})    ),
                .DEVICE     (DEVICE                         ),
                .SIMULATION (SIMULATION                     ),
                .DEBUG      (DEBUG                          )
            )
        u_additional_latency_write
            (
                .reset      (1'b0                           ),
                .clk        ,
                .cke        ,

                .s_data     ({s_waddr,  s_wdata}            ),
                .s_clear    (1'b0                           ),
                .s_valid    (1'b1                           ),

                .m_data     ({wr_waddr, wr_wdata}           )
            );
    elixirchip_es1_spu_ctl_valid
            #(
                .LATENCY    (WLATENCY - 1                   ),
                .DEVICE     (DEVICE                         ),
                .SIMULATION (SIMULATION                     ),
                .DEBUG      (DEBUG                          )
            )
        u_additional_latency_wvalid
            (
                .reset      ,
                .clk        ,
                .cke        ,

                .s_valid     (s_wvalid                      ),

                .m_valid     (wr_wvalid                     )
            );


    // メモリ
    (* ram_style = MEM_TYPE *)
    data_t  mem [0:MEM_SIZE-1];

    // 書き込みポート
    always_ff @( posedge clk ) begin
        if ( cke ) begin
            if ( wr_wvalid ) begin
                mem[wr_waddr] <= wr_wdata;
            end
        end
    end

    // 読み出しポート
    data_t  rd0_rdata;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            rd0_rdata <= 'x;
        end
        else if ( cke ) begin
            if ( s_rvalid ) begin
                rd0_rdata <= mem[s_raddr];
            end
        end
    end

    // パイプライン遅延追加
    elixirchip_es1_spu_op_nop
            #(
                .LATENCY    (RLATENCY - 1   ),
                .DATA_BITS  ($bits(m_rdata) ),
                .DEVICE     (DEVICE         ),
                .SIMULATION (SIMULATION     ),
                .DEBUG      (DEBUG          )
            )
        u_additional_latency_read
            (
                .reset      (1'b0           ),
                .clk        ,
                .cke        ,

                .s_data     (rd0_rdata      ),
                .s_clear    (1'b0           ),
                .s_valid    (1'b1           ),

                .m_data     (m_rdata        )
            );
    
endmodule


`default_nettype wire

