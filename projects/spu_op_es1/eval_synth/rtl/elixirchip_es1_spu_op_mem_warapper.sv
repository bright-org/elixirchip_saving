

`timescale 1ns / 1ps
`default_nettype none


module elixirchip_es1_spu_op_mem_warapper
        #(
            parameter   int     WLATENCY   = 1                      ,   // 書き込みレイテンシ指定
            parameter   int     RLATENCY   = 2                      ,   // 読み出しレイテンシ指定
            parameter   int     DATA_BITS  = 18                     ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   int     ADDR_BITS  = 10                     ,   // アドレス幅指定
            parameter   type    addr_t     = logic [ADDR_BITS-1:0]  ,   // アドレス型指定(オプション)
            parameter   int     MEM_SIZE   = 2 ** ADDR_BITS         ,   // メモリサイズ
            parameter           MEM_TYPE   = "block"                ,   // メモリタイプ("block" or "distributed")      
            parameter           DEVICE     = "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,
            input   var logic           clk     ,
            input   var logic           cke     ,
            
            input   var logic           din     ,
            output  var logic           dout    
        );
    

     (* DONT_TOUCH = "true" *)  addr_t  s_waddr ;   // 書き込みアドレス
     (* DONT_TOUCH = "true" *)  data_t  s_wdata ;   // 書き込みデータ
     (* DONT_TOUCH = "true" *)  logic   s_wvalid;   // 書き込み有効
     (* DONT_TOUCH = "true" *)  addr_t  s_raddr ;   // 読み出しアドレス
     (* DONT_TOUCH = "true" *)  logic   s_rvalid;   // 読み出し有効
                                data_t  m_rdata ;   // 読み出しデータ
                                logic   dummy   ;  
 
    elixirchip_es1_spu_op_mem
            #(
                .WLATENCY       (WLATENCY       ),
                .RLATENCY       (RLATENCY       ),
                .DATA_BITS      (DATA_BITS      ),
                .ADDR_BITS      (ADDR_BITS      ),
                .MEM_SIZE       (MEM_SIZE       ),
                .MEM_TYPE       (MEM_TYPE       ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_mem
            (
                .reset          ,
                .clk            ,
                .cke            (1'b1),

                .s_waddr        ,
                .s_wdata        ,
                .s_wvalid       ,

                .s_raddr        ,
                .s_rvalid       ,
                .m_rdata        
            );

    always_ff @( posedge clk ) begin
        if ( cke ) begin
           {dummy, s_waddr, s_wdata, s_wvalid, s_raddr, s_rvalid} <= {s_waddr, s_wdata, s_wvalid, s_raddr, s_rvalid, din};
        end
    end

    assign dout = ^{m_rdata};

endmodule


`default_nettype wire


// end of file
