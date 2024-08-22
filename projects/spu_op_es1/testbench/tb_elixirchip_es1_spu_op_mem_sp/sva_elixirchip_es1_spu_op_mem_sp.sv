

`timescale 1ns / 1ps
`default_nettype none


module sva_elixirchip_es1_spu_op_mem_sp
        #(
            parameter   int     LATENCY    = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   int     ADDR_BITS  = 8                      ,   // アドレス幅指定
            parameter   type    addr_t     = logic [ADDR_BITS-1:0]  ,   // アドレス型指定(オプション)
            parameter   int     MEM_SIZE   = 2 ** ADDR_BITS         ,   // メモリサイズ
            parameter           MEM_TYPE   = "block"                ,   // メモリタイプ("block" or "distributed")      
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

            input   var data_t          m_rdata     // 読み出しデータ(書き込みしない時のみ)
        );

    // 期待値生成
    data_t  mem     [0:MEM_SIZE-1];    
    logic   mval    [0:MEM_SIZE-1] = '{default:1'b0};

    data_t      s_expected_data;
    logic       s_expected_valid;
    always_ff @(posedge clk) begin
        if (reset) begin
            s_expected_data  <= 'x;
            s_expected_valid <= 1'b0;
        end
        else if ( cke ) begin
            s_expected_valid <= ~s_wvalid && !$isunknown(s_addr) && mval[s_addr];
            if ( s_wvalid ) begin
                mem[s_addr]  <= s_wdata;
                mval[s_addr] <= 1'b1;
            end
            else begin
                s_expected_data <= mem[s_addr];
            end
        end
    end

    // 期待値を遅延させる
    data_t      m_expected_data;
    logic       m_expected_valid;
    expected_delay
            #(
                .LATENCY        (LATENCY - 1        ),
                .EXPECTED_BITS  ($bits(data_t)      )
            )
        u_expected_delay
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         (s_expected_data      ),
                .s_valid        (s_expected_valid     ),
                
                .m_data         (m_expected_data      ),
                .m_valid        (m_expected_valid     )
            );



    // valid の unknown は許容しない
    property p_valid_unknown();
        @(posedge (clk & cke)) disable iff ( reset )
        (1) |-> !$isunknown(s_wvalid);
    endproperty
    sva_valid_unknown : assert property(p_valid_unknown) else begin
        $error("%t : ERROR valid_unknown", $time);
        $finish;
    end

    // valid 有効の時他の信号も有効であること
    property p_other_unknown();
        @(posedge (clk & cke)) disable iff ( reset )
        s_wvalid |-> !$isunknown(s_addr) && !$isunknown(s_wdata);
    endproperty
    sva_other_unknown : assert property(p_other_unknown) else begin
        $error("%t : ERROR other_unknown", $time);
        $finish;
    end

    property p_m_data();
        @(posedge (clk & cke)) disable iff ( reset )
        m_expected_valid |-> m_rdata == m_expected_data;
    endproperty
    sva_m_data : assert property(p_m_data) else begin
        $error("%t : ERROR m_data=%x (expected:%x)", $time, m_rdata, m_expected_data);
        $finish;
    end


    initial begin
        $display("LATENCY=%0d DATA_BITS=%0d", LATENCY, $bits(data_t));
    end


endmodule


`default_nettype wire

// end of file
