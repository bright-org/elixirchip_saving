

`timescale 1ns / 1ps
`default_nettype none


module sva_elixirchip_es1_spu_op_reg
        #(
            parameter   int     LATENCY    = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA = '0                     ,   // m_data クリア値
            parameter           DEVICE     = "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var data_t          s_data  ,   // 入力データ
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 入力有効

            input   var data_t          m_data      // 出力データ
        );

    // 期待値生成
    data_t      s_expected_data;
    logic       s_expected_valid;
    logic       s_expected_init  = 1'b0;
    always_ff @(posedge clk) begin
        if ( cke ) begin
            if ( s_clear ) begin
                s_expected_data  <= CLEAR_DATA;
                s_expected_init  <= 1'b1;
            end
            else if ( s_valid ) begin
                s_expected_data <= s_data;
                s_expected_init <= 1'b1;
            end
        end
    end
    always_ff @(posedge clk) begin
        if ( cke ) begin
            s_expected_valid <= s_valid;
        end
    end

    // 期待値を遅延させる
    data_t      m_expected_data;
    logic       m_expected_valid;
    logic       m_expected_init;
    expected_delay
            #(
                .LATENCY        (LATENCY - 1        ),
                .EXPECTED_BITS  ($bits(m_data) + 1  )
            )
        u_expected_delay
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         ({s_expected_data, s_expected_valid}),
                .s_valid        (s_expected_init   ),
                
                .m_data         ({m_expected_data, m_expected_valid}),
                .m_valid        (m_expected_init   )
            );



    // valid の unknown は許容しない
    property p_valid_unknown();
        @(posedge (clk & cke)) disable iff ( reset )
        !m_expected_init |-> !$isunknown(s_valid);
    endproperty
    sva_valid_unknown : assert property(p_valid_unknown) else begin
        $error("%t : ERROR valid_unknown", $time);
        $finish;
    end

    property p_m_data();
        @(posedge (clk & cke)) disable iff ( reset )
        m_expected_valid |-> m_data === m_expected_data;
    endproperty
    sva_m_data : assert property(p_m_data) else begin
        $error("%t : ERROR m_data=%x (expected:%x)", $time, m_data, m_expected_data);
        $finish;
    end

    property p_stable();
        @(posedge (clk & cke)) disable iff ( reset )
        !m_expected_valid && m_expected_init |-> $stable(m_data);
    endproperty
    sva_stable : assert property(p_stable) else begin
        $error("%m %t : ERROR : m_data is changed while non-valid", $time);
        $display("LATENCY=%0d DATA_BITS=%0d", LATENCY, $bits(data_t));
        $finish(1);
    end

    initial begin
        $display("LATENCY=%0d DATA_BITS=%0d", LATENCY, $bits(data_t));
    end

endmodule


`default_nettype wire

// end of file
