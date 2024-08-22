

`timescale 1ns / 1ps
`default_nettype none


module sva_elixirchip_es1_spu_op_mul
        #(
            parameter   int         LATENCY      = 3                                ,   // レイテンシ指定
            parameter   int         S_DATA0_BITS = 8                                ,   // s_data0 幅指定
            parameter   type        s_data0_t    = logic signed [S_DATA0_BITS-1:0]  ,   // s_data0 型指定(オプション)
            parameter   int         S_DATA1_BITS = 8                                ,   // s_data1 幅指定
            parameter   type        s_data1_t    = logic signed [S_DATA1_BITS-1:0]  ,   // s_data1 型指定(オプション)
            parameter   int         M_DATA_BITS  = 64                               ,   // m_data 幅指定
            parameter   type        m_data_t     = logic signed [M_DATA_BITS-1:0]   ,   // m_data 型指定(オプション)
            parameter   int         DATA_SHIFT   = 0                                ,   // 出力前の右シフト量
            parameter   m_data_t    CLEAR_DATA   = 'x                               ,   // m_data クリア値
            parameter   bit         IMMEDIATE_DATA0   = 1'b0                             ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit         IMMEDIATE_DATA1   = 1'b0                             ,   // s_data1 が即値の場合に1にする
            parameter               DEVICE       = "RTL"                            ,   // デバイス名
            parameter               SIMULATION   = "false"                          ,   // シミュレーション
            parameter               DEBUG        = "false"                              // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var s_data0_t       s_data0 ,   // 入力データ0
            input   var s_data1_t       s_data1 ,   // 入力データ1
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            input   var m_data_t        m_data     // 出力データ
        );

    localparam  int     MUL_BITS = $bits(s_data0_t) + $bits(s_data1_t);
    localparam  type    mul_t    = logic signed    [MUL_BITS-1:0];

    // 期待値生成
    m_data_t    s_expected_data;
    logic       s_expected_valid;
    always_comb begin
        s_expected_data  = m_data_t'((mul_t'(s_data0) * mul_t'(s_data1)) >>> DATA_SHIFT);
        if ( LATENCY > 0 && s_clear ) begin
            s_expected_data  = CLEAR_DATA;
        end
    end
    assign s_expected_valid = s_valid || s_clear || LATENCY == 0;


    // 期待値を遅延させる
    m_data_t    m_expected_data;
    logic       m_expected_valid;
    expected_delay
            #(
                .LATENCY        (LATENCY                    ),
                .EXPECTED_BITS  ($bits({m_expected_data})   )
            )
        u_expected_delay
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         (s_expected_data            ),
                .s_valid        (s_expected_valid           ),
                
                .m_data         (m_expected_data            ),
                .m_valid        (m_expected_valid           )
            );


    // assertion
    property p_result();
        @(posedge (clk & cke)) disable iff ( reset )
        m_expected_valid |-> m_data == m_expected_data;
    endproperty
    sva_result : assert property(p_result) else begin
        $error("%t : ERROR : m_data=%x (expected : %x)", $time, m_data, m_expected_data);
        $finish(1);
    end

    property p_stable();
        @(posedge (clk & cke)) disable iff ( reset )
        !m_expected_valid |-> $stable(m_data);
    endproperty
    sva_stable : assert property(p_stable) else begin
        $error("%m %t : ERROR : m_data is changed while non-valid", $time);
        $finish(1);
    end

    initial begin
        $display("LATENCY=%0d S_DATA0_BITS=%0d S_DATA1_BITS=%0d M_DATA_BITS=%0d", LATENCY, $bits(s_data0_t), $bits(s_data1_t), $bits(m_data_t));
    end

endmodule


`default_nettype wire

// end of file
