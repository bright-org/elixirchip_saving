

`timescale 1ns / 1ps
`default_nettype none


module sva_elixirchip_es1_spu_op_mac
        #(
            parameter   int     LATENCY      = 3                                ,   // レイテンシ指定
            parameter   int     S_DATA0_BITS = 8                                ,   // s_data0 幅指定
            parameter   type    s_data0_t    = logic signed [S_DATA0_BITS-1:0]  ,   // s_data0 型指定(オプション)
            parameter   int     S_DATA1_BITS = 9                                ,   // s_data1 幅指定
            parameter   type    s_data1_t    = logic signed [S_DATA1_BITS-1:0]  ,   // s_data1 型指定(オプション)
            parameter   int     M_DATA_BITS  = 10                               ,   // m_data 幅指定
            parameter   type    m_data_t     = logic signed [M_DATA_BITS-1:0]   ,   // m_data 型指定(オプション)
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                               ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                               ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE     = "RTL"                              ,   // デバイス名
            parameter           SIMULATION = "false"                            ,   // シミュレーション
            parameter           DEBUG      = "false"                                // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var logic           s_set   ,   // 1の時にアキュミュレータは積算せずに新しい値をセット
            input   var logic           s_sub   ,   // 1の時にアキュミュレータの演算を加算ではなく減算にする
            input   var s_data0_t       s_data0 ,   // 入力データ0
            input   var s_data1_t       s_data1 ,   // 入力データ1
            input   var logic           s_valid ,   // 1の時有効データ

            input   var m_data_t        m_data      // 出力データ
        );

    // 期待値生成
    m_data_t    s_expected_data;
    logic       s_expected_valid;
    always_ff @(posedge clk) begin
        if (reset) begin
            s_expected_data  <= 'x;
            s_expected_valid <= 1'b0;
        end
        else if ( cke ) begin
            if ( s_valid ) begin
                if (s_set) begin
                    s_expected_data <= m_data_t'(s_data0 * s_data1);
                end
                else begin
                    if ( s_sub ) begin
                        s_expected_data <= s_expected_data - m_data_t'(s_data0 * s_data1);
                    end
                    else begin
                        s_expected_data <= s_expected_data + m_data_t'(s_data0 * s_data1);
                    end
                end
            end
            if ( s_valid && s_set ) begin
                s_expected_valid <= 1'b1;
            end
        end
    end

    // 期待値を遅延させる
    m_data_t    m_expected_data;
    logic       m_expected_valid;
    expected_delay
            #(
                .LATENCY        (LATENCY - 1        ),
                .EXPECTED_BITS  ($bits(m_data)      )
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
        (1) |-> !$isunknown(s_valid);
    endproperty
    sva_valid_unknown : assert property(p_valid_unknown) else begin
        $error("%m %t : ERROR valid_unknown", $time);
        $finish;
    end

    // valid 有効の時他の信号も有効であること
    property p_other_unknown();
        @(posedge (clk & cke)) disable iff ( reset )
        s_valid |-> !$isunknown(s_set) && !$isunknown(s_sub) && !$isunknown(s_data0) && !$isunknown(s_data1);
    endproperty
    sva_other_unknown : assert property(p_other_unknown) else begin 
        $error("%m %t : ERROR other_unknown", $time);
        $finish;
    end

    property p_m_data();
        @(posedge (clk & cke)) disable iff ( reset )
        m_expected_valid |-> m_data == m_expected_data;
    endproperty
    sva_m_data : assert property(p_m_data) else begin 
        $error("%m %t : ERROR m_data=%x (expected:%x)", $time, m_data, m_expected_data);
        $finish;
    end

    /*
    // valid のない時出力は変化しない
    property p_valid();
        @(posedge (clk & cke)) disable iff ( reset )
        !s_valid |-> ##LATENCY $stable(m_data);
    endproperty
    sva_valid : assert property(p_valid) else begin
        $error("%t : ERROR valid : m_data=%x", $time, m_data);
        $finish;
    end

    // set でその値を設定
    property p_set();
        @(posedge (clk & cke)) disable iff ( reset )
        s_valid && s_set |-> ##LATENCY m_data == m_data_t'(($past(s_data0, LATENCY) * $past(s_data1, LATENCY)));
    endproperty
    sva_set : assert property(p_set) else begin
        $error("%t : ERROR set : m_data=%x cycle=%d", $time, m_data, cycle);
        $finish;
    end

    // 通常の積和
    property p_add();
        @(posedge (clk & cke)) disable iff ( reset )
        s_valid && !s_set && !s_sub |-> ##LATENCY m_data == m_data_t'($past(m_data, 1) + ($past(s_data0, LATENCY) * $past(s_data1, LATENCY)));
    endproperty
    sva_add : assert property(p_add) else begin
        $error("%t : ERROR add : m_data=%x cycle=%d", $time, m_data, cycle);
        $finish;
    end

    // 減算モード
    property p_sub();
        @(posedge (clk & cke)) disable iff ( reset )
        s_valid && !s_set && s_sub |-> ##LATENCY m_data == m_data_t'($past(m_data, 1) - $past(s_data0, LATENCY) * $past(s_data1, LATENCY));
    endproperty
    sva_sub : assert property(p_sub) else begin
        $error("%t : ERROR sub : m_data=%x", $time, m_data);
        $finish;
    end
    */


endmodule


`default_nettype wire

// end of file
