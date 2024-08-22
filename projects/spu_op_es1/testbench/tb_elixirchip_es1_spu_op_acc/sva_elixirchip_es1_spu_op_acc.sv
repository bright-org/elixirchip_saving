

`timescale 1ns / 1ps
`default_nettype none


module sva_elixirchip_es1_spu_op_acc
        #(
            parameter   int         LATENCY      = 1                                ,   // レイテンシ指定
            parameter   int         S_DATA_BITS  = 8                                ,   // s_data0 幅指定
            parameter   type        s_data_t     = logic    [S_DATA_BITS-1:0]       ,   // s_data0 型指定(オプション)
            parameter   int         M_DATA_BITS  = 8                                ,   // m_data 幅指定
            parameter   type        m_data_t     = logic    [M_DATA_BITS-1:0]       ,   // m_data 型指定(オプション)
            parameter   m_data_t    CLEAR_DATA   = 'x                               ,   // m_data クリア値
            parameter   logic       CLEAR_CARRY  = 'x                               ,   // m_carryクリア値
            parameter   bit         IMMEDIATE_DATA    = 1'b0                             ,   // s_data0 が即値の場合に1にする(オプション)
            parameter               DEVICE       = "RTL"                            ,   // デバイス名
            parameter               SIMULATION   = "false"                          ,   // シミュレーション
            parameter               DEBUG        = "false"                              // デバッグ
        )
        (
            input   var logic           reset       ,   // 同期リセット(制論理)
            input   var logic           clk         ,   // クロック
            input   var logic           cke         ,   // クロックイネーブル

            input   var logic           s_sub       ,   // 1の時にアキュミュレータの演算を加算ではなく減算にする
            input   var logic           s_carry     ,   // キャリー入力 (sub 時は 0 でボローあり)
            input   var s_data_t        s_data      ,   // 入力データ
            input   var logic           s_clear     ,   // クリア
            input   var logic           s_valid     ,   // 1の時有効データ

            input   var logic           m_carry     ,   // キャリー
            input   var m_data_t        m_data          // 出力データ
        );

    // 期待値生成
    logic       s_expected_carry;
    m_data_t    s_expected_data;
    logic       s_expected_valid;
    always_ff @(posedge clk) begin
        if ( reset || s_clear ) begin
            s_expected_data  <= CLEAR_DATA;
            s_expected_carry <= CLEAR_CARRY;
            s_expected_valid <= 1'b0;
        end
        else if ( cke ) begin
            if ( s_valid ) begin
                if ( s_sub ) begin
                    {s_expected_carry, s_expected_data} <= {1'b0, s_expected_data} + {1'b0, ~m_data_t'(s_data)} + {1'b0, m_data_t'(s_carry)};
                end
                else begin
                    {s_expected_carry, s_expected_data} <= {1'b0, s_expected_data} + {1'b0,  m_data_t'(s_data)} + {1'b0, m_data_t'(s_carry)};
                end
            end
        end
        if ( s_clear ) begin
            s_expected_valid <= 1'b1;
        end
    end

    // 期待値を遅延させる
    logic       m_expected_carry    ;
    m_data_t    m_expected_data     ;
    logic       m_expected_valid    ;
    expected_delay
            #(
                .LATENCY        (LATENCY - 1                            ),
                .EXPECTED_BITS  ($bits({m_carry, m_data})               )
            )
        u_expected_delay
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         ({s_expected_carry, s_expected_data}    ),
                .s_valid        (s_expected_valid                       ),
                
                .m_data         ({m_expected_carry, m_expected_data}    ),
                .m_valid        (m_expected_valid                       )
            );


    // valid と s_clear の unknown は許容しない
    property p_valid_unknown();
        @(posedge (clk & cke)) disable iff ( reset )
        (1) |-> !$isunknown(s_valid) && !$isunknown(s_clear);
    endproperty
    sva_valid_unknown : assert property(p_valid_unknown) else begin
        $error("%t : ERROR valid_unknown", $time);
        $finish;
    end

    // valid 有効の時他の信号も有効であること
    property p_other_unknown();
        @(posedge (clk & cke)) disable iff ( reset )
        s_valid |-> !$isunknown(s_sub) && !$isunknown(s_data);
    endproperty
    sva_other_unknown : assert property(p_other_unknown) else begin
        $error("%t : ERROR other_unknown", $time);
        $finish;
    end

    property p_m_carry();
        @(posedge (clk & cke)) disable iff ( reset )
        m_expected_valid |-> m_carry == m_expected_carry;
    endproperty
    sva_m_carry : assert property(p_m_carry) else begin
        $error("%t : ERROR m_carry=%x (expected:%x)", $time, m_carry, m_expected_carry);
        $finish;
    end

    property p_m_data();
        @(posedge (clk & cke)) disable iff ( reset )
        m_expected_valid |-> m_data == m_expected_data;
    endproperty
    sva_m_data : assert property(p_m_data) else begin
        $error("%t : ERROR m_data=%x (expected:%x)", $time, m_data, m_expected_data);
        $finish;
    end

    initial begin
        $display("LATENCY=%0d S_DATA_BITS=%0d, M_DATA_BITS=%0d", LATENCY, $bits(s_data_t), $bits(m_data_t));
    end


endmodule


`default_nettype wire

// end of file
