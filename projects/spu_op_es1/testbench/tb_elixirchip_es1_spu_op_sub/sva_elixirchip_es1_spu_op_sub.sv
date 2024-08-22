

`timescale 1ns / 1ps
`default_nettype none


module sva_elixirchip_es1_spu_op_sub
        #(
            parameter   int     LATENCY     = 1                     ,   // レイテンシ指定
            parameter   int     DATA_BITS   = 8                     ,   // データ幅指定
            parameter   type    data_t      = logic [DATA_BITS-1:0] ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA  = '0                    ,   // m_data クリア値
            parameter   logic   CLEAR_CARRY = '0                    ,   // m_carryクリア値
            parameter   logic   CLEAR_MSB_C = '0                    ,   // m_msb_c クリア値
            parameter   bit     IMMEDIATE_CARRY  = 1'b1                  ,   // s_carry が即値の場合に1にする
            parameter   bit     IMMEDIATE_DATA0  = 1'b0                  ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1  = 1'b0                  ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE      = "RTL"                 ,   // デバイス名
            parameter           SIMULATION  = "false"               ,   // シミュレーション
            parameter           DEBUG       = "false"                   // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk     ,   // クロック
            input   var logic           cke     ,   // クロックイネーブル

            input   var logic           s_carry ,   // キャリー入力
            input   var data_t          s_data0 ,   // 入力データ0
            input   var data_t          s_data1 ,   // 入力データ1
            input   var logic           s_clear ,   // クリア
            input   var logic           s_valid ,   // 信号有効

            input   var data_t          m_data  ,   // 出力データ
            input   var logic           m_msb_c ,   // MSBキャリー出力
            input   var logic           m_carry     // キャリー出力
        );

    data_t          s_data1_n;
    assign s_data1_n = ~s_data1;
    
    // 期待値生成
    data_t      s_expected_data;
    logic       s_expected_msb_c;
    logic       s_expected_carry;
    logic       s_expected_valid;

    /* verilator lint_off SELRANGE */
    always_comb begin
        {s_expected_carry, s_expected_data} = s_data0 + s_data1_n + data_t'(s_carry);
        if ( DATA_BITS > 1 ) begin
            s_expected_msb_c = 1'(({1'b0, s_data0[$bits(s_data0)-2:0]} + {1'b0, s_data1_n[$bits(s_data1_n)-2:0]} + {1'b0, data_t'(s_carry)}) >> ($bits(data_t)-1));
        end
        else begin
            s_expected_msb_c = s_carry;
        end
        if ( LATENCY > 0 && s_clear ) begin
            s_expected_data  = CLEAR_DATA;
            s_expected_carry = CLEAR_CARRY;
            s_expected_msb_c = CLEAR_MSB_C;
        end
    end
    /* verilator lint_on SELRANGE */

    assign s_expected_valid = s_valid || s_clear || LATENCY == 0;


    // 期待値を遅延させる
    data_t      m_expected_data;
    logic       m_expected_msb_c;
    logic       m_expected_carry;
    logic       m_expected_valid;
    expected_delay
            #(
                .LATENCY        (LATENCY                                                        ),
                .EXPECTED_BITS  ($bits({m_expected_carry, m_expected_msb_c, m_expected_data})   )
            )
        u_expected_delay
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         ({s_expected_carry, s_expected_msb_c, s_expected_data}          ),
                .s_valid        (s_expected_valid                                               ),
                
                .m_data         ({m_expected_carry, m_expected_msb_c, m_expected_data}          ),
                .m_valid        (m_expected_valid                                               )
            );


    // assertion
    property p_result();
        @(posedge (clk & cke)) disable iff ( reset )
        m_expected_valid |-> m_carry == m_expected_carry && m_msb_c == m_expected_msb_c && m_data == m_expected_data;
    endproperty
    sva_result : assert property(p_result) else begin
        $error("%t : ERROR : m_carry=%b (expected: %b) m_msb_c=%b (expected:%b) m_data=%x (expected : %x)", $time, m_carry, m_expected_carry, m_msb_c, m_expected_msb_c, m_data, m_expected_data);
        $finish(1);
    end
    
    property p_stable();
        @(posedge (clk & cke)) disable iff ( reset )
        !m_expected_valid |-> $stable(m_data);
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
