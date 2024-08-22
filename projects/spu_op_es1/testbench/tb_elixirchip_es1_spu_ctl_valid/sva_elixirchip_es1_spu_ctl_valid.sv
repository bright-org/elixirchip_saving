

`timescale 1ns / 1ps
`default_nettype none


module sva_elixirchip_es1_spu_ctl_valid
        #(
            parameter int       LATENCY   = 1           ,   // レイテンシ指定
            parameter           DEVICE     = "RTL"      ,   // デバイス名
            parameter           SIMULATION = "false"    ,   // シミュレーション
            parameter           DEBUG      = "false"        // デバッグ
        )
        (
            input   var logic       reset       ,
            input   var logic       clk         ,
            input   var logic       cke         ,

            input   var logic       s_valid     ,

            input   var logic       m_valid     
        );

    // 期待値生成
    logic       s_expected_valid;
    assign s_expected_valid = s_valid;


    // 期待値を遅延させる
    logic       m_expected_valid;
    expected_delay
            #(
                .LATENCY        (LATENCY                    ),
                .EXPECTED_BITS  (1                          )
            )
        u_expected_delay
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         (1'bx                       ),
                .s_valid        (s_expected_valid           ),
                
                .m_data         (                           ),
                .m_valid        (m_expected_valid           )
            );


    // assertion
    property p_result();
        @(posedge (clk & cke)) disable iff ( reset )
        1 |-> m_valid == m_expected_valid;
    endproperty
    sva_result : assert property(p_result) else begin
        $error("%t : ERROR : m_data=%x (expected : %x)", $time, m_valid, m_expected_valid);
        $finish(1);
    end
    
    initial begin
        $display("LATENCY=%0d", LATENCY);
    end

endmodule


`default_nettype wire

// end of file
