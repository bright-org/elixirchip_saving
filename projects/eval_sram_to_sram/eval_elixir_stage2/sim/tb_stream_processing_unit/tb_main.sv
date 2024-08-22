

`timescale 1ns / 1ps
`default_nettype none


// 以降は Verilator で C++ のテストドライバも使えるように時間待ちを書かない
module tb_main
        (
            input   var logic                       reset   ,
            input   var logic                       clk     
        );

    // -----------------------------------------
    //  stream_processing_unit
    // -----------------------------------------

    logic               cke     ;   // クロックイネーブル

    logic   [63:0]      s_data0 ;   // source0
    logic   [63:0]      s_data1 ;   // source1
    logic               s_valid ;   // データ有効

    logic   [63:0]      m_data0 ;   // destination0
    logic   [63:0]      m_data1 ;   // destination1
    logic               m_valid ;   // データ有効

    stream_processing_unit
        u_stream_processing_unit
            (
                .reset  ,
                .clk    ,
                .cke    ,

                .s_data0,
                .s_data1,
                .s_valid,

                .m_data0,
                .m_data1,
                .m_valid 
            );

    // -----------------------------------------
    //  testbench
    // -----------------------------------------

    assign cke = 1'b1;

    // 入力生成
    logic   [63:0]      data0 ;
    logic   [63:0]      data1 ;
    int                 counter;
    always_ff @(posedge clk) begin
        if ( reset ) begin
            data0   <= 'x;
            data1   <= 'x;
            counter <= '0;
        end
        else if ( cke ) begin
            for ( int i = 0; i < 8; i++ ) begin
                data0[i*8 +: 8] <= 8'($urandom());
                data1[i*8 +: 8] <= 8'($urandom());
            end
            counter <= counter + 1;
        end
    end

    assign s_data0 = s_valid ? data0 : 'x;
    assign s_data1 = s_valid ? data1 : 'x;
    assign s_valid = counter >= 100 && counter < 200;


    // 期待値
    logic   [63:0]      exp_data0;
    always_comb begin
        for ( int i = 0; i < 8; i++ ) begin
            exp_data0[i*8 +: 8] = (s_data0[i*8 +: 8] + 8'd2) - (s_data1[i*8 +: 8] + 8'd1);
        end
    end

    // 期待値キューイング
    logic   [63:0]      exp_que[$];
    always_ff @(posedge clk) begin
        if ( !reset && cke ) begin
            if ( s_valid ) begin
                exp_que.push_back(exp_data0);
            end
        end
    end

    // 期待値比較
    always_ff @(posedge clk) begin
        if ( !reset && cke ) begin
            if ( m_valid ) begin
                if ( m_data0 != exp_que.pop_front() ) begin
                    $error("NG");
                    $finish;
                end
                if ( exp_que.size() == 0 ) begin
                    $display("OK");
                    $finish;
                end
            end
        end
    end



endmodule


`default_nettype wire


// end of file
