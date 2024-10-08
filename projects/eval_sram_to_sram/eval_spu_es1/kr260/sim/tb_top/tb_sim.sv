

`timescale 1ns / 1ps
`default_nettype none


module tb_sim();
    
    initial begin
        $dumpfile("tb_sim.vcd");
        $dumpvars(0, tb_sim);
        
    #10000000
        $display("timeout");
        $finish;
    end
    
    
    // ---------------------------------
    //  clock & reset
    // ---------------------------------

    localparam RATE100 = 1000.0/100.00;
    localparam RATE300 = 1000.0/300.00;
    localparam RATE500 = 1000.0/500.00;

    logic       reset = 1;
    initial #100 reset = 0;

    logic       clk300 = 1'b1;
    always #(RATE300/2.0) clk300 <= ~clk300;

    logic       clk500 = 1'b1;
    always #(RATE500/2.0) clk500 <= ~clk500;


    
    // ---------------------------------
    //  main
    // ---------------------------------
    

`ifdef __VERILATOR__
    localparam   DEVICE     = "RTL"             ;
`else
    localparam   DEVICE     = "ULTRASCALE_PLUS" ;
`endif    
    localparam   SIMULATION = "true"            ;
    localparam   DEBUG      = "false"           ;

    localparam  int     WB_ADR_WIDTH        = 37;
    localparam  int     WB_DAT_WIDTH        = 64;
    localparam  int     WB_SEL_WIDTH        = (WB_DAT_WIDTH / 8);
    
    parameter   type    wb_adr_t = logic [WB_ADR_WIDTH-1:0];
    parameter   type    wb_dat_t = logic [WB_DAT_WIDTH-1:0];


    logic   [WB_ADR_WIDTH-1:0]      wb_adr_i;
    logic   [WB_DAT_WIDTH-1:0]      wb_dat_o;
    logic   [WB_DAT_WIDTH-1:0]      wb_dat_i;
    logic   [WB_SEL_WIDTH-1:0]      wb_sel_i;
    logic                           wb_we_i;
    logic                           wb_stb_i;
    logic                           wb_ack_o;

    tb_main
            #(
                .WB_ADR_WIDTH   (WB_ADR_WIDTH   ),
                .WB_DAT_WIDTH   (WB_DAT_WIDTH   ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_tb_main
            (
                .reset,
                .clk300,
                .clk500,

                .s_wb_adr_i     (wb_adr_i       ),
                .s_wb_dat_o     (wb_dat_o       ),
                .s_wb_dat_i     (wb_dat_i       ),
                .s_wb_sel_i     (wb_sel_i       ),
                .s_wb_we_i      (wb_we_i        ),
                .s_wb_stb_i     (wb_stb_i       ),
                .s_wb_ack_o     (wb_ack_o       )
            );
    

    // ----------------------------------
    //  WISHBONE master
    // ----------------------------------

    jelly2_wb_accessor
            #(
                .WB_ADR_WIDTH   (WB_ADR_WIDTH),
                .WB_DAT_WIDTH   (WB_DAT_WIDTH)
            )
        u_wb_accessor
            (
                .m_wb_rst_i     (reset      ),
                .m_wb_clk_i     (clk300     ),
                .m_wb_adr_o     (wb_adr_i   ),
                .m_wb_dat_i     (wb_dat_o   ),
                .m_wb_dat_o     (wb_dat_i   ),
                .m_wb_sel_o     (wb_sel_i   ),
                .m_wb_we_o      (wb_we_i    ),
                .m_wb_stb_o     (wb_stb_i   ),
                .m_wb_ack_i     (wb_ack_o   )
            );
    
    localparam  wb_adr_t    ADR_REG  = wb_adr_t'(32'h00000000);
    localparam  wb_adr_t    ADR_MEM0 = wb_adr_t'(32'h00001000);
    localparam  wb_adr_t    ADR_MEM1 = wb_adr_t'(32'h00001400);
    localparam  wb_adr_t    ADR_MEM2 = wb_adr_t'(32'h00001800);
    localparam  wb_adr_t    ADR_MEM3 = wb_adr_t'(32'h00001c00);

    logic [7:0][7:0]    input_data0     [0:1023];   // 入力データ0
    logic [7:0][7:0]    input_data1     [0:1023];   // 入力データ1
    logic [7:0][7:0]    expect_data0    [0:1023];  // 期待値0
    logic [7:0][7:0]    expect_data1    [0:1023];  // 期待値1

    // データと期待値生成
    initial begin
        // 入力データ作成
        for ( int i = 0; i < 1024; i++ ) begin
            for ( int j = 0; j < 8; j++ ) begin
                input_data0[i][j]  = 8'($random());
                input_data1[i][j]  = 8'($random());
                expect_data0[i][j] = input_data0[i][j];
                expect_data1[i][j] = input_data1[i][j];
            end
        end
    
        // 期待値作成
        for ( int depth = 0; depth < 256; depth++ ) begin
            for ( int i = 0; i < 1024; i++ ) begin
                for ( int j = 0; j < 8; j++ ) begin
                    automatic logic [7:0] v0, v1;
                    v0 = expect_data0[i][j] * expect_data1[i][j];
                    v1 = expect_data0[i][j] + expect_data1[i][j];
                    expect_data0[i][j] = v0;
                    expect_data1[i][j] = v1;
                end
            end
        end
    end


    initial begin
        automatic logic [WB_DAT_WIDTH-1:0] dat;
        // リセット解除待ち
    #1000;

        // メモリ読み書きテスト
        $display("mem read/write test");
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(0), 64'h0706050403020100, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(1), 64'h0f0e0d0c0b0a0908, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(2), 64'h1716151413121110, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(3), 64'h1f1e1d1c1b1a1918, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(4), 64'h2726252423222120, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(5), 64'h2f2e2d2c2b2a2928, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(6), 64'h3736353433323130, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(7), 64'h3f3e3d3c3b3a3938, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(8), 64'h4746454443424140, 8'hff);
        u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(9), 64'h4f4e4d4c4b4a4948, 8'hff);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h0000000000000011, 8'h01);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h0000000000002200, 8'h02);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h0000000000330000, 8'h04);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h0000000044000099, 8'h08);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h0000005500000099, 8'h10);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h0000660000000099, 8'h20);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h0077000000000099, 8'h40);
        u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(1), 64'h8800000000000099, 8'h80);
        u_wb_accessor.write(ADR_MEM2 + wb_adr_t'(0), 64'h0000000000003333, 8'hff);
        u_wb_accessor.write(ADR_MEM3 + wb_adr_t'(0), 64'h0000000000004444, 8'hff);

        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(0), dat); assert (dat == 64'h0706050403020100) else begin $error("mismatch"); $finish; end
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(1), dat); assert (dat == 64'h0f0e0d0c0b0a0908) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(2), dat); assert (dat == 64'h1716151413121110) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(3), dat); assert (dat == 64'h1f1e1d1c1b1a1918) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(4), dat); assert (dat == 64'h2726252423222120) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(5), dat); assert (dat == 64'h2f2e2d2c2b2a2928) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(6), dat); assert (dat == 64'h3736353433323130) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(7), dat); assert (dat == 64'h3f3e3d3c3b3a3938) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(8), dat); assert (dat == 64'h4746454443424140) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM0 + wb_adr_t'(9), dat); assert (dat == 64'h4f4e4d4c4b4a4948) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM1 + wb_adr_t'(1), dat); assert (dat == 64'h8877665544332211) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM2 + wb_adr_t'(0), dat); assert (dat == 64'h0000000000003333) else begin $error("mismatch"); $finish; end;
        u_wb_accessor.read(ADR_MEM3 + wb_adr_t'(0), dat); assert (dat == 64'h0000000000004444) else begin $error("mismatch"); $finish; end;

        // 演算テスト
        for ( int i = 0; i < 1024; i++ ) begin
            u_wb_accessor.write(ADR_MEM0 + wb_adr_t'(i), input_data0[i], 8'hff);
            u_wb_accessor.write(ADR_MEM1 + wb_adr_t'(i), input_data1[i], 8'hff);
        end

        // start
        $display("start");
        u_wb_accessor.write(ADR_REG + 0, 64'h1, 8'hff);

        // wait for done
        $display("wait for done");
        do begin
            #100;
            u_wb_accessor.read(ADR_REG + 1, dat);
        end while ( dat == 0 );
        $display("done");
        u_wb_accessor.write(ADR_REG + 1, 64'h0, 8'hff);

        // read
        for ( int i = 0; i < 1024; i++ ) begin
            u_wb_accessor.read(ADR_MEM2 + wb_adr_t'(i), dat);
            $display("mem2[%d] = %h (expect:%h)", i, dat, expect_data0[i]);
            assert (dat == expect_data0[i]) else begin $error("mismatch"); $finish; end;

            u_wb_accessor.read(ADR_MEM3 + wb_adr_t'(i), dat);
            $display("mem3[%d] = %h (expect:%h)", i, dat, expect_data1[i]);
            assert (dat == expect_data1[i]) else begin $error("mismatch"); $finish; end;
        end

    #10000;
        $display("end");
        $finish;
    end
    
endmodule


`default_nettype wire


// end of file
