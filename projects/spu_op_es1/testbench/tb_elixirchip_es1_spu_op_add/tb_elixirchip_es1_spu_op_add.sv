

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_add
        #(
            parameter   int     LATENCY     = 1                     ,   // レイテンシ指定
            parameter   int     DATA_BITS   = 8                     ,   // データ幅指定
            parameter   type    data_t      = logic [DATA_BITS-1:0] ,   // データ型指定(オプション)
            parameter   bit     IMMEDIATE_CARRY  = 1'b1                  ,   // s_carry が即値の場合に1にする
            parameter   bit     IMMEDIATE_DATA0  = 1'b0                  ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1  = 1'b0                  ,   // s_data1 が即値の場合に1にする
            parameter   data_t  CLEAR_DATA  = '1                    ,   // m_data クリア値
            parameter   logic   CLEAR_CARRY = '1                    ,   // m_carryクリア値
            parameter   logic   CLEAR_MSB_C = '0                    ,   // m_msb_c クリア値
            parameter           DEVICE      = "RTL"                 ,   // デバイス名
            parameter           SIMULATION  = "false"               ,   // シミュレーション
            parameter           DEBUG       = "false"                   // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk         // クロック
        );

    // ランダムにCKEを下げる
    logic           cke     ;
    always_ff @( negedge clk ) begin
        cke <= ($urandom_range(0, 9) != 0);
    end

    logic           s_carry ;
    data_t          s_data0 ;
    data_t          s_data1 ;
    logic           s_clear ;
    logic           s_valid ;
    logic           m_carry ;
    logic           m_msb_c ;
    data_t          m_data  ;

    elixirchip_es1_spu_op_add
            #(
                .LATENCY        (LATENCY    ),
                .DATA_BITS      (DATA_BITS  ),
                .data_t         (data_t     ),
                .IMMEDIATE_CARRY     (1'b1       ),
                .IMMEDIATE_DATA0     (1'b0       ),
                .IMMEDIATE_DATA1     (1'b0       ),
                .CLEAR_DATA     (CLEAR_DATA ),
                .CLEAR_CARRY    (CLEAR_CARRY),
                .CLEAR_MSB_C    (CLEAR_MSB_C),
                .DEVICE         (DEVICE     ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      ) 
            )
        u_elixirchip_es1_spu_op_add
            (
                .reset   ,
                .clk     ,
                .cke     ,

                .s_carry ,
                .s_data0 ,
                .s_data1 ,
                .s_clear ,
                .s_valid ,

                .m_carry ,
                .m_msb_c ,
                .m_data   
            );


    // -----------------------------------------
    //  testbench
    // -----------------------------------------

    int     cycle = 0;
    always_ff @(posedge clk) begin
        if ( reset ) begin
            cycle <= 0;
        end
        else if ( cke ) begin
            cycle <= cycle + 1;
        end
    end

    int             sel0;
    int             sel1;
    logic   [1:0]   flg ;
    always_ff @(posedge clk) begin
        if ( cycle < 2048 ) begin
            // 前半は網羅テスト
            sel0    <= int'(cycle[2:0]);
            sel1    <= int'(cycle[5:3]);
            flg     <=   2'(cycle[7:6]);
            s_carry <= cycle[8];
        end
        else begin
            // 後半はランダムテスト
            sel0    <= $urandom_range(0, 7);
            sel1    <= $urandom_range(0, 7);
            flg     <= 2'($urandom_range(0, 3));
            s_carry <= 1'($urandom_range(0, 1));
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_data0 <= '0;
            s_data1 <= '0;
            s_clear <= 1'b0;
            s_valid <= 1'b0;
        end
        else if ( cke ) begin
            case ( sel0 )
            0:          s_data0 <= '0;                                                      // unsigned min ALL-0
            1:          s_data0 <= '1;                                                      // unsigned max ALL-1
            3:          s_data0 <=  data_t'(2**($bits(s_data0)-1)  );                       // signed min
            4:          s_data0 <=  data_t'(2**($bits(s_data0)-1)-1);                       // signed max
            5:          s_data0 <=  (data_t'(1) << $urandom_range(0, $bits(s_data0)-1));    // one-hot
            6:          s_data0 <= ~(data_t'(1) << $urandom_range(0, $bits(s_data0)-1));    // one-hot(neg)
            default:    s_data0 <= data_t'($urandom());                                     // random
            endcase

            case ( sel1 )
            0:          s_data1 <= '0;                                                      // unsigned min ALL-0
            1:          s_data1 <= '1;                                                      // unsigned max ALL-1
            3:          s_data1 <=  data_t'(2**($bits(s_data1)-1)  );                       // signed min
            4:          s_data1 <=  data_t'(2**($bits(s_data1)-1)-1);                       // signed max
            5:          s_data1 <=  (data_t'(1) << $urandom_range(0, $bits(s_data1)-1));    // one-hot
            6:          s_data1 <= ~(data_t'(1) << $urandom_range(0, $bits(s_data1)-1));    // one-hot(neg)
            default:    s_data1 <= data_t'($urandom());                                     // random
            endcase
            s_clear <= &flg;
            s_valid <= flg[0];
        end
    end
    
    
endmodule


`default_nettype wire


// end of file
