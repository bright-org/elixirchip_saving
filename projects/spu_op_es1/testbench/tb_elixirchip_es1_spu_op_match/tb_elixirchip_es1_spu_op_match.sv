

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_match
        #(
            parameter   int     LATENCY    = 1                              ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                              ,   // データ幅指定
            parameter   type    data_t     = logic signed [DATA_BITS-1:0]   ,   // データ型指定(オプション)
            parameter   logic   CLEAR_DATA = '1                             ,   // m_data クリア値
            parameter   bit     IMMEDIATE_DATA0 = 1'b0                           ,   // s_data0 が即値の場合に1にする(オプション)
            parameter   bit     IMMEDIATE_DATA1 = 1'b0                           ,   // s_data1 が即値の場合に1にする
            parameter           DEVICE     = "RTL"                          ,   // デバイス名
            parameter           SIMULATION = "false"                        ,   // シミュレーション
            parameter           DEBUG      = "false"                            // デバッグ
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

    data_t          s_data0 ;
    data_t          s_data1 ;
    logic           s_clear ;
    logic           s_valid ;
    logic           m_data  ;

    elixirchip_es1_spu_op_match
            #(
                .LATENCY        (LATENCY    ),
                .DATA_BITS      (DATA_BITS  ),
                .data_t         (data_t     ),
                .CLEAR_DATA     (CLEAR_DATA ),
                .IMMEDIATE_DATA0     (1'b0       ),
                .IMMEDIATE_DATA1     (1'b0       ),
                .DEVICE         (DEVICE     ),
                .SIMULATION     (SIMULATION ),
                .DEBUG          (DEBUG      ) 
            )
        u_elixirchip_es1_spu_op_match
            (
                .reset   ,
                .clk     ,
                .cke     ,

                .s_data0 ,
                .s_data1 ,
                .s_clear ,
                .s_valid ,

                .m_data   
            );


    // -----------------------------------------
    //  testbench
    // -----------------------------------------

    int     cycle;
    always_ff @(posedge clk) begin
        if ( reset ) begin
            cycle <= 0;
        end
        else if ( cke ) begin
            cycle <= cycle + 1;
        end
    end

    data_t          rand_data;
    data_t          rand_bit;
    logic   [1:0]   flg ;
    always_ff @(posedge clk) begin
        if ( cke ) begin
            rand_data <= data_t'($urandom());
            rand_bit  <= data_t'(1 << $urandom_range(0, $bits(data_t)-1));
            flg <= 2'($urandom_range(0, 3));
        end
    end
    
    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_data0 <= '0;
            s_data1 <= '0;
            s_clear <= '0;
            s_valid <= '0;
        end
        else if ( cke ) begin
            case ( cycle[3:0] )
            0:          begin s_data0 <= '0;          s_data1 <= '0         ;                   end
            1:          begin s_data0 <= '1;          s_data1 <= '1         ;                   end
            2:          begin s_data0 <=  rand_data;  s_data1 <= rand_data  ;                   end
            3:          begin s_data0 <= '0;          s_data1 <= '0        ^ rand_bit;          end // 1bitだけ不一致
            4:          begin s_data0 <= '1;          s_data1 <= '1        ^ rand_bit;          end // 1bitだけ不一致
            5:          begin s_data0 <=  rand_data;  s_data1 <= rand_data ^ rand_bit;          end // 1bitだけ不一致
            default:    begin s_data0 <=  data_t'($urandom());  s_data1 <= data_t'($urandom()); end // 完全ランダム
            endcase
            s_clear <= &flg;
            s_valid <= flg[0];
        end
    end
    
endmodule


`default_nettype wire


// end of file
