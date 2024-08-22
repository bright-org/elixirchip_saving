

`timescale 1ns / 1ps
`default_nettype none


module tb_elixirchip_es1_spu_op_reg
        #(
            parameter   int     LATENCY    = 1                      ,   // レイテンシ指定
            parameter   int     DATA_BITS  = 8                      ,   // データ幅指定
            parameter   type    data_t     = logic [DATA_BITS-1:0]  ,   // データ型指定(オプション)
            parameter   data_t  CLEAR_DATA = '1                     ,   // m_data クリア値
            parameter           DEVICE     = "RTL"                  ,   // デバイス名
            parameter           SIMULATION = "false"                ,   // シミュレーション
            parameter           DEBUG      = "false"                    // デバッグ
        )
        (
            input   var logic           reset   ,   // 同期リセット(制論理)
            input   var logic           clk         // クロック
        );

    // ランダムにCKEを下げる
    logic           cke     = 1'b1;
    always_ff @( negedge clk ) begin
        cke <= $urandom_range(0, 9) != 0;
    end

    data_t          s_data  ;
    logic           s_clear;
    logic           s_valid ;
    data_t          m_data  ;

    elixirchip_es1_spu_op_reg
            #(
                .LATENCY        (LATENCY        ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         ),
                .CLEAR_DATA     (CLEAR_DATA     ),
                .DEVICE         (DEVICE         ),
                .SIMULATION     (SIMULATION     ),
                .DEBUG          (DEBUG          )
            )
        u_elixirchip_es1_spu_op_reg
            (
                .reset          ,
                .clk            ,
                .cke            ,

                .s_data         ,
                .s_clear        ,
                .s_valid        ,
                
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

    int             sel;
    logic   [1:0]   flg ;
    always_ff @(posedge clk) begin
        if ( cycle < 2048 ) begin
            // 前半は網羅テスト
            sel  <= int'(cycle[10:7]);
            flg  <= cycle[1:0];
        end
        else begin
            // 後半はランダムテスト
            sel  <= $urandom_range(0, 8);
            flg  <= 2'($urandom_range(0, 3));
        end
    end

    // 入力生成
    always_ff @(posedge clk) begin
        if ( reset ) begin
            s_data  <= '0;
            s_clear <= 1'b0;
            s_valid <= '0;
        end
        else if ( cke ) begin
            case ( sel )
            0:          s_data <= '0;
            1:          s_data <= '1;
            2:          s_data <= ~(data_t'(1) << $urandom_range(0, DATA_BITS-1));
            3:          s_data <=  (data_t'(1) << $urandom_range(0, DATA_BITS-1));
            default:    s_data <= data_t'($urandom());
            endcase
            s_clear <= &flg;
            s_valid <= flg[0];
        end
    end
    

endmodule


`default_nettype wire


// end of file
