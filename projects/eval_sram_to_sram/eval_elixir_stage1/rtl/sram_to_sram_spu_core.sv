
`timescale 1ns / 1ps
`default_nettype none


(* use_dsp = "no" *)
module sram_to_sram_spu_core
        #(
            parameter int  ADDR_BITS = 10,
            parameter type addr_t    = logic [ADDR_BITS-1:0],
            parameter int  DATA_BITS = 64,
            parameter type data_t    = logic [DATA_BITS-1:0]
        )
        (
            input   var logic       reset           ,
            input   var logic       clk             ,
            input   var logic       cke             ,

            input   var logic       start           ,
            output  var logic       done            ,

            output  var logic       mem0_ren        ,
            output  var addr_t      mem0_raddr      ,
            input   var data_t      mem0_rdata      ,

            output  var logic       mem1_ren        ,
            output  var addr_t      mem1_raddr      ,
            input   var data_t      mem1_rdata      ,

            output  var logic       mem2_wen        ,
            output  var addr_t      mem2_waddr      ,
            output  var data_t      mem2_wdata      ,

            output  var logic       mem3_wen        ,
            output  var addr_t      mem3_waddr      ,
            output  var data_t      mem3_wdata
        );

    // read
    data_t      read_data0      ;
    data_t      read_data1      ;
    logic       read_valid      ;
    sram_to_sram_read
            #(
                .ADDR_BITS      (ADDR_BITS),
                .addr_t         (addr_t   ),
                .DATA_BITS      (DATA_BITS),
                .data_t         (data_t   )
            )
        u_sram_to_sram_read
            (
                .reset           ,
                .clk             ,
                .cke             ,
                .start           ,
                .mem0_ren        ,
                .mem0_raddr      ,
                .mem0_rdata      ,
                .mem1_ren        ,
                .mem1_raddr      ,
                .mem1_rdata      ,
                .m_addr          (          ),
                .m_data0         (read_data0),
                .m_data1         (read_data1),
                .m_valid         (read_valid)
            );

    // ストリームプロセッシングユニット
    data_t      write_data0     ;
    data_t      write_data1     ;
    logic       write_valid     ;
    stream_processing_unit
        u_stream_processing_unit
            (
                .reset          ,
                .clk            ,
                .cke            ,
                .s_data0        (read_data0 ),
                .s_data1        (read_data1 ),
                .s_valid        (read_valid ),
                .m_data0        (write_data0),
                .m_data1        (write_data1),
                .m_valid        (write_valid)
            );

    // write
    sram_to_sram_write
            #(
                .ADDR_BITS      (ADDR_BITS      ),
                .addr_t         (addr_t         ),
                .DATA_BITS      (DATA_BITS      ),
                .data_t         (data_t         )
            )
        u_sram_to_sram_write
            (
                .reset           ,
                .clk             ,
                .cke             ,

                .done            ,

                .mem2_wen        ,
                .mem2_waddr      ,
                .mem2_wdata      ,
                .mem3_wen        ,
                .mem3_waddr      ,
                .mem3_wdata      ,

                .s_data0         (write_data0   ),
                .s_data1         (write_data1   ),
                .s_valid         (write_valid   )
            );


endmodule

`default_nettype wire

