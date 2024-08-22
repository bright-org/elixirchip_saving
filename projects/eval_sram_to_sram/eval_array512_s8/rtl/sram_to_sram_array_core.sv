
`timescale 1ns / 1ps
`default_nettype none


(* use_dsp = "no" *)
module sram_to_sram_array_core
        #(
            parameter int  ADDR_BITS = 10,
            parameter type addr_t    = logic [ADDR_BITS-1:0],
            parameter int  DATA_BITS = 8,
            parameter type data_t    = logic signed [DATA_BITS-1:0],
            parameter int  UNIT_LEN  = 64,
            parameter int  ARRAY_LEN = 32
        )
        (
            input   var logic                           reset           ,
            input   var logic                           clk             ,
            input   var logic                           cke             ,

            input   var logic                           start           ,
            output  var logic                           done            ,

            output  var logic                           mem0_ren        ,
            output  var addr_t                          mem0_raddr      ,
            input   var data_t  [UNIT_LEN-1:0]          mem0_rdata      ,

            output  var logic                           mem1_ren        ,
            output  var addr_t                          mem1_raddr      ,
            input   var data_t  [UNIT_LEN-1:0]          mem1_rdata      ,

            output  var logic                           mem2_wen        ,
            output  var addr_t                          mem2_waddr      ,
            output  var data_t  [UNIT_LEN-1:0]          mem2_wdata
        );

    // read
    data_t  [UNIT_LEN-1:0]          read_data0      ;
    data_t  [UNIT_LEN-1:0]          read_data1      ;
    logic                           read_valid      ;
    sram_to_sram_read
            #(
                .ADDR_BITS      (ADDR_BITS), 
                .addr_t         (addr_t   ), 
                .DATA_BITS      (DATA_BITS), 
                .data_t         (data_t   ), 
                .UNIT_LEN       (UNIT_LEN ) 
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

    // calc array
    data_t  [UNIT_LEN-1:0]          array_data0    [ARRAY_LEN:0];
    data_t  [UNIT_LEN-1:0]          array_data1    [ARRAY_LEN:0];
    logic                           array_valid    [ARRAY_LEN:0];

    assign array_data0[0] = read_data0;
    assign array_data1[0] = read_data1;
    assign array_valid[0] = read_valid;

    for ( genvar i = 0; i < ARRAY_LEN; ++i ) begin : calc_unit
        sram_to_sram_calc_unit
                #(
                    .DATA_BITS      (DATA_BITS),
                    .data_t         (data_t   ),
                    .UNIT_LEN       (UNIT_LEN )
                )
            u_sram_to_sram_calc_unit
                (
                    .reset           ,
                    .clk             ,
                    .cke             ,

                    .s_data0         (array_data0[i]),
                    .s_data1         (array_data1[i]),
                    .s_valid         (array_valid[i]),

                    .m_data0         (array_data0[i+1]),
                    .m_data1         (array_data1[i+1]),
                    .m_valid         (array_valid[i+1])
                );
    end

    // add
    data_t  [UNIT_LEN-1:0]          add_data;
    logic                           add_valid;
    always_ff @( posedge clk ) begin
        if ( reset ) begin
            add_data  <= 'x;
            add_valid <= 1'b0;
        end
        else if ( cke ) begin
            for ( int i = 0; i < UNIT_LEN; i++) begin
                add_data[i] <= array_data0[ARRAY_LEN][i] + array_data1[ARRAY_LEN][i];
            end
            add_valid <= array_valid[ARRAY_LEN];
        end
    end


    // write
    sram_to_sram_write
            #(
                .ADDR_BITS      (ADDR_BITS ),
                .addr_t         (addr_t    ),
                .DATA_BITS      (DATA_BITS ),
                .data_t         (data_t    ),
                .UNIT_LEN       (UNIT_LEN  )
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

                .s_data          (add_data),
                .s_valid         (add_valid)
            );


endmodule

`default_nettype wire

