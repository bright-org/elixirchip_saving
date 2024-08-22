
`timescale 1ns / 1ps
`default_nettype none


module sram_to_sram_any
        #(
            parameter   int     MEM_ADDR_BITS = 10      ,
            parameter   int     MEM_DATA_BITS = 512     ,
            parameter           MEM_RAM_TYPE  = "block" ,
            parameter   int     WB_ADR_BITS   = 15      ,
            parameter   int     WB_DAT_BITS   = 64      ,
            parameter   int     WB_SEL_BITS   = (WB_DAT_BITS / 8)
        )
        (
            input   var logic                           core_reset      ,
            input   var logic                           core_clk        ,

            input   var logic                           s_wb_rst_i      ,
            input   var logic                           s_wb_clk_i      ,
            input   var logic   [WB_ADR_BITS-1:0]       s_wb_adr_i      ,
            input   var logic   [WB_DAT_BITS-1:0]       s_wb_dat_i      ,
            output  var logic   [WB_DAT_BITS-1:0]       s_wb_dat_o      ,
            input   var logic                           s_wb_we_i       ,
            input   var logic   [WB_SEL_BITS-1:0]       s_wb_sel_i      ,
            input   var logic                           s_wb_stb_i      ,
            output  var logic                           s_wb_ack_o      
        );


    localparam  int     MEM_WE_BITS      = MEM_DATA_BITS/8;
    localparam  int     WB_MEM_ADDR_BITS = MEM_ADDR_BITS + $clog2(MEM_DATA_BITS/WB_DAT_BITS);


    // -------------------------------------
    //  Async Pulse
    // -------------------------------------

    // signals
    logic               start;
    logic               done;

    // core signals
    logic               core_start;
    logic               core_done;

    jelly_pulse_async
            #(
                .ASYNC      (1)
            )
        u_pulse_async_start
            (
                .s_reset    (s_wb_rst_i ),
                .s_clk      (s_wb_clk_i ),
                .s_pulse    (start      ),

                .m_reset    (core_reset ),
                .m_clk      (core_clk   ),
                .m_pulse    (core_start )
            );
    
    jelly_pulse_async
            #(
                .ASYNC      (1)
            )
        u_pulse_async_done
            (
                .s_reset    (core_reset ),
                .s_clk      (core_clk   ),
                .s_pulse    (core_done  ),

                .m_reset    (s_wb_rst_i ),
                .m_clk      (s_wb_clk_i ),
                .m_pulse    (done       )

            );
    

    // -------------------------------------
    //  registers domain
    // -------------------------------------
    
    logic                       wb_reg_stb_i;
    logic   [WB_DAT_BITS-1:0]   wb_reg_dat_o;
    logic                       wb_reg_ack_o;

    // register address offset
    localparam  bit     [WB_ADR_BITS-1:0]  ADR_START  = WB_ADR_BITS'('h00);
    localparam  bit     [WB_ADR_BITS-1:0]  ADR_DONE   = WB_ADR_BITS'('h01);

    // registers
    logic   [0:0]       reg_start;
    logic   [0:0]       reg_done;

    // write mask
    function [WB_DAT_BITS-1:0] write_mask(
                                        input [WB_DAT_BITS-1:0] org,
                                        input [WB_DAT_BITS-1:0] wdat,
                                        input [WB_SEL_BITS-1:0] msk
                                    );
    integer i;
    begin
        for ( i = 0; i < WB_DAT_BITS; i = i+1 ) begin
            write_mask[i] = msk[i/8] ? wdat[i] : org[i];
        end
    end
    endfunction
    
    // registers control
    always_ff @(posedge s_wb_clk_i) begin
        if ( s_wb_rst_i ) begin
            reg_start <= 1'b0;
            reg_done  <= 1'b0;
        end
        else begin
            // auto clear
            reg_start <= 1'b0;

            // set done
            if ( done ) begin
                reg_done <= 1'b1;
            end
            
            // write
            if ( wb_reg_stb_i && s_wb_we_i ) begin
                case ( s_wb_adr_i )
                ADR_START:  reg_start <= 1'(write_mask(WB_DAT_BITS'(reg_start), s_wb_dat_i, s_wb_sel_i));
                ADR_DONE:   reg_done  <= 1'(write_mask(WB_DAT_BITS'(reg_done ), s_wb_dat_i, s_wb_sel_i));
                default: ;
                endcase
            end
        end
    end
    
    // read
    always_comb begin
        wb_reg_dat_o = '0;
        case (s_wb_adr_i )
        ADR_START:  wb_reg_dat_o = WB_DAT_BITS'(reg_start);
        ADR_DONE:   wb_reg_dat_o = WB_DAT_BITS'(reg_done );
        default: ;
        endcase
    end

    always_comb wb_reg_ack_o = wb_reg_stb_i;

    assign start = reg_start;
    
    
    
    // -------------------------------------
    //  memory0
    // -------------------------------------

    logic                               wb_mem0_stb_i   ;
    logic   [WB_DAT_BITS-1:0]           wb_mem0_dat_o   ;
    logic                               wb_mem0_ack_o   ;

    logic   [MEM_WE_BITS-1:0]           mem0_wb_we      ;
    logic   [MEM_ADDR_BITS-1:0]         mem0_wb_addr    ;
    logic   [MEM_DATA_BITS-1:0]         mem0_wb_wdata   ;
    logic   [MEM_DATA_BITS-1:0]         mem0_wb_rdata   ;

    logic   [MEM_ADDR_BITS-1:0]         mem0_core_addr  ;
    logic   [MEM_DATA_BITS-1:0]         mem0_core_dout  ;

    jelly2_wishbone_to_mem
            #(
                .WB_ADR_WIDTH       (WB_MEM_ADDR_BITS   ),
                .WB_DAT_WIDTH       (WB_DAT_BITS        ),
                .MEM_ADDR_WIDTH     (MEM_ADDR_BITS      ),
                .MEM_DATA_WIDTH     (MEM_DATA_BITS      ),
                .MEM_LATENCY        (2                  )
            )
        u_wishbone_to_mem_0
            (
                .reset              (s_wb_rst_i         ),
                .clk                (s_wb_clk_i         ),
                .cke                (1'b1               ),
                
                .s_wb_adr_i         (s_wb_adr_i[WB_MEM_ADDR_BITS-1:0]),
                .s_wb_dat_o         (wb_mem0_dat_o      ),
                .s_wb_dat_i         (s_wb_dat_i         ),
                .s_wb_sel_i         (s_wb_sel_i         ),
                .s_wb_we_i          (s_wb_we_i          ),
                .s_wb_stb_i         (wb_mem0_stb_i      ),
                .s_wb_ack_o         (wb_mem0_ack_o      ),

                .m_mem_we           (mem0_wb_we         ),
                .m_mem_addr         (mem0_wb_addr       ),
                .m_mem_wdata        (mem0_wb_wdata      ),
                .m_mem_rdata        (mem0_wb_rdata      )
            );

    jelly2_ram_dualport
            #(
                .ADDR_WIDTH         (MEM_ADDR_BITS      ),
                .DATA_WIDTH         (MEM_DATA_BITS      ),
                .WE_WIDTH           (MEM_WE_BITS        ),
                .WORD_WIDTH         (8                  ),
                .RAM_TYPE           (MEM_RAM_TYPE       ),
                .DOUT_REGS0         (1                  ),
                .DOUT_REGS1         (1                  ),
                .MODE0              ("NO_CHANGE"        ),
                .MODE1              ("NO_CHANGE"        )
            )
        u_ram_dualport_mem0
            (
                .port0_clk          (core_clk           ),
                .port0_en           (1'b1               ),
                .port0_regcke       (1'b1               ),
                .port0_we           ('0                 ),
                .port0_addr         (mem0_core_addr     ),
                .port0_din          ('0                 ),
                .port0_dout         (mem0_core_dout     ),
                
                .port1_clk          (s_wb_clk_i         ),
                .port1_en           (1'b1               ),
                .port1_regcke       (1'b1               ),
                .port1_we           (mem0_wb_we         ),
                .port1_addr         (mem0_wb_addr       ),
                .port1_din          (mem0_wb_wdata      ),
                .port1_dout         (mem0_wb_rdata      )
            );


    // -------------------------------------
    //  memory1
    // -------------------------------------

    logic                               wb_mem1_stb_i   ;
    logic   [WB_DAT_BITS-1:0]           wb_mem1_dat_o   ;
    logic                               wb_mem1_ack_o   ;

    logic   [MEM_WE_BITS-1:0]           mem1_wb_we      ;
    logic   [MEM_ADDR_BITS-1:0]         mem1_wb_addr    ;
    logic   [MEM_DATA_BITS-1:0]         mem1_wb_wdata   ;
    logic   [MEM_DATA_BITS-1:0]         mem1_wb_rdata   ;

    logic   [MEM_ADDR_BITS-1:0]         mem1_core_addr  ;
    logic   [MEM_DATA_BITS-1:0]         mem1_core_dout  ;


    jelly2_wishbone_to_mem
            #(
                .WB_ADR_WIDTH       (WB_MEM_ADDR_BITS   ),
                .WB_DAT_WIDTH       (WB_DAT_BITS        ),
                .MEM_ADDR_WIDTH     (MEM_ADDR_BITS      ),
                .MEM_DATA_WIDTH     (MEM_DATA_BITS      ),
                .MEM_LATENCY        (2                  )
            )
        u_wishbone_to_mem_1
            (
                .reset              (s_wb_rst_i         ),
                .clk                (s_wb_clk_i         ),
                .cke                (1'b1               ),
                
                .s_wb_adr_i         (s_wb_adr_i[WB_MEM_ADDR_BITS-1:0]),
                .s_wb_dat_o         (wb_mem1_dat_o      ),
                .s_wb_dat_i         (s_wb_dat_i         ),
                .s_wb_sel_i         (s_wb_sel_i         ),
                .s_wb_we_i          (s_wb_we_i          ),
                .s_wb_stb_i         (wb_mem1_stb_i      ),
                .s_wb_ack_o         (wb_mem1_ack_o      ),

                .m_mem_we           (mem1_wb_we         ),
                .m_mem_addr         (mem1_wb_addr       ),
                .m_mem_wdata        (mem1_wb_wdata      ),
                .m_mem_rdata        (mem1_wb_rdata      )
            );

    jelly2_ram_dualport
            #(
                .ADDR_WIDTH         (MEM_ADDR_BITS      ),
                .DATA_WIDTH         (MEM_DATA_BITS      ),
                .WE_WIDTH           (MEM_WE_BITS        ),
                .WORD_WIDTH         (8                  ),
                .RAM_TYPE           (MEM_RAM_TYPE       ),
                .DOUT_REGS0         (1                  ),
                .DOUT_REGS1         (1                  ),
                .MODE0              ("NO_CHANGE"        ),
                .MODE1              ("NO_CHANGE"        )
            )
        u_ram_dualport_mem1
            (
                .port0_clk          (core_clk           ),
                .port0_en           (1'b1               ),
                .port0_regcke       (1'b1               ),
                .port0_we           ('0                 ),
                .port0_addr         (mem1_core_addr     ),
                .port0_din          ('0                 ),
                .port0_dout         (mem1_core_dout     ),
                
                .port1_clk          (s_wb_clk_i         ),
                .port1_en           (1'b1               ),
                .port1_regcke       (1'b1               ),
                .port1_we           (mem1_wb_we         ),
                .port1_addr         (mem1_wb_addr       ),
                .port1_din          (mem1_wb_wdata      ),
                .port1_dout         (mem1_wb_rdata      )
            );



    // -------------------------------------
    //  memory2
    // -------------------------------------

    logic                               wb_mem2_stb_i   ;
    logic   [WB_DAT_BITS-1:0]           wb_mem2_dat_o   ;
    logic                               wb_mem2_ack_o   ;

    logic   [MEM_WE_BITS-1:0]           mem2_wb_we      ;
    logic   [MEM_ADDR_BITS-1:0]         mem2_wb_addr    ;
    logic   [MEM_DATA_BITS-1:0]         mem2_wb_wdata   ;
    logic   [MEM_DATA_BITS-1:0]         mem2_wb_rdata   ;

    logic                               mem2_core_we    ;
    logic   [MEM_ADDR_BITS-1:0]         mem2_core_addr  ;
    logic   [MEM_DATA_BITS-1:0]         mem2_core_din   ;

    jelly2_wishbone_to_mem
            #(
                .WB_ADR_WIDTH       (WB_MEM_ADDR_BITS   ),
                .WB_DAT_WIDTH       (WB_DAT_BITS        ),
                .MEM_ADDR_WIDTH     (MEM_ADDR_BITS      ),
                .MEM_DATA_WIDTH     (MEM_DATA_BITS      ),
                .MEM_LATENCY        (2                  )
            )
        u_wishbone_to_mem_2
            (
                .reset              (s_wb_rst_i         ),
                .clk                (s_wb_clk_i         ),
                .cke                (1'b1               ),
                
                .s_wb_adr_i         (s_wb_adr_i[WB_MEM_ADDR_BITS-1:0]),
                .s_wb_dat_o         (wb_mem2_dat_o      ),
                .s_wb_dat_i         (s_wb_dat_i         ),
                .s_wb_sel_i         (s_wb_sel_i         ),
                .s_wb_we_i          (s_wb_we_i          ),
                .s_wb_stb_i         (wb_mem2_stb_i      ),
                .s_wb_ack_o         (wb_mem2_ack_o      ),

                .m_mem_we           (mem2_wb_we         ),
                .m_mem_addr         (mem2_wb_addr       ),
                .m_mem_wdata        (mem2_wb_wdata      ),
                .m_mem_rdata        (mem2_wb_rdata      )
            );

    jelly2_ram_dualport
            #(
                .ADDR_WIDTH         (MEM_ADDR_BITS      ),
                .DATA_WIDTH         (MEM_DATA_BITS      ),
                .WE_WIDTH           (MEM_WE_BITS        ),
                .WORD_WIDTH         (8                  ),
                .RAM_TYPE           (MEM_RAM_TYPE       ),
                .DOUT_REGS0         (1                  ),
                .DOUT_REGS1         (1                  ),
                .MODE0              ("NO_CHANGE"        ),
                .MODE1              ("NO_CHANGE"        )
            )
        u_ram_dualport_mem2
            (
                .port0_clk          (core_clk           ),
                .port0_en           (1'b1               ),
                .port0_regcke       (1'b1               ),
                .port0_we           ({MEM_WE_BITS{mem2_core_we}}),
                .port0_addr         (mem2_core_addr     ),
                .port0_din          (mem2_core_din      ),
                .port0_dout         (                   ),
                
                .port1_clk          (s_wb_clk_i         ),
                .port1_en           (1'b1               ),
                .port1_regcke       (1'b1               ),
                .port1_we           (mem2_wb_we         ),
                .port1_addr         (mem2_wb_addr       ),
                .port1_din          (mem2_wb_wdata      ),
                .port1_dout         (mem2_wb_rdata      )
            );



    // -------------------------------------
    //  core
    // -------------------------------------

    sram_to_sram_any_core
            #(
                .ADDR_BITS      (MEM_ADDR_BITS  ),
                .DATA_BITS      (8              ),
                .UNIT_LEN       (MEM_DATA_BITS/8)
            )
        u_sram_to_sram_mul_core
            (
                .reset          (core_reset     ),
                .clk            (core_clk       ),
                .cke            (1'b1           ),
                .start          (core_start     ),
                .done           (core_done      ),
                .mem0_ren       (               ),
                .mem0_raddr     (mem0_core_addr ),
                .mem0_rdata     (mem0_core_dout ),
                .mem1_ren       (               ),
                .mem1_raddr     (mem1_core_addr ),
                .mem1_rdata     (mem1_core_dout ),
                .mem2_wen       (mem2_core_we   ),
                .mem2_waddr     (mem2_core_addr ),
                .mem2_wdata     (mem2_core_din  )
            );


    assign wb_reg_stb_i  = s_wb_stb_i && s_wb_adr_i[WB_ADR_BITS-1:WB_MEM_ADDR_BITS] == 0;
    assign wb_mem0_stb_i = s_wb_stb_i && s_wb_adr_i[WB_ADR_BITS-1:WB_MEM_ADDR_BITS] == 1;
    assign wb_mem1_stb_i = s_wb_stb_i && s_wb_adr_i[WB_ADR_BITS-1:WB_MEM_ADDR_BITS] == 2;
    assign wb_mem2_stb_i = s_wb_stb_i && s_wb_adr_i[WB_ADR_BITS-1:WB_MEM_ADDR_BITS] == 3;
    
    assign s_wb_dat_o = wb_reg_stb_i  ? wb_reg_dat_o  :
                        wb_mem0_stb_i ? wb_mem0_dat_o :
                        wb_mem1_stb_i ? wb_mem1_dat_o :
                        wb_mem2_stb_i ? wb_mem2_dat_o :
                        '0;

    assign s_wb_ack_o = wb_reg_stb_i  ? wb_reg_ack_o  :
                        wb_mem0_stb_i ? wb_mem0_ack_o :
                        wb_mem1_stb_i ? wb_mem1_ack_o :
                        wb_mem2_stb_i ? wb_mem2_ack_o :
                        s_wb_stb_i;

endmodule

`default_nettype wire

