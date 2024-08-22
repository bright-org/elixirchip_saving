`timescale 1ns / 1ps
`default_nettype none


// Dualport-RAM
module ram_dualport_ramb18e2
        #(
            parameter   int                                 ADDR_WIDTH   = 10,
            parameter   int                                 DATA_WIDTH   = 18,
            parameter   int                                 WE_WIDTH     = 1,
            parameter   int                                 WORD_WIDTH   = DATA_WIDTH/WE_WIDTH,
            parameter   int                                 MEM_SIZE     = (1 << ADDR_WIDTH),
            parameter                                       RAM_TYPE     = "block",
            parameter   bit                                 DOUT_REGS0   = 1,
            parameter   bit                                 DOUT_REGS1   = 1,
            parameter                                       MODE0        = "READ_FIRST", // NO_CHANGE",
            parameter                                       MODE1        = "READ_FIRST", // "NO_CHANGE",

            parameter   bit                                 FILLMEM      = 0,
            parameter   logic   [WE_WIDTH*WORD_WIDTH-1:0]   FILLMEM_DATA = 0,
            parameter   bit                                 READMEMB     = 0,
            parameter   bit                                 READMEMH     = 0,
            parameter                                       READMEM_FIlE = ""
        )
        (
            input   wire                                clk,

            // port0
//          input   wire                                port0_clk,
            input   wire                                port0_en,
            input   wire                                port0_regcke,
//            input   wire    [WE_WIDTH-1:0]              port0_we,
            input   wire    [ADDR_WIDTH-1:0]            port0_addr,
            input   wire    [WE_WIDTH*WORD_WIDTH-1:0]   port0_din,
//            output  wire    [WE_WIDTH*WORD_WIDTH-1:0]   port0_dout,
            
            // port1
//          input   wire                                port1_clk,
            input   wire                                port1_en,
            input   wire                                port1_regcke,
//            input   wire    [WE_WIDTH-1:0]              port1_we,
            input   wire    [ADDR_WIDTH-1:0]            port1_addr,
//            input   wire    [WE_WIDTH*WORD_WIDTH-1:0]   port1_din,
            output  wire    [WE_WIDTH*WORD_WIDTH-1:0]   port1_dout
        );



    wire    [WE_WIDTH-1:0]              port0_we = 1'b1;
    wire    [WE_WIDTH*WORD_WIDTH-1:0]   port0_dout;

    wire    [WE_WIDTH-1:0]              port1_we  = '0;
    wire    [WE_WIDTH*WORD_WIDTH-1:0]   port1_din = '0;
  

    RAMB18E2
        #(
            .CASCADE_ORDER_A            ("NONE"             ),
            .CASCADE_ORDER_B            ("NONE"             ),
            .CLOCK_DOMAINS              ("INDEPENDENT"      ),
            .SIM_COLLISION_CHECK        ("ALL"              ),
            .DOA_REG                    (1                  ),
            .DOB_REG                    (1                  ),
            .ENADDRENA                  ("FALSE"            ),
            .ENADDRENB                  ("FALSE"            ),
            .INIT_A                     (18'h00000          ),
            .INIT_B                     (18'h00000          ),
            .INIT_FILE                  ("NONE"             ),
            .IS_CLKARDCLK_INVERTED      (1'b0               ),
            .IS_CLKBWRCLK_INVERTED      (1'b0               ),
            .IS_ENARDEN_INVERTED        (1'b0               ),
            .IS_ENBWREN_INVERTED        (1'b0               ),
            .IS_RSTRAMARSTRAM_INVERTED  (1'b0               ),
            .IS_RSTRAMB_INVERTED        (1'b0               ),
            .IS_RSTREGARSTREG_INVERTED  (1'b0               ),
            .IS_RSTREGB_INVERTED        (1'b0               ),
            .RDADDRCHANGEA              ("FALSE"            ),
            .RDADDRCHANGEB              ("FALSE"            ),
            .READ_WIDTH_A               (18                 ), // 0-9
            .READ_WIDTH_B               (18                 ), // 0-9
            .WRITE_WIDTH_A              (18                 ), // 0-9
            .WRITE_WIDTH_B              (18                 ), // 0-9
            .RSTREG_PRIORITY_A          ("RSTREG"           ),
            .RSTREG_PRIORITY_B          ("RSTREG"           ),
            .SRVAL_A                    (18'h00000          ),
            .SRVAL_B                    (18'h00000          ),
            .SLEEP_ASYNC                ("FALSE"            ),
            .WRITE_MODE_A               ("NO_CHANGE"        ),
            .WRITE_MODE_B               ("NO_CHANGE"        )
        )
    RAMB18E2_inst
        (
            .CASDOUTA                   (                   ), // 16-bit output: Port A cascade output data
            .CASDOUTB                   (                   ), // 16-bit output: Port B cascade output data
            .CASDOUTPA                  (                   ), // 2-bit output: Port A cascade output parity data
            .CASDOUTPB                  (                   ), // 2-bit output: Port B cascade output parity data
            .DOUTADOUT                  (port1_dout[15:0]   ), // 16-bit output: Port A data/LSB data
            .DOUTPADOUTP                (port1_dout[17:16]  ), // 2-bit output: Port A parity/LSB parity
            .DOUTBDOUT                  (port0_dout[15:0]   ), // 16-bit output: Port B data/MSB data
            .DOUTPBDOUTP                (port0_dout[17:16]  ), // 2-bit output: Port B parity/MSB parity
            .CASDIMUXA                  ('0                 ), // 1-bit input: Port A input data (0=DINA, 1=CASDINA)
            .CASDIMUXB                  ('0                 ), // 1-bit input: Port B input data (0=DINB, 1=CASDINB)
            .CASDINA                    ('0                 ), // 16-bit input: Port A cascade input data
            .CASDINB                    ('0                 ), // 16-bit input: Port B cascade input data
            .CASDINPA                   ('0                 ), // 2-bit input: Port A cascade input parity data
            .CASDINPB                   ('0                 ), // 2-bit input: Port B cascade input parity data
            .CASDOMUXA                  (1'b0               ), // 1-bit input: Port A unregistered data (0=BRAM data, 1=CASDINA)
            .CASDOMUXB                  (1'b0               ), // 1-bit input: Port B unregistered data (0=BRAM data, 1=CASDINB)
            .CASDOMUXEN_A               (1'b0               ), // 1-bit input: Port A unregistered output data enable
            .CASDOMUXEN_B               (1'b0               ), // 1-bit input: Port B unregistered output data enable
            .CASOREGIMUXA               (1'b0               ), // 1-bit input: Port A registered data (0=BRAM data, 1=CASDINA)
            .CASOREGIMUXB               (1'b0               ), // 1-bit input: Port B registered data (0=BRAM data, 1=CASDINB)
            .CASOREGIMUXEN_A            (1'b0               ), // 1-bit input: Port A registered output data enable
            .CASOREGIMUXEN_B            (1'b0               ), // 1-bit input: Port B registered output data enable
            .ADDRARDADDR                ({port1_addr, 4'd0} ), // 14-bit input: A/Read port address
            .ADDRENA                    (1'b1               ), // 1-bit input: Active-High A/Read port address enable
            .CLKARDCLK                  (clk                ), // 1-bit input: A/Read port clock
            .ENARDEN                    (port1_en           ), // 1-bit input: Port A enable/Read enable
            .REGCEAREGCE                (port1_regcke       ), // 1-bit input: Port A register enable/Register enable
            .RSTRAMARSTRAM              (1'b1               ), // 1-bit input: Port A set/reset
            .RSTREGARSTREG              (1'b1               ), // 1-bit input: Port A register set/reset
            .WEA                        ({4{port1_we}}      ), // 2-bit input: Port A write enable
            .DINADIN                    (port1_din[15:0]    ), // 16-bit input: Port A data/LSB data
            .DINPADINP                  (port1_din[17:16]   ), // 2-bit input: Port A parity/LSB parity
            .ADDRBWRADDR                ({port0_addr, 4'd0} ), // 14-bit input: B/Write port address
            .ADDRENB                    (1'b1               ), // 1-bit input: Active-High B/Write port address enable
            .CLKBWRCLK                  (clk                ), // 1-bit input: B/Write port clock
            .ENBWREN                    (port0_en           ), // 1-bit input: Port B enable/Write enable
            .REGCEB                     (port0_regcke       ), // 1-bit input: Port B register enable
            .RSTRAMB                    (1'b0               ), // 1-bit input: Port B set/reset
            .RSTREGB                    (1'b0               ), // 1-bit input: Port B register set/reset
            .SLEEP                      (1'b0               ), // 1-bit input: Sleep Mode
            .WEBWE                      ({4{port0_we}}      ), // 4-bit input: Port B write enable/Write enable
            .DINBDIN                    (port0_din[15:0]    ), // 16-bit input: Port B data/MSB data
            .DINPBDINP                  (port0_din[17:16]   ) // 2-bit input: Port B parity/MSB parity
        );

endmodule