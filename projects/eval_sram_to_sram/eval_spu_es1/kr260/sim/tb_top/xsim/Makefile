

# setting
TOP_MODULE = tb_sim

JELLY_TOP_DIR = ../../../../../../../packages/jelly

-include $(JELLY_TOP_DIR)/include/make/def_simulation.inc

XILINX_VIVADO ?= /tools/Xilinx/Vivado/2023.2

SIM_LIB_DIRS += ../../stub
SIM_LIB_DIRS += ../../../rtl
SIM_LIB_DIRS += ../../../../rtl
SIM_LIB_DIRS += ../../../../../../spu_op_es1/rtl

VLOGFLAGS  = -sv
VLOGFLAGS += --sourcelibext .v
VLOGFLAGS += --sourcelibext .sv
VLOGFLAGS += $(addprefix --sourcelibdir ,$(SIM_LIB_DIRS))

ELABFLAGS  = -debug wave

SRCS  = ../$(TOP_MODULE).sv
SRCS += ../tb_main.sv
SRCS += ../../stub/design1.v
SRCS += $(XILINX_VIVADO)/data/verilog/src/glbl.v

# rulres
.PHONY: all
all: clean build run

.PHONY: build
build:
	xvlog $(VLOGFLAGS) $(SRCS)
	xelab $(ELABFLAGS) $(TOP_MODULE) glbl -s $(TOP_MODULE) -L unisims_ver -L unimacro_ver -L secureip

.PHONY: run
run:
	xsim $(TOP_MODULE) --R

.PHONY: clean
clean:
	-rm -fr xsim.dir
	-rm -fr .Xil
	-rm -f webtalk*.jou
	-rm -f webtalk*.log
	-rm -f xvlog*.log
	-rm -f xvlog*.pb
	-rm -f xelab*.log
	-rm -f xelab*.pb
	-rm -f xsim*.jou
	-rm -f xsim*.log

.PHONY: distclean
distclean: clean
	-rm -f *.pgm
	-rm -f *.ppm
	-rm -f $(TOP_MODULE).vcd
	-rm -f $(TOP_MODULE).wdb
