

# setting
TOP_MODULE = tb_top

# jelly
JELLY_TOP_DIR = ../../../../../../packages/jelly
-include $(JELLY_TOP_DIR)/include/make/def_simulation.inc

XILINX_VIVADO ?= /tools/Xilinx/Vivado/2023.2

SIM_LIB_DIRS += ..
SIM_LIB_DIRS += ../..
SIM_LIB_DIRS += ../../../rtl
SIM_LIB_DIRS += ../../../../rtl

VLOGFLAGS  = -sv
VLOGFLAGS += --sourcelibext .v
VLOGFLAGS += --sourcelibext .sv
VLOGFLAGS += $(addprefix --sourcelibdir ,$(SIM_LIB_DIRS))
#VLOGFLAGS += -L uvm

ELABFLAGS  = -debug wave
#ELABFLAGS += -L unisims_ver -L unimacro_ver -L secureip
#ELABFLAGS += -L uvm
 
SRCS  = ../$(TOP_MODULE).sv
SRCS += $(XILINX_VIVADO)/data/verilog/src/glbl.v

# rulres
.PHONY: all
all: clean build run

.PHONY: build
build:
	xvlog $(VLOGFLAGS) $(SRCS)
	xelab $(ELABFLAGS) $(TOP_MODULE) glbl -s $(TOP_MODULE) -L unisims_ver -L unimacro_ver -L secureip
#	xelab $(ELABFLAGS) $(TOP_MODULE) glbl -s $(TOP_MODULE) -L unisims_ver -L unimacro_ver -L secureip -L uvm -timescale 1ns/1ps

.PHONY: run
run:
	rm -f simulation_completed.log
	xsim $(TOP_MODULE) --onerror quit --R
	@if [ ! -e simulation_completed.log ]; then exit 1; fi

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
