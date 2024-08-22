

# setting
TOP_MODULE = tb_sim

# Elixir
ELIXIR_DIR = ../../../../elixir
SPU_EXS    = $(ELIXIR_DIR)/spu1.exs
SPU_RTL    = $(ELIXIR_DIR)/rtl/spu1.sv
SPU_ALU    = add

# jelly
JELLY_TOP_DIR = ../../../../../../../packages/jelly
-include $(JELLY_TOP_DIR)/include/make/def_simulation.inc

SIM_LIB_DIRS += ../../stub
SIM_LIB_DIRS += ../../../rtl
SIM_LIB_DIRS += ../../../../rtl

VLOGFLAGS  = -sv
VLOGFLAGS += --sourcelibext .v
VLOGFLAGS += --sourcelibext .sv
VLOGFLAGS += $(addprefix --sourcelibdir ,$(SIM_LIB_DIRS))

ELABFLAGS  = -debug wave

SRCS  = ../$(TOP_MODULE).sv
SRCS += ../tb_main.sv
SRCS += ../../stub/design1.v
#SRCS += $(SPU_RTL)

# rulres
.PHONY: all
all: clean build run

.PHONY: build
build:
	xvlog $(VLOGFLAGS) $(SRCS)
	xelab $(ELABFLAGS) $(TOP_MODULE) -s $(TOP_MODULE)

$(SPU_RTL): $(SPU_EXS)
	elixir $(SPU_EXS) $(SPU_RTL) > $(SPU_RTL)	

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
	-rm -f $(SPU_RTL)