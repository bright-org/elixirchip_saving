
A_WIDTH ?= 16
B_WIDTH ?= 16
SIGN    ?= unsigned

# get vivado version
empty:=
space:= $(empty) $(empty)
VIVADO_VERSIONS := $(subst .,$(space),$(subst v,,$(word 2,$(shell vivado -version))))
VIVADO_VERSION  := $(word 1,$(VIVADO_VERSIONS)).$(word 2,$(VIVADO_VERSIONS))

# settings
PROJECT_NAME = mul_utilization
BOARD_NAME   = zybo_z7
export PRJ_NAME     = $(PROJECT_NAME)_tcl
export TOP_MODULE   = $(PROJECT_NAME)
export BOARD_PART   = digilentinc.com:zybo-z7-10*
export DEVICE_PART  = xc7z010clg400-1

export SYNTH_ARGS_MORE = -mode out_of_context

TARGET_FILE = $(PRJ_NAME).runs/synth_1/$(TOP_MODULE)_utilization_synth.dcp


# directories
TOP_DIR = ../../../../..

PRJ_DIR = ../..

# include
JELLY_TOP_DIR =  ../../../../../../packages/jelly
#$(TOP_DIR)
-include $(JELLY_TOP_DIR)/include/make/def_sources.inc

# HLS IP
HLS_IP =
export HLS_IP

DEFINES  = A_WIDTH=$(A_WIDTH)
DEFINES += B_WIDTH=$(B_WIDTH)
DEFINES += SIGN=$(SIGN)
ifdef INS_FF
DEFINES += INS_FF=1
endif
export DEFINES

# sources
SOURCES  = $(PRJ_DIR)/rtl/mul_utilization.sv
#SOURCES += $(JELLY_RTL_SOURCES)
export SOURCES

# IP cores
IP_CORES =
export IP_CORES

# block design
BD_SCRIPTS =
export BD_SCRIPTS

# constrains
CONSTRAINS  = 
CONSTRAINS  = ../../constrain/top.xdc
#CONSTRAINS += ../../constrain/$(CLK_XDC)
export CONSTRAINS

TO_STEP = route_design
export TO_STEP


# rules
.PHONY : all
all: build

.PHONY : rebuild
rebuild: clean create build

.PHONY : create
create: $(PRJ_NAME).xpr

.PHONY : build
build: $(TARGET_FILE)
#build: $(TARGET_FILE) check_log


$(PRJ_NAME).xpr: $(SOURCES) $(CONSTRAINS) $(IP_CORES) $(BD_SCRIPTS) Makefile
	rm -f $(PRJ_NAME).xpr
	vivado -m64 -mode batch -source $(JELLY_TOP_DIR)/scripts/vivado_create_project.tcl

$(TARGET_FILE): $(PRJ_NAME).xpr
	vivado -m64 -mode batch -source $(JELLY_TOP_DIR)/scripts/vivado_synthesize.tcl

.PHONY : check_log
check_log:
	@echo "----- synth_1 -----"
	@cat $(PRJ_NAME).runs/synth_1/runme.log | grep encountered.
	@echo "----- impl_1 -----"
	@cat $(PRJ_NAME).runs/impl_1/runme.log | grep encountered.

.PHONY : clean
clean:
	-rm -fr .Xil
	-rm -fr $(PRJ_NAME).cache
	-rm -fr $(PRJ_NAME).hw
	-rm -fr $(PRJ_NAME).ip_user_files
	-rm -fr $(PRJ_NAME).runs
	-rm -fr $(PRJ_NAME).sim
	-rm -fr $(PRJ_NAME).srcs
	-rm -fr $(PRJ_NAME).gen
	-rm -fr $(PRJ_NAME).xpr
	-rm -f vivado*.jou
	-rm -f vivado*.log
