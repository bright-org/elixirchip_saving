
LATENCY ?= 3
A_WIDTH ?= 8
B_WIDTH ?= 8
P_WIDTH ?= 16
A_SIGN  ?= signed
B_SIGN  ?= signed
P_SIGN  ?= signed
SHIFT   ?= 0
CLK_XDC ?= clk_775.xdc

# get vivado version
empty:=
space:= $(empty) $(empty)
VIVADO_VERSIONS := $(subst .,$(space),$(subst v,,$(word 2,$(shell vivado -version))))
VIVADO_VERSION  := $(word 1,$(VIVADO_VERSIONS)).$(word 2,$(VIVADO_VERSIONS))

# settings
PROJECT_NAME = dsp_mul_speed
BOARD_NAME   = zcu106
export PRJ_NAME     = $(PROJECT_NAME)_tcl
export TOP_MODULE   = $(PROJECT_NAME)
export BOARD_PART   = xilinx.com:zcu106*
export DEVICE_PART  =


TARGET_FILE = $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_routed.dcp


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

DEFINES  = LATENCY=$(LATENCY)
DEFINES += A_WIDTH=$(A_WIDTH)
DEFINES += B_WIDTH=$(B_WIDTH)
DEFINES += P_WIDTH=$(P_WIDTH)
DEFINES += A_SIGN=$(A_SIGN)
DEFINES += B_SIGN=$(B_SIGN)
DEFINES += P_SIGN=$(P_SIGN)
DEFINES += SHIFT=$(SHIFT)
export DEFINES

# sources
SOURCES  = $(PRJ_DIR)/rtl/dsp_mul_speed.sv
#SOURCES += $(JELLY_RTL_SOURCES)
export SOURCES

# IP cores
IP_CORES =
export IP_CORES

# block design
BD_SCRIPTS =
export BD_SCRIPTS

# constrains
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
build: $(TARGET_FILE) make_csv check_log


$(TARGET_FILE): $(SOURCES) $(CONSTRAINS) $(IP_CORES) $(BD_SCRIPTS)
	rm -f $(PRJ_NAME).xpr
	vivado -m64 -mode batch -source $(JELLY_TOP_DIR)/scripts/vivado_create_project.tcl | tee vivado_create_project.log
	vivado -m64 -mode batch -source $(JELLY_TOP_DIR)/scripts/vivado_implementation.tcl | tee vivado_implementation.log

.PHONY : make_csv
make_csv:
	$(JELLY_TOP_DIR)/scripts/vivado_utilization_rpt_to_csv.py $(PRJ_NAME).runs/synth_1/$(TOP_MODULE)_utilization_synth.rpt utilization_synth.csv
	$(JELLY_TOP_DIR)/scripts/vivado_utilization_rpt_to_csv.py $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_utilization_placed.rpt utilization_placed.csv
	$(JELLY_TOP_DIR)/scripts/vivado_timing_rpt_to_csv.py summary       $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_clock_summary.csv
	$(JELLY_TOP_DIR)/scripts/vivado_timing_rpt_to_csv.py intra         $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_intra_clock.csv
	$(JELLY_TOP_DIR)/scripts/vivado_timing_rpt_to_csv.py inter         $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_inter_clock.csv
#	$(JELLY_TOP_DIR)/scripts/vivado_timing_rpt_to_csv.py other         $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_other_path_group.csv
#	$(JELLY_TOP_DIR)/scripts/vivado_timing_rpt_to_csv.py ignore        $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_ignore_path.csv
#	$(JELLY_TOP_DIR)/scripts/vivado_timing_rpt_to_csv.py unconstrained $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_unconstrained_path.csv
	$(JELLY_TOP_DIR)/scripts/vivado_timing_estimate_max_freq.py timing_clock_summary.csv timing_intra_clock.csv timing_estimate_max_freq.csv

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
	-rm -f *.str
	-rm -f *.jou
	-rm -f *.log
	-rm -f *.csv
