
# Elixir から RTL を生成して単体合成評価を行う

RTL_DIR  = ../rtl
SPU_EXS  = ../spu1.exs
SPU_RTL  = $(RTL_DIR)/spu1.sv
SPU_ALU  = add


# get vivado version
empty:=
space:= $(empty) $(empty)
VIVADO_VERSIONS := $(subst .,$(space),$(subst v,,$(word 2,$(shell vivado -version))))
VIVADO_VERSION  := $(word 1,$(VIVADO_VERSIONS)).$(word 2,$(VIVADO_VERSIONS))

# settings
PROJECT_NAME = eval_spu_elixir_stage1
BOARD_NAME   = kv260
export PRJ_NAME     = $(PROJECT_NAME)_tcl
export TOP_MODULE   = stream_processing_unit
export BOARD_PART   = xilinx.com:kv260_som*
export DEVICE_PART  =

export SYNTH_ARGS_MORE = -mode out_of_context
export TO_STEP         = route_design

TARGET_FILE = $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_routed.dcp


# directories
SCRIPTS_DIR = ../../../../../packages/jelly/scripts

# HLS IP
HLS_IP =
export HLS_IP

# sources
SOURCES  = $(SPU_RTL)
export SOURCES

# IP cores
IP_CORES = 
export IP_CORES

# block design
BD_SCRIPTS =
export BD_SCRIPTS

# constrains
CONSTRAINS  = ../../constrain/clk_kv260.xdc
export CONSTRAINS


# rules
.PHONY : all
all: build

.PHONY : rebuild
rebuild: clean create build

.PHONY : create
create: $(PRJ_NAME).xpr

.PHONY : build
build: $(TARGET_FILE) make_csv check_log

$(SPU_RTL): $(SPU_EXS)
	mkdir -p $(RTL_DIR)
	elixir $(SPU_EXS) $(SPU_ALU) > $(SPU_RTL)

$(TARGET_FILE): $(SOURCES) $(CONSTRAINS) $(IP_CORES) $(BD_SCRIPTS)
	rm -f $(PRJ_NAME).xpr
	vivado -m64 -mode batch -source $(SCRIPTS_DIR)/vivado_create_project.tcl | tee vivado_create_project.log
	vivado -m64 -mode batch -source $(SCRIPTS_DIR)/vivado_implementation.tcl | tee vivado_implementation.log

.PHONY : make_csv
make_csv:
	$(SCRIPTS_DIR)/vivado_utilization_rpt_to_csv.py $(PRJ_NAME).runs/synth_1/$(TOP_MODULE)_utilization_synth.rpt utilization_synth.csv
	$(SCRIPTS_DIR)/vivado_utilization_rpt_to_csv.py $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_utilization_placed.rpt utilization_placed.csv
	$(SCRIPTS_DIR)/vivado_timing_rpt_to_csv.py summary       $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_clock_summary.csv
	$(SCRIPTS_DIR)/vivado_timing_rpt_to_csv.py intra         $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_intra_clock.csv
	$(SCRIPTS_DIR)/vivado_timing_rpt_to_csv.py inter         $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_inter_clock.csv
#	$(SCRIPTS_DIR)/vivado_timing_rpt_to_csv.py other         $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_other_path_group.csv
#	$(SCRIPTS_DIR)/vivado_timing_rpt_to_csv.py ignore        $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_ignore_path.csv
#	$(SCRIPTS_DIR)/vivado_timing_rpt_to_csv.py unconstrained $(PRJ_NAME).runs/impl_1/$(TOP_MODULE)_timing_summary_routed.rpt timing_unconstrained_path.csv
	$(SCRIPTS_DIR)/vivado_timing_estimate_max_freq.py timing_clock_summary.csv timing_intra_clock.csv estimate_max_freq.csv

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
	-rm -f *.csv
	-rm -f $(SPU_RTL)

