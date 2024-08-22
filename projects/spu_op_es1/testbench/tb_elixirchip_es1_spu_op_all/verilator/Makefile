

# setting
TOP_MODULE = tb_top

# jelly
JELLY_TOP_DIR = ../../../../../../packages/jelly
-include $(JELLY_TOP_DIR)/include/make/def_simulation.inc

SIM_LIB_DIRS += ..
SIM_LIB_DIRS += ../../../rtl
SIM_LIB_DIRS += ../../../../rtl

FLAGS  = --binary -j 0
FLAGS += --assert
FLAGS += --trace-fst --trace-params --trace-structs --trace-underscore
FLAGS += -D__VERILATOR__ -D__SIMULATION__
FLAGS += $(addprefix -y ,$(SIM_LIB_DIRS))
#FLAGS += -Wall
#FLAGS += -Wno-WIDTH
#FLAGS += -Wno-PINCONNECTEMPTY
#FLAGS += -Wno-UNUSEDPARAM
#FLAGS += -Wno-UNUSEDSIGNAL
#FLAGS += -Wno-UNUSEDPARAM
#FLAGS += -Wno-WIDTHTRUNC
#FLAGS += -Wno-fatal
#FLAGS += -Wno-WIDTHEXPAND
#FLAGS += -Wno-SIDEEFFECT

SRCS  = ../$(TOP_MODULE).sv
SRCS += ../tb_main.sv

# rulres
all: build run

.PHONY : build
build: $(SRCS)
	verilator $(FLAGS) --top $(TOP_MODULE) $(SRCS)

$(SPU_RTL): $(SPU_EXS)
	elixir $(SPU_EXS) $(SPU_ALU) > $(SPU_RTL)	

.PHONY : run
run:
	./obj_dir/V$(TOP_MODULE)

.PHONY : coverage
coverage:
	verilator_coverage --annotate annotated coverage.dat


.PHONY : clean
clean:
	rm -rf obj_dir

.PHONY : distclean
distclean: clean
	rm -f *.fst *.vcd
	rm -f *.ppm *.pgm
	rm -f axi*.txt
	rm -f coverage.dat
	rm -fr annotated
