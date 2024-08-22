
cmake_minimum_required(VERSION 3.16)

set(TARGET elixirchip_es1_spu_op_add)

project(${TARGET})

find_package(verilator 4.218 REQUIRED HINTS $ENV{VERILATOR_ROOT} ${VERILATOR_ROOT})
if (NOT verilator_FOUND)
    message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
endif()

add_library(${TARGET} STATIC ./${TARGET}.cpp)
set_target_properties(${TARGET} PROPERTIES POSITION_INDEPENDENT_CODE ON)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

verilate(${TARGET}
    VERILATOR_ARGS -D__VERILATOR__ -O3 -y ../../rtl
    SOURCES ./${TARGET}_wrapper.sv
)
