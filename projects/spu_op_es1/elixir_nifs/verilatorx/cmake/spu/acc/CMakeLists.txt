
cmake_minimum_required(VERSION 3.16)

set(TARGET sv_acc_#{bit}bit)

project(${TARGET})

find_package(verilator 4.218 REQUIRED HINTS $ENV{VERILATOR_ROOT} ${VERILATOR_ROOT})
if (NOT verilator_FOUND)
    message(FATAL_ERROR "Verilator was not found. Either install it, or set the VERILATOR_ROOT environment variable")
endif()

add_library(${TARGET} STATIC ./wrapper.cpp)
set_target_properties(${TARGET} PROPERTIES POSITION_INDEPENDENT_CODE ON)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

if(NOT DEFINED ENV{REF_RTL_PATH} OR "$ENV{REF_RTL_PATH}" STREQUAL "")
    set(RTL_PATH ../../rtl)
else()
    set(RTL_PATH $ENV{REF_RTL_PATH})
endif()

verilate(${TARGET}
    VERILATOR_ARGS -D__VERILATOR__ -O3 -y ${RTL_PATH} # --assert --trace-fst --trace-params --trace-structs --trace-underscore
    SOURCES ./wrapper.sv
)
