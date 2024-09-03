# Environment variables passed via elixir_make
# ERTS_INCLUDE_DIR
# MIX_APP_PATH

# SPU extension installation location
SPU_EXTENSION_DIR := cache/xla_extension
SPU_EXTENSION_LIB := $(SPU_EXTENSION_DIR)/lib
SPU_INCLUDE_PATH  := $(SPU_EXTENSION_DIR)/include

# Cache configuration
EXLA_CACHE_SO = cache/libexla.so
EXLA_CACHE_OBJ_DIR = cache/objs
TARGET_DIR = ./cmake
BUILD_DIR = ${TARGET_DIR}/build

# Private configuration
CMAKE_DIR = cmake
PRIV_DIR = $(MIX_BUILD_PATH)/priv
EXLA_SO = $(PRIV_DIR)/libspu.so
EXLA_LIB_DIR = $(PRIV_DIR)/spu/lib

# Link paths
XLA_EXTENSION_LIB_LINK_PATH = ../$(CWD_RELATIVE_TO_PRIV_PATH)/$(XLA_EXTENSION_LIB)
EXLA_CACHE_SO_LINK_PATH = $(CWD_RELATIVE_TO_PRIV_PATH)/$(EXLA_CACHE_SO)

# all:
# 	@echo "${EXLA_DIR}"
# 	@echo "${PRIV_DIR}"
# 	@echo "${EXLA_SO}"
# 	@echo "${EXLA_LIB_DIR}"
 
build: 
	mkdir -p ${PRIV_DIR}/cmake
	cp -RT ./cmake ${PRIV_DIR}/cmake

clean:
	rm -rf "${BUILD_DIR}"