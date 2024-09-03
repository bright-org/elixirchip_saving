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

# Private configuration
CMAKE_DIR = cmake
PRIV_DIR = $(MIX_BUILD_PATH)/priv/cmake
BUILD_DIR = ${PRIV_DIR}/build
EXLA_SO = $(PRIV_DIR)/libspu.so
EXLA_LIB_DIR = $(PRIV_DIR)/spu/lib

# Link paths
XLA_EXTENSION_LIB_LINK_PATH = ../$(CWD_RELATIVE_TO_PRIV_PATH)/$(XLA_EXTENSION_LIB)
EXLA_CACHE_SO_LINK_PATH = $(CWD_RELATIVE_TO_PRIV_PATH)/$(EXLA_CACHE_SO)

build: 
	@ cmake -S "$(PRIV_DIR)" -B "${BUILD_DIR}"
	@ cmake --build "${BUILD_DIR}" -j

clean:
	rm -rf "${BUILD_DIR}"