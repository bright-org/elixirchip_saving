# Environment variables passed via elixir_make
# MIX_BUILD_PATH

export
REF_RTL_PATH := /src/rtl

# Private configuration
PRIV_DIR = $(MIX_BUILD_PATH)/priv/cmake
BUILD_DIR = ${PRIV_DIR}/build

build: 
	@ cmake -S "$(PRIV_DIR)" -B "${BUILD_DIR}"
	@ cmake --build "${BUILD_DIR}" -j

clean:
	rm -rf ./_build