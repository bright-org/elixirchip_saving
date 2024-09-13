# Environment variables passed via elixir_make
# MIX_BUILD_PATH

# Private configuration
PRIV_DIR = $(MIX_BUILD_PATH)/priv/template
BUILD_DIR = ${PRIV_DIR}/build
 
build: 
	mkdir -p ${PRIV_DIR}
	cp -RT ./cmake ${PRIV_DIR}

clean:
	rm -rf "${BUILD_DIR}"