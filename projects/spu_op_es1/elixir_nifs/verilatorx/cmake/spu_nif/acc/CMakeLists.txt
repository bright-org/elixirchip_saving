file(GLOB EXAMPLE_SRC ./*.cpp)

set(TARGET acc_#{bit}bit)

add_library(${TARGET} SHARED ${EXAMPLE_SRC})
target_include_directories(${TARGET}
  PUBLIC /src/elixir_nifs/gx_sample/_build/dev/priv/cmake/spu/${TARGET}
)
    
# ライブラリの名前を 任意の名前に変更
set_target_properties(${TARGET} PROPERTIES OUTPUT_NAME "${TARGET}" PREFIX "" SUFFIX ".so")
target_link_libraries(${TARGET}
    pthread
    sv_acc_#{bit}bit
    /src/elixir_nifs/gx_sample/_build/dev/priv/cmake/build/spu/${TARGET}
)