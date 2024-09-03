file(GLOB EXAMPLE_SRC ./*.cpp)

add_library(acc SHARED ${EXAMPLE_SRC})
target_include_directories(acc 
  PUBLIC /src/elixir_nifs/gx_sample/_build/dev/priv/cmake/spu/acc
)
    
# ライブラリの名前を 任意の名前に変更
set_target_properties(acc PROPERTIES OUTPUT_NAME "acc" PREFIX "" SUFFIX ".so")
target_link_libraries(acc
    pthread
    elixirchip_es1_spu_op_acc
    /src/elixir_nifs/gx_sample/_build/dev/priv/cmake/build/spu/acc
)