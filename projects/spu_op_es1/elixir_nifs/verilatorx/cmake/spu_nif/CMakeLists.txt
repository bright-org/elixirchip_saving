file(GLOB EXAMPLE_SRC ./*.cpp)

include_directories(
  ../spu
)

link_directories(
    ../spu/build
)

add_library(spu SHARED ${EXAMPLE_SRC})

# ライブラリの名前を 任意の名前に変更
set_target_properties(spu PROPERTIES OUTPUT_NAME "spu" PREFIX "" SUFFIX ".so")
target_link_libraries(spu
    pthread
    elixirchip_es1_spu_op_acc
)