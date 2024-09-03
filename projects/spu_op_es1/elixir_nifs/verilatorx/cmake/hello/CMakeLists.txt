file(GLOB EXAMPLE_SRC ./hello_nif.cpp)
add_library(hello SHARED ${EXAMPLE_SRC})

# ライブラリの名前を 任意の名前に変更
set_target_properties(hello PROPERTIES OUTPUT_NAME "hello" PREFIX "" SUFFIX ".so")