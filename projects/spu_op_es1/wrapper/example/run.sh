#!/bin/bash -eu

# acc build
cd ../elixirchip_es1_spu_op_acc
rm -fr build
mkdir build
cd build
cmake ..
cd ..
cmake --build build -j

# add build
cd ../elixirchip_es1_spu_op_add
rm -fr build
mkdir build
cd build
cmake ..
cd ..
cmake --build build -j

# exsample  build
cd ../exsample
g++ example.cpp -o example.out -pthread \
       -I../elixirchip_es1_spu_op_acc -I../elixirchip_es1_spu_op_add \
       -L../elixirchip_es1_spu_op_acc/build -L../elixirchip_es1_spu_op_add/build \
       -lelixirchip_es1_spu_op_acc -lelixirchip_es1_spu_op_add -lz

# run
./example.out
