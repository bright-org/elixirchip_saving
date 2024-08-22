#!/bin/bash -eu

# 最初にソースコード内にパラメータを埋め込む処理を行う

# クリーンナップ
rm -fr build
rm -f example.out

# ライブラリビルド
mkdir build
cd build
cmake ..
cd ..
cmake --build build -j

# 出来上がったライブラリを使うC++のサンプルをビルド
g++ example.cpp -o example.out -pthread -L./build -lelixirchip_es1_spu_op_add

# サンプルの実行
./example.out


