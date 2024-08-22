#!/bin/bash -eu


# 最初にソースコード内にパラメータを埋め込む処理を行う
# ビット幅のなどのパラメータの異なるモジュールを混在する場合はそれぞれ異なる命名を行い
# ビルドする必要があるので、随時リネーミングを行う

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
g++ example.cpp -o example.out -pthread -L./build -lelixirchip_es1_spu_op_acc -lz

# サンプルの実行
./example.out

