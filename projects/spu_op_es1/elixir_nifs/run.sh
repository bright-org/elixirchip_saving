# ラッパーファイル生成プロジェクト
cd ./sv_parser
rm -rf ./rtl
mkdir ./rtl

# 確認対象のみ記述
cp ../../rtl/elixirchip_es1_spu_op_add.sv ./rtl/elixirchip_es1_spu_op_add.sv

mix compile

# コンパイルして利用
cd ../gx_sample
make clean
iex -S mix