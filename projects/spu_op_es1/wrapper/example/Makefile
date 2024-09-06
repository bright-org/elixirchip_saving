

.PHONY : all
all: lib_build

# ライブラリのビルド
.PHONY : lib_build
lib_build:
	make -C ../elixirchip_es1_spu_op_acc
	make -C ../elixirchip_es1_spu_op_add

# クリーンアップ
.PHONY : clean
clean:
	rm -f example.out

# サンプルの実行
.PHONY : run
run: lib_build
	g++ example.cpp -o example.out -pthread \
	    -I../elixirchip_es1_spu_op_acc -I../elixirchip_es1_spu_op_add \
	    -L../elixirchip_es1_spu_op_acc/build -L../elixirchip_es1_spu_op_add/build \
		-lelixirchip_es1_spu_op_acc -lelixirchip_es1_spu_op_add -lz
	./example.out
