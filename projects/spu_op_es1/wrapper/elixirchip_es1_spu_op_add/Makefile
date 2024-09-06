

LIB_FILE = build/libelixirchip_es1_spu_op_add.a
SRC_FILE = elixirchip_es1_spu_op_add_wrapper.sv \
           elixirchip_es1_spu_op_add.cpp        \
           elixirchip_es1_spu_op_add.h          

.PHONY : all
all: $(LIB_FILE)

# ライブラリのビルド
.PHONY : lib_build
$(LIB_FILE): $(SRC_FILE)
	rm -fr build
	mkdir -p build
	cd build && cmake ..
	cmake --build build -j

# クリーンアップ
.PHONY : clean
clean:
	rm -fr build
	rm -f example.out

# サンプルの実行
.PHONY : run
run: $(LIB_FILE)
	g++ example.cpp -o example.out -pthread -L./build -lelixirchip_es1_spu_op_add -lz
	./example.out
