# ElixirChip ES1 の演算オペレータの単独呼び出しラッパー

## 概要

SPU 生成評価に先立ち、SPU で利用する演算オペレータを Elixir から単独でリファレンスとして利用できるようにすることを目的としたラッパー群である。

なお、今後の議論で大きく変わる可能性がある。

主に Elixir から呼ぶことを目的とはするが、汎用の C言語関数として呼び出し可能なライブラリモジュールとして構築する。

SystemVerilog では インスタンス生成時に parameter でモジュールの特性を指定できる。

これによって 4bit の加算器や 8bit の加算器を同じソースからコンパイルすることが出来る。

一方で、Elixir からの呼び出しに先立ってコンパイルが必要であるため、Elixir で  4bit加算器と8bit加算器を混ぜて使う場合は
それぞれを個別にビルドして利用する必要がある。将来的にそのような状況も視野に入れて構成しておく。


## 使い方の案

下記のようなフローを想定している

1. Elixir 側で評価したいモジュールの構成パターンに合わせて元のソースコードのパラメータを埋め直す(置換する)
3. Verilator 用の cmake でコンパイルを行う
4. 出来上がったライブラリファイルをリンクして自由にC言語関数を呼び出して評価する


## 現在のサンプル

elixirchip_es1_spu_op_add と elixirchip_es1_spu_op_acc の2種類について準備している。

elixirchip_es1_spu_op_acc を例に説明する

### 動かし方

verilator と cmake がインスト－るされている環境で、

projects/spu_op_es1/wrapper/elixirchip_es1_spu_op_acc

に移動して、 ./run.sh を実行すればよい。
下記が実行される。

1. elixirchip_es1_spu_op_acc.sv を利用するライブラリがビルドされる
2. 上記で作ったライブラリを使うサンプルがビルドされる
3. サンプルを実行する


### 構成の説明

| ファイル | 説明 |
|:---------|:-----|
| elixirchip_es1_spu_op_acc_wrapper.sv | パラメータを与えてインスタンス化するためのラッパー。Elixir でパラメータを埋めるべきファイル。|
| elixirchip_es1_spu_op_acc.cpp        | Verilator を使って SV を呼び出す C関数群 |
| elixirchip_es1_spu_op_acc.h          | ヘッダファイル|
| CMakeLists.txt                       | Verilator でライブラリを作るための cmake 用ファイル|
| example.cpp                          | サンプルプログラム|
| run.sh                               | 一連の実行スクリプト|


### Elixir 側でやる必要のある事

parameter 違いの同じ演算オペレータが名前空間が衝突しないように適切にリネームが必要。

1. elixirchip_es1_spu_op_acc_wrapper.sv の中の parameter の値を置換
2. run.sh に習って cmake でビルド
3. elixirchip_es1_spu_op_acc/build/libelixirchip_es1_spu_op_acc.a にライブラリが出来上がる
4. 出来上がったライブラリファイルを Elixir から呼べるようにする(nifなど？)


### 実行時にやる事

1. 各ライブラリでオペレータを生成してハンドルを得る
2. ハンドルを使って各オペレータを呼び出し
3. 終了時にハンドルを削除する


## その他議論内容

現在スタティックライブラリにしていますが、ダイナミックにすることも出来ます。

Verilator が内部でコンテキストを生成する仕組みなので、生成と削除の関数が必要です。

add や sub など副作用のない関数は、bit幅が同じなら 1つだけ生成して使いまわしても構いません。

acc や reg や メモリ関連など、以前の演算内容を内部状態に持つものは個別にハンドルを作る必要があります。

前時代的な(Win3.1的？)なハンドルにしていますが、C++ のクラスにした方がむしろラップしやすいとかであればそれも可能です。


## サンプルの実行結果例

run.sh を実行して下記のようになれば成功です。

### acc の場合

```
start
acc1: 10
acc2: 20
acc1: 12
acc2: 17
end
```

### add の場合

```
start
s_carry: 0, s_data0: 1 , s_data1: 2  -> m_data: 3, m_carry: 0, m_msb_c:0
s_carry: 1, s_data0: 2 , s_data1: 3  -> m_data: 6, m_carry: 0, m_msb_c:0
s_carry: 0, s_data0: 100 , s_data1: 28 -> m_data: 128, m_carry: 0, m_msb_c:1
s_carry: 0, s_data0: 128 , s_data1: 128 -> m_data: 0, m_carry: 1, m_msb_c:0
s_carry: 1, s_data0: 200 , s_data1: 56 -> m_data: 1, m_carry: 1, m_msb_c:1
end
```
