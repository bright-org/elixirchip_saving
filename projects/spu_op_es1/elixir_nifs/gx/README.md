# gx

Nxに相当するアプリケーションの予定

FPGAシミュレータであるVerilatorをElixirからNIFs経由で利用してシミュレーションします。
シミュレート対象は、`elixir_fpga_eva/projects/spu_op_es1/rtl`です。

Elixirから直接シミュレーション上の回路を利用することはできないため、C++によるラッパーが作成されています。

## Installation

[サンプル](../verilatorx_sample/)が同リポジトリに存在します。
ローカルパス参照方式で依存関係に追加します。

```elixir
def deps do
  [
    {:verilatorx, path: "../01_verilatorx"},
  ]
end
```

