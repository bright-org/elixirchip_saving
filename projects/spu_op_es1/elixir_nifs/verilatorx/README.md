# verilatorx_sample

verilatorxで定義された`defg`の利用例です。
Elixirのコードはそのままで内部的にSPUを利用する関数呼びだしを行います。

```elixir:lib/hoge.ex
defmodule Hoge do
  import Defg

  defg calc(list) do
    Enum.sum(list)
  end
end
```

上記の関数は下記のコードとしてコンパイルされます（予定）

```elixir
  def calc(list) do
    Spu.sum(list)
  end
```

