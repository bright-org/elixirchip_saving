defmodule Parameter do
  def extract(ast, _acc = %{}) do
    {_ast, acc} =
      Macro.postwalk(ast, %{}, fn
        {:@, _, [{:bit, _, [num]}]} = ast, acc -> {ast, Map.put(acc, "bit", num)}
        other, acc -> {other, acc}
      end)

    acc
  end
end
