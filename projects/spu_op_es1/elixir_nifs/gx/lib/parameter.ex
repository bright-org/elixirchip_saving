defmodule Parameter do
  def extract(ast, acc = %{}) do
    {ast, acc} =
      Macro.postwalk(ast, %{}, fn
        {:@, _, [{:bit, _, [num]}]} = ast, acc -> {ast, Map.put(acc, "bit", num)}
        other, acc -> {other, acc}
      end)

    acc
  end
end
