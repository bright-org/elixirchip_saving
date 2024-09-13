defmodule Generator.Nif do
  def module_name(_bit, op) do
    name =
      op
      |> String.split("_")
      |> Enum.map(&String.capitalize/1)
      |> Enum.join("")

    Module.concat([SpuNif, name])
  end
end
