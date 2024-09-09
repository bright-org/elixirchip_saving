defmodule Generator.Nif do
  def module_name(bit, op) do
    Module.concat([SpuNif, "#{String.capitalize(op)}#{bit}bit"])
  end
end
