defmodule Defg do
  @doc """
  Nx.Defnを参考に記述

  defg := def generic
  """
  defmacro defg(call, do: block) do
    define_defg(:def, call, block, __CALLER__)
  end

  defp define_defg(kind, call, _block, _env) do
    quote do
      # unquote(__MODULE__).__define__(
      #   __MODULE__,
      #   unquote(kind),
      #   unquote(name),
      #   unquote(arity),
      #   :numerical,
      #   %{unquote_splicing(defaults)}
      # )

      # unquote(kind)(unquote(call)) do
      #   unquote(block)
      # end
      unquote(kind)(unquote(call)) do
        Spu.reduce("test", 0, 10)
      end
    end
  end
end
