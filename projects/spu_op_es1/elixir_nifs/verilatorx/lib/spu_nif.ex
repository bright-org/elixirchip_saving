defmodule SpuNif do
  @on_load :load_nifs

  def load_nifs do
    so =
      Path.join(Mix.Project.build_path(), "priv")

    :erlang.load_nif(~c"#{so}/acc_8bit", 0)
  end

  def create(_name) do
    raise "NIF fast_compare/2 not implemented"
  end

  @doc """
  パラメータヒントは下記。

  https://github.com/bright-org/elixirchip_saving/blob/1e71f3becdbb79de28060521ff70e26a3eca6bd0/projects/spu_op_es1/wrapper/elixirchip_es1_spu_op_acc/elixirchip_es1_spu_op_acc_wrapper.sv#L22-L31
  """
  def acc_clk(
        _resource,
        _s_sub,
        _s_carry,
        _s_data,
        _s_clear,
        _s_valid,
        _m_carry,
        _m_data
      ) do
    raise "not implemented"
  end
end
