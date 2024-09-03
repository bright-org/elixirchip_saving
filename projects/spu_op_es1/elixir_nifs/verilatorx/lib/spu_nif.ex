defmodule SpuNif do
  @on_load :load_nifs

  def load_nifs do
    so =
      Path.join(Mix.Project.app_path(), "priv")

    :erlang.load_nif(~c"#{so}/spu", 0)
  end

  def create(_name) do
    raise "NIF fast_compare/2 not implemented"
  end

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
