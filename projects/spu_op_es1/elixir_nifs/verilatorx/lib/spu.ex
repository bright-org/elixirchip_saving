defmodule Spu do
  # defp add_map(s_data, s_carry, m_data \\ 0, m_carry \\ 0) do
  #   %{
  #     # 0..add, 1..sub
  #     s_sub: 0,
  #     s_carry: 0,
  #     # 入力
  #     s_data: 0,
  #     # クリアフラグ
  #     s_clear: 0,
  #     # 1の時有効データ
  #     s_valid: 0,
  #     # キャリー
  #     m_carry: m_carry,
  #     # 出力データ
  #     m_data: m_data
  #   }
  # end

  def reduce(name, _acc, num) do
    {:ok, context} = SpuNif.create(name)

    {_ok, m_carry, m_data} =
      SpuNif.acc_clk(
        context,
        0,
        0,
        num,
        0,
        1,
        0,
        0
      )

    {m_carry, m_data}
  end
end
