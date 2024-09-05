defmodule SpuTest do
  use ExUnit.Case

  alias SpuNif, as: SpuNif

  test "create/1" do
    assert {:ok, _} = SpuNif.create("test")
  end

  test "test acc1 of example.cpp" do
    {:ok, res} = SpuNif.create("test")

    # add 10
    assert {:ok, 0, 10} =
             {_ok, m_carry, m_data} =
             SpuNif.acc_clk(
               res,
               0,
               0,
               10,
               0,
               1,
               0,
               0
             )

    # add 2
    assert {:ok, 0, 12} =
             {_ok, _m_carry, _m_data} =
             SpuNif.acc_clk(
               res,
               0,
               0,
               2,
               0,
               1,
               m_carry,
               m_data
             )
  end

  test "test acc2 of example.cpp" do
    {:ok, res} = SpuNif.create("test")

    # add 10
    assert {:ok, 0, 20} =
             {_ok, m_carry, m_data} =
             SpuNif.acc_clk(
               res,
               0,
               0,
               20,
               0,
               1,
               0,
               0
             )

    # sub 3
    assert {:ok, 1, 17} =
             {_ok, _m_carry, _m_data} =
             SpuNif.acc_clk(
               res,
               1,
               1,
               3,
               0,
               1,
               m_carry,
               m_data
             )
  end
end
