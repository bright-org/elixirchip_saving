defmodule Test do
  use ExUnit.Case

  test "sub" do
    {:ok, ret} = SpuNif.ElixirchipEs1SpuOpSub.create("test")

    assert {:ok, _, _, _} =
             SpuNif.ElixirchipEs1SpuOpSub.clk(
               ret,
               1,
               3,
               1,
               0,
               1,
               0,
               1,
               0
             )
             |> dbg()
  end

  test "add" do
    {:ok, ret} = SpuNif.ElixirchipEs1SpuOpAdd.create("test")

    assert {:ok, _, _, _} =
             SpuNif.ElixirchipEs1SpuOpAdd.clk(
               ret,
               0,
               1,
               3,
               0,
               1,
               0,
               0,
               0
             )
             |> dbg()
  end
end
