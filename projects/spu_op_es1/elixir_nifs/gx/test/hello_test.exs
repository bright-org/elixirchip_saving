defmodule HelloTest do
  use ExUnit.Case

  test "hello/0" do
    assert 1 == Hello.hello_nif()
  end
end
