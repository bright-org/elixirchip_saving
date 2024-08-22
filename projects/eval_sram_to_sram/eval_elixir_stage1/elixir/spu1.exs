defmodule StreamProcessingUnit do
  def generate(operator) do
    prologue() <> body(operator) <> epilogue()
  end

  def usage() do
    """
    Usage: elixir spu.exs OPERATOR [CONSTANTS]
    """
  end

  defp prologue() do
    """
    module stream_processing_unit
            (
                // system
                input   var logic           reset,      // リセット
                input   var logic           clk,        // クロック
                input   var logic           cke,        // クロックイネーブル

                // input port
                input   var logic   [63:0]  s_data0,    // source0
                input   var logic   [63:0]  s_data1,    // source1
                input   var logic           s_valid,    // データ有効

                // output port
                output  var logic   [63:0]  m_data0,    // destination0
                output  var logic   [63:0]  m_data1,    // destination1
                output  var logic           m_valid     // データ有効
            );

        always_ff @(posedge clk) begin
            if ( reset ) begin
                m_data0 <= 'x;
                m_data1 <= 'x;
                m_valid <= 1'b0;
            end
            else if ( cke ) begin
                for ( int i = 0; i < 8; i++ ) begin
    """
  end

  defp epilogue() do
    """
                end
                m_valid <= s_valid;
            end
        end
    endmodule
    """
  end

  defp body(:add) do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] + s_data1[i*8 +: 8];
    """
  end

  defp body({:add, n}) when is_integer(n) and n >= 0 and n < 256 do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] + #{n};
    """
  end

  defp body(:subtract) do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] - s_data1[i*8 +: 8];
    """
  end

  defp body({:subtract, n}) when is_integer(n) and n >= 0 and n < 256 do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] - #{n};
    """
  end

  defp body(:bitwise_and) do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] & s_data1[i*8 +: 8];
    """
  end

  defp body({:bitwise_and, n}) when is_integer(n) and n >= 0 and n < 256 do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] & #{n};
    """
  end

  defp body(:bitwise_or) do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] | s_data1[i*8 +: 8];
    """
  end

  defp body({:bitwise_or, n}) when is_integer(n) and n >= 0 and n < 256 do
    """
                    m_data0[i*8 +: 8] <= s_data0[i*8 +: 8] | #{n};
    """
  end
end

args = System.argv()

case Enum.count(args) do
  1 ->
   args
   |> hd()
   |> String.to_atom()
   |> StreamProcessingUnit.generate()
   |> IO.puts()

  2 ->
   [operator, constant] = args
   operator = String.to_atom(operator)
   constant = String.to_integer(constant)

   {operator, constant}
   |> StreamProcessingUnit.generate()
   |> IO.puts()

  _ -> StreamProcessingUnit.usage() |> IO.puts()
end
