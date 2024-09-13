defmodule Mix.Tasks.Compile.Defg do
  use Mix.Task

  @doc """
      任意のフォルダをコンパイルするのではなく、指定のキーワードを持つElixirコードのみを
      コンパイル対象として抽出(未完成)
  """

  @impl Mix.Task
  def run(_) do
    # ソースファイルのパス
    source_files =
      Path.wildcard("lib/**/*.ex")
      |> IO.inspect()

    Enum.each(source_files, fn file ->
      {:ok, ast} = File.read!(file) |> Code.string_to_quoted()

      # ASTを走査してdefnを探す
      extract_defn_functions(ast)
      |> IO.inspect()
      |> Enum.each(fn defn_ast ->
        IO.puts("Compiling #{inspect(defn_ast)}")
        Code.eval_quoted(defn_ast, [], __ENV__)
      end)
    end)
  end

  defp extract_defn_functions({:defmodule, _, [{_mod_name, _, _}, [do: do_block]]}) do
    do_block
    |> extract_defn_functions()
  end

  defp extract_defn_functions({:__block__, _, body}) when is_list(body) do
    Enum.filter(body, fn
      {:defg, _, _} -> true
      _ -> false
    end)
  end
end
