defmodule Mix.Tasks.Compile.Burn do
  # import Generator

  require Logger

  @folder "fastlib"
  @doc """
    任意のフォルダのASTを取得してファイル出力
  """
  def run(_args) do
    # src/ フォルダ内のすべての .ex ファイルをコンパイルする
    files = Path.wildcard("#{@folder}/**/*.ex")
    Mix.shell().info(Mix.Project.app_path())

    if files == [] do
      Mix.shell().error("No .ex files found in the folder: #{@folder}")
    else
      Mix.shell().info("Compiling .ex files in #{@folder}...")

      files
      |> Enum.each(&parse_file/1)
    end
  end

  defp parse_file(file_path) do
    # ファイルの内容を読み込む
    file_content = File.read!(file_path)

    # ファイル内容をASTに変換
    {:ok, ast} = Code.string_to_quoted(file_content)

    Mix.shell().info("AST for #{file_path}:")
    IO.inspect(ast, pretty: true)

    Generator.run()
  end
end
