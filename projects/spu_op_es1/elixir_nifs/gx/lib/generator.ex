defmodule Generator do
  defp __template_path__, do: Path.join(Mix.Project.build_path(), "/priv/template")
  def template_path(name), do: Path.join(__template_path__(), name)

  defp __output_path__, do: Path.join(Mix.Project.build_path(), "/priv/cmake")
  def output_path(name), do: Path.join(__output_path__(), name)

  def run() do
    bit = 8

    unless(File.exists?(__output_path__())) do
      File.mkdir_p(__output_path__() <> "/spu/acc_#{bit}bit")
      File.mkdir_p(__output_path__() <> "/spu_nif/acc_#{bit}bit")
    end

    IO.puts("Generating files...")

    hardware = %{
      "bit" => "#{bit}",
      "op" => "acc"
    }

    template_files = [
      {"wrapper.sv", "spu"},
      {"wrapper.h", "spu"},
      {"wrapper.cpp", "spu"},
      {"call.cpp", "spu_nif"}
    ]

    compile(hardware, template_files)
    __compile__(hardware, "CMakeLists.txt")
    __compile__(hardware, "spu/CMakeLists.txt")
    __compile__(hardware, "spu/acc/CMakeLists.txt", "spu/acc_#{bit}bit/CMakeLists.txt")
    __compile__(hardware, "spu_nif/CMakeLists.txt")
    __compile__(hardware, "spu_nif/acc/CMakeLists.txt", "spu_nif/acc_#{bit}bit/CMakeLists.txt")
  end

  def compile(hardware, template_files) do
    template_files
    |> Enum.map(&__compile_dynamic_path__(hardware, &1))
  end

  defp __compile_dynamic_path__(hardware, {path, dir}) do
    %{
      "bit" => bit,
      "op" => op
    } = hardware

    fin_path =
      "#{dir}/#{op}/#{path}"

    fout_path =
      "#{dir}/#{op}_#{bit}bit/#{op}_#{bit}bit#{Path.extname(path)}"

    __compile__(hardware, fin_path, fout_path)
  end

  defp __compile__(hardware, fin_path, fout_path) do
    embed_parameters!(hardware, fin_path)
    |> then(&File.write(output_path(fout_path), &1))
  end

  defp __compile__(hardware, fin_path) do
    __compile__(hardware, fin_path, fin_path)
  end

  @doc """
  パラメーターを埋め込む
  """
  def embed_parameters!(hardware, path) do
    File.read!(template_path(path))
    |> then(
      &Regex.replace(~r/#\{(\w+)\}/, &1, fn _, key ->
        Map.get(hardware, key, "")
      end)
    )
  end
end
