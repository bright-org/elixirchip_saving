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

    replace("acc", bit)
    __replace__(bit, "CMakeLists.txt")
    __replace__(bit, "spu/CMakeLists.txt")
    __replace__(bit, "spu/acc/CMakeLists.txt", "spu/acc_#{bit}bit/CMakeLists.txt")
    __replace__(bit, "spu_nif/CMakeLists.txt")
    __replace__(bit, "spu_nif/acc/CMakeLists.txt", "spu_nif/acc_#{bit}bit/CMakeLists.txt")
  end

  def replace(op, bit) do
    [
      {"wrapper.sv", "spu"},
      {"wrapper.h", "spu"},
      {"wrapper.cpp", "spu"},
      {"call.cpp", "spu_nif"}
    ]
    |> Enum.map(&__replace__(op, bit, &1))
  end

  defp __replace__(op, bit, {path, dir}) do
    fin_path =
      "#{dir}/#{op}/#{path}"

    fout_path =
      "#{dir}/#{op}_#{bit}bit/#{Path.basename(path)}"

    __replace__(bit, fin_path, fout_path)
  end

  defp __replace__(bit, fin_path, fout_path) do
    {:ok, target} = File.read(template_path(fin_path))

    str =
      Regex.replace(~r/#\{(\w+)\}/, target, fn _, key ->
        case key do
          "bit" -> "#{bit}"
          _ -> ""
        end
      end)

    File.write(output_path(fout_path), str)
  end

  defp __replace__(bit, fin_path) do
    __replace__(bit, fin_path, fin_path)
  end
end
