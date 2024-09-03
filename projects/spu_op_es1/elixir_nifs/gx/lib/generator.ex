defmodule Generator do
  def base_path, do: Path.join(Mix.Project.build_path(), "/priv/cmake")
  def join_base_path(name), do: Path.join(base_path(), name)

  def run() do
    unless(File.exists?(base_path())) do
      File.mkdir_p(base_path() <> "/spu")
      File.mkdir_p(base_path() <> "/spu_nif")
    end

    IO.puts("Generating files...")

    Generator.Sv.sv()
  end

  def super_cmakelist() do
    File.write!(join_base_path("CMakeLists.txt"), """
    cmake_minimum_required(VERSION 3.16)
    project(EXAMPLE)

    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY $ENV{MIX_APP_PATH}/priv)
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY $ENV{MIX_APP_PATH}/priv)

    set(CMAKE_CXX_STANDARD 14)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)
    set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -shared -fPIC -Wall -pthread -I$ENV{ERTS_INCLUDE_DIR}")
    set(CMAKE_BUILD_TYPE Release)

    add_subdirectory(spu)
    add_subdirectory(spu_nif)
    """)
  end
end
