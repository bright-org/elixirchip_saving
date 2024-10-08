defmodule GxSample.MixProject do
  use Mix.Project

  def project do
    [
      app: :gx_sample,
      version: "0.1.0",
      elixir: "~> 1.17",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      compilers: [:burn, :elixir_make] ++ Mix.compilers(),
      elixirc_paths: elixirc_paths(Mix.env())
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      # {:dep_from_hexpm, "~> 0.3.0"},
      # {:dep_from_git, git: "https://github.com/elixir-lang/my_dep.git", tag: "0.1.0"}
      {:elixir_make, "~> 0.4", runtime: false},
      {:gx, path: "../gx"},
      {:verilatorx, path: "../verilatorx"}
    ]
  end

  defp elixirc_paths(_), do: ["lib", "priv"]
end
