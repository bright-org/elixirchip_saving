# フォルダ構成

`gx`: コード生成のフックとなるカスタムMixタスクを提供します。`fastlib`フォルダ内のコードをSPUを利用するコードとして先にコンパイルします。  
`verilatorx`: verilatorによるシミュレーションを行うためのファイル群です。  
現状はcmake配下のファイル群をテンプレートファイルとして、Elixirからパラメータ埋め込みを行います。（途中）  

`gx_sample`:上記プロジェクトを利用するサンプルプロジェクトです。

# 環境構築

動作確認した環境情報

- MacOS: 14.1.2（23B92）
- Docker Desktop v4.33.0

```bash
$ cd (your parh)/projects/spu_op_es1/elixir_nifs
$ docker compose up -d
```

`docker ps`で何かコンテナが起動してたらOK

```
CONTAINER ID   IMAGE            COMMAND   CREATED      STATUS      PORTS                    NAMES
69d433a2fc5f   elixirchip-app   "iex"     2 days ago   Up 2 days   0.0.0.0:4000->4000/tcp   elixir-nif-sample
```

## コンパイル手順

コンテナ名を確認してコンテナ内のbashにアクセスします

```bash
$ docker ps
CONTAINER ID   IMAGE            COMMAND   CREATED      STATUS      PORTS                    NAMES
example   elixirchip-app   "iex"     2 days ago   Up 2 days   0.0.0.0:4000->4000/tcp   elixir-nif-sample

$ docker exec -it elixir-nif-sample bash
root@example:/#
```

先に`mix deps.get`しておきます。

```bash
root@example:/# cd src/elixir_nifs/gx_sample
root@example:/# mix deps.get
```

## テスト

`projects/spu_op_es1/elixir_nifs/run.sh`を実行します。

デフォルトでは`elixirchip_es1_spu_op_add`がElixirから利用できるようになります。
モジュールを大量にビルドするとメモリを使い潰してしまうため、使いたいものだけ記載します。

```bash 
root@example:/# cd /src/elixir_nifs
root@example:/src/elixir_nifs# ./run.sh

（コンパイルログが流れます）

iex> SpuNif.ElixirchipEs1SpuOpAdd.create("test")
{:ok, Reference<>}
```

### サンプル

コードの利用例は元の*.svファイルを参考にしてください。
ExUnitでの記載方法は下記を参考にしてください。

[elixirchip_es1_spu_op_add_test.exs](./gx_sample/test/elixirchip_es1_spu_op_add_test.exs)