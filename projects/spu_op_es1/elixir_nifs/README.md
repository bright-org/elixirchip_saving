# フォルダ構成

gx: コード生成のフックとなるカスタムMixタスクを提供します。`fastlib`フォルダ内のコードをSPUを利用するコードとして先にコンパイルします。
verilatorx: verilatorによるシミュレーションを行うためのファイル群です。現状は単なるファイルコピーを行います。

gx_sample:上記プロジェクトを利用するサンプルプロジェクトです。

# 環境構築

動作確認した環境情報

- MacOS: 14.1.2（23B92）
- Docker Desktop v4.33.0

```bash
$ cd (任意のパス)/elixir_fpga_eva/projects/spu_op_es1/elixir_nifs
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
69d433a2fc5f   elixirchip-app   "iex"     2 days ago   Up 2 days   0.0.0.0:4000->4000/tcp   elixir-nif-sample

$ docker exec -it elixir-nif-sample bash
root@69d433a2fc5f:/#
```

```bash 
$ cd /src/elixir_nifs/gx_sample
$ iex -S mix
```

コンパイル後にiexを起動します。

```bash
$ iex -S mix
iex> Spu.nif_elixirchip_es1_spu_op_acc_create
0
``` 