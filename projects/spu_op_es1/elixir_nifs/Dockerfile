FROM erlang:27

# elixir expects utf8.
ENV ELIXIR_VERSION="v1.17.2" \
	LANG=C.UTF-8

ENV TERM xterm-256color

RUN set -xe \
	&& ELIXIR_DOWNLOAD_URL="https://github.com/elixir-lang/elixir/archive/${ELIXIR_VERSION}.tar.gz" \
	&& ELIXIR_DOWNLOAD_SHA256="7bb8e6414b77c1707f39f620a2ad54f68d64846d663ec78069536854247fb1ab" \
	&& curl -fSL -o elixir-src.tar.gz $ELIXIR_DOWNLOAD_URL \
	&& echo "$ELIXIR_DOWNLOAD_SHA256  elixir-src.tar.gz" | sha256sum -c - \
	&& mkdir -p /usr/local/src/elixir \
	&& tar -xzC /usr/local/src/elixir --strip-components=1 -f elixir-src.tar.gz \
	&& rm elixir-src.tar.gz \
	&& cd /usr/local/src/elixir \
	&& make install clean \
	&& find /usr/local/src/elixir/ -type f -not -regex "/usr/local/src/elixir/lib/[^\/]*/lib.*" -exec rm -rf {} + \
	&& find /usr/local/src/elixir/ -type d -depth -empty -delete

# https://zenn.dev/ndjndj/articles/65f11bd69a97e2#cmake-%E3%82%92-install-%E3%81%99%E3%82%8B
RUN apt-get update && \
    apt-get -y install build-essential && \
    apt-get install -y wget && \
    wget https://github.com/Kitware/CMake/releases/download/v3.28.1/cmake-3.28.1-linux-x86_64.sh -q -O /tmp/cmake-install.sh && \
    chmod u+x /tmp/cmake-install.sh && \
    mkdir /opt/cmake-3.28.1 && \
    /tmp/cmake-install.sh --skip-license --prefix=/opt/cmake-3.28.1 && \
    rm /tmp/cmake-install.sh && \
    ln -s /opt/cmake-3.28.1/bin/* usr/local/bin

# Verilogのシミュレーター
RUN apt-get -y install verilator

# Elixir NIFsに必要
RUN apt-get -y install erlang-dev

CMD ["iex"]

