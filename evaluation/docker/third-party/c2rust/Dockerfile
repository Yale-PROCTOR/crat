# c2rust 0.21.0-p1: upstream c2rust v0.21.0 (93471e6) + c2rust-0.21.0-p1.patch (13 lines: the emitted rust-toolchain
# file, and a cast on a subscripted pointer whose element type differs from the expected one). The patched source tree
# is checked by its git tree hash, e2631f82, before building. Built as the evaluation's translator of the eight was:
#   base   ubuntu:22.04 pinned by digest; LLVM/clang 14 from the 22.04 archive (versions printed in the build log)
#   rust   the repository's toolchain channel nightly-2022-08-08, with rustc-dev / rust-src / rustfmt
#   deps   Cargo.lock vendored by a current stable cargo, then built --locked --offline by the pinned nightly
FROM ubuntu:22.04@sha256:104ae83764a5119017b8e8d6218fa0832b09df65aae7d5a6de29a85d813da2fb
ARG JOBS=8
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
 && apt-get install -y --no-install-recommends build-essential cmake pkg-config libssl-dev python3 git curl ca-certificates \
      llvm-14-dev clang-14 libclang-14-dev \
 && rm -rf /var/lib/apt/lists/* \
 && dpkg-query -W -f='${Package}\t${Version}\n' 'llvm-14*' clang-14 'libclang*14*' libc6-dev gcc cmake | sort
ENV LLVM_CONFIG_PATH=/usr/bin/llvm-config-14 LIBCLANG_PATH=/usr/lib/llvm-14/lib PATH=/root/.cargo/bin:$PATH
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain none \
 && rustup toolchain install nightly-2022-08-08 --profile minimal --component rustc-dev,rust-src,rustfmt \
 && rustup toolchain install stable --profile minimal \
 && rustc +nightly-2022-08-08 -V && cargo +stable -V
COPY c2rust-0.21.0-p1.patch /src/
RUN git clone --quiet --depth 1 --branch v0.21.0 https://github.com/immunant/c2rust.git /src/c2rust \
 && cd /src/c2rust && test "$(git rev-parse HEAD)" = 93471e6bbdca883d7c18383cc842a07812e6e11e \
 && git apply /src/c2rust-0.21.0-p1.patch && git add -A && test "$(git write-tree)" = e2631f82b071455cd72a7cd50ccdb61723b78252 \
 && rm -rf .git && mkdir -p .cargo \
 && cargo +stable vendor --locked --versioned-dirs /src/vendor > .cargo/config.toml && cat .cargo/config.toml
RUN cd /src/c2rust && cargo +nightly-2022-08-08 build --release --locked --offline -j ${JOBS} -p c2rust \
 && install -m 0755 target/release/c2rust target/release/c2rust-transpile /usr/local/bin/ \
 && c2rust --version && sha256sum /usr/local/bin/c2rust /usr/local/bin/c2rust-transpile \
 && rm -rf target /root/.cargo/registry
WORKDIR /work
