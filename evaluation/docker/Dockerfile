# The evaluation's image: the translator built from this source tree, its pinned toolchain and solver, the Miri
# toolchain of RQ3, Python 3 and the counters of RQ1. Build from the source root (the directory holding Cargo.toml):
#   docker build -f artifact/Dockerfile -t jobcrat-artifact .
# Every download is pinned: the base image by digest, the toolchains by date, the solver wheel and cloc by SHA-256,
# the crates by the lockfiles (--locked).
FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac

ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8
RUN apt-get update \
 && apt-get install -y --no-install-recommends build-essential ca-certificates clang curl libclang-dev make perl \
      pkg-config python3 python3-venv time unzip \
 && rm -rf /var/lib/apt/lists/*

# z3 4.15.4 from its Python wheel: the library the translator links (on the loader path, since the top-level
# wrapper sets LD_LIBRARY_PATH to the rustc sysroot only), its headers, and the z3 module for the setup keys.
RUN python3 -m venv /opt/venv \
 && echo 'z3-solver==4.15.4.0 --hash=sha256:7e103a6f203f505b8b8b8e5c931cc407c95b61556512d4921c1ddc0b3f41b08e' > /tmp/z3.txt \
 && /opt/venv/bin/pip install --no-cache-dir --require-hashes -r /tmp/z3.txt && rm /tmp/z3.txt \
 && Z=$(/opt/venv/bin/python3 -c 'import os, z3; print(os.path.dirname(z3.__file__))') \
 && cp -a $Z/lib/libz3.so $Z/lib/libz3.so.4.15 /usr/local/lib/ && ldconfig \
 && mkdir -p /usr/local/include/z3 && cp -a $Z/include/. /usr/local/include/z3/
ENV Z3_SYS_Z3_HEADER=/usr/local/include/z3/z3.h Z3_LIBRARY_PATH_OVERRIDE=/usr/local/lib

# cloc 2.00 (the C and Rust line counts of the setup and of Table effect-inator): the release script, as npm's
# cloc@2.0.0-cloc ships it
RUN curl -fsSL -o /tmp/cloc.tgz https://registry.npmjs.org/cloc/-/cloc-2.0.0-cloc.tgz \
 && tar --warning=no-unknown-keyword -xzf /tmp/cloc.tgz -C /tmp package/lib/cloc \
 && install -m 755 /tmp/package/lib/cloc /usr/local/bin/cloc && rm -rf /tmp/cloc.tgz /tmp/package \
 && echo '2e8d7d57112b0af14d8578d8679423b6e82f1007b29f71c71510f0bc09563b95  /usr/local/bin/cloc' | sha256sum -c -

# The translator's toolchain (rust-toolchain.toml: the nightly and its components) and the Miri toolchain of RQ3,
# with Miri's sysroot built here so that the runs need no network.
ENV RUSTUP_HOME=/opt/rustup CARGO_HOME=/opt/cargo XDG_CACHE_HOME=/opt/cache PATH=/opt/venv/bin:/opt/cargo/bin:$PATH
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
      | sh -s -- -y --no-modify-path --profile minimal --default-toolchain none \
 && rustup toolchain install nightly-2025-06-23 --profile minimal \
      --component rustfmt,clippy,rust-src,rustc-dev,llvm-tools-preview \
 && rustup toolchain install nightly-2026-09-17 --profile minimal --component miri,rust-src \
 && rustup default nightly-2025-06-23 \
 && cargo +nightly-2026-09-17 miri setup

# The source tree: the translator (release), deps_crate (debug, where the translator looks for it), the crates
# the emitted programs depend on fetched for offline builds, and RQ1's two counters.
COPY . /jobcrat-source
WORKDIR /jobcrat-source
RUN cargo build --release --locked \
 && cargo build --locked --manifest-path deps_crate/Cargo.toml \
 && cargo fetch --locked --manifest-path deps_crate/Cargo.toml \
 && bash artifact/rq1/build.sh \
 && ./jobcrat --help > /dev/null

ENTRYPOINT ["artifact/run.sh"]
CMD ["--help"]
