# Verus sandbox for the AlgoVeri Verus track. Same user, WORKDIR and claude binary as harness/docker.
# Build (from repo root): harness/docker-verus/build.sh
# Verus 0.2025.01.13.da1c777 is the version in the AlgoVeri README; its toolchain is Rust 1.79.0
# (rust-toolchain.toml at da1c777). Both are fetched at build time and checked by SHA-256.

FROM debian:bookworm-slim AS fetch
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl unzip \
    && rm -rf /var/lib/apt/lists/*
ARG VERUS_VER=0.2025.01.13.da1c777
ARG VERUS_SHA256=239538605b3e18b047d4d70fe2fbb653abb507a46df364ad594eab63843abe4e
ARG RUSTUP_VER=1.27.1
ARG RUSTUP_SHA256=6aeece6993e902708983b209d04c0d1dbb14ebb405ddb87def578d41f920f56d
ARG RUST_TC=1.79.0-x86_64-unknown-linux-gnu
RUN curl -fsSLo /tmp/verus.zip \
      "https://github.com/principled-systems/verus/releases/download/release%2Frolling%2F${VERUS_VER}/verus-${VERUS_VER}-x86-linux.zip" \
    && echo "${VERUS_SHA256}  /tmp/verus.zip" | sha256sum -c - \
    && unzip -q /tmp/verus.zip -d /opt && mv /opt/verus-x86-linux /opt/verus && rm /tmp/verus.zip
ENV RUSTUP_HOME=/opt/rust/rustup CARGO_HOME=/opt/rust/cargo
RUN curl -fsSLo /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/${RUSTUP_VER}/x86_64-unknown-linux-gnu/rustup-init" \
    && echo "${RUSTUP_SHA256}  /tmp/rustup-init" | sha256sum -c - \
    && chmod +x /tmp/rustup-init \
    && /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain "${RUST_TC}" \
    && rm /tmp/rustup-init \
    && rm -rf /opt/rust/rustup/downloads /opt/rust/rustup/tmp /opt/rust/rustup/toolchains/*/share/doc

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates git bash coreutils procps ripgrep \
    && rm -rf /var/lib/apt/lists/*
COPY --from=claude claude /usr/local/bin/claude
COPY --from=fetch /opt/verus /opt/verus
COPY --from=fetch /opt/rust /opt/rust
RUN useradd -m -u 1000 agent
ENV RUSTUP_HOME=/opt/rust/rustup CARGO_HOME=/opt/rust/cargo \
    PATH=/opt/verus:/opt/rust/cargo/bin:/usr/local/bin:/usr/bin:/bin \
    DISABLE_AUTOUPDATER=1
USER agent
WORKDIR /work
