# Agent and verifier sandbox. Lean toolchain and Mathlib are bind-mounted read-only at run time.
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates git bash coreutils procps ripgrep \
    && rm -rf /var/lib/apt/lists/*
COPY claude /usr/local/bin/claude
RUN useradd -m -u 1000 agent
# Host paths, baked in so the bind mounts land at the same path. Build with harness/docker/build.sh.
ARG TC
ARG LE
ENV TC=$TC
ENV LE=$LE
ENV PATH=$TC/bin:/usr/local/bin:/usr/bin:/bin \
    LEAN_PATH=$LE/packages/Cli/.lake/build/lib/lean:$LE/packages/batteries/.lake/build/lib/lean:$LE/packages/Qq/.lake/build/lib/lean:$LE/packages/aesop/.lake/build/lib/lean:$LE/packages/proofwidgets/.lake/build/lib/lean:$LE/packages/importGraph/.lake/build/lib/lean:$LE/packages/LeanSearchClient/.lake/build/lib/lean:$LE/packages/plausible/.lake/build/lib/lean:$LE/packages/mathlib/.lake/build/lib/lean:$LE/build/lib/lean:$TC/lib/lean \
    DISABLE_AUTOUPDATER=1
USER agent
WORKDIR /work
