#!/usr/bin/env bash
# Build the agent sandbox image. The Lean toolchain and lean_env/.lake are bind-mounted at run time at
# the same host paths, so the image needs them at build time. Needs harness/docker/claude (the Claude Code
# binary; copy it from `which claude`, or download the native build).
set -eu
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
TC="${COTML_TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}"
docker build --build-arg "TC=$TC" --build-arg "LE=$root/lean_env/.lake" -t cotml-sandbox "$here"
