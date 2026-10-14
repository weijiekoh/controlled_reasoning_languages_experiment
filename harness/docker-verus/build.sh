#!/bin/sh
# Build cotml-verus. The claude binary comes from harness/docker (named build context).
set -eu
cd "$(dirname "$0")/../.."
exec docker buildx build --load -t cotml-verus --build-context claude=harness/docker harness/docker-verus
