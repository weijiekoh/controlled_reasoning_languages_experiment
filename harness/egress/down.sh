#!/usr/bin/env bash
# Remove proxy cotml-proxy and network cotml-egress.
# Fails if other containers are still attached to cotml-egress.
set -euo pipefail

docker rm -f cotml-proxy >/dev/null 2>&1 && echo "removed container cotml-proxy" || true
if docker network inspect cotml-egress >/dev/null 2>&1; then
  docker network rm cotml-egress >/dev/null && echo "removed network cotml-egress"
fi
