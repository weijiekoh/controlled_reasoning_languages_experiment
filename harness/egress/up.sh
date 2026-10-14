#!/usr/bin/env bash
# Create internal network cotml-egress and (re)start proxy cotml-proxy.
# Idempotent: safe to run again; the proxy is always recreated.
set -euo pipefail

NET=cotml-egress
PROXY=cotml-proxy
SQUID_IMAGE=ubuntu/squid:6.13-25.04_beta
CURL_IMAGE=curlimages/curl:8.11.1
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# 1. Network: must exist and be internal.
if docker network inspect "$NET" >/dev/null 2>&1; then
  internal="$(docker network inspect -f '{{.Internal}}' "$NET")"
  if [ "$internal" != "true" ]; then
    echo "ERROR: network $NET exists but is not --internal. Run down.sh first." >&2
    exit 1
  fi
else
  # Fixed bridge interface name: lets a host firewall rule target this network.
  docker network create --internal --label cotml=egress \
    -o com.docker.network.bridge.name=br-cotml-egress "$NET" >/dev/null
  echo "created network $NET (internal)"
fi

# 2. Proxy: recreate. Attach to bridge (egress) first, then to cotml-egress.
docker rm -f "$PROXY" >/dev/null 2>&1 || true
docker run -d --name "$PROXY" \
  --label cotml=egress \
  --network bridge \
  --restart unless-stopped \
  --read-only \
  --tmpfs /var/log/squid:uid=13,gid=13,mode=0755 \
  --tmpfs /var/spool/squid:uid=13,gid=13,mode=0755 \
  --tmpfs /run:mode=0755 \
  --tmpfs /tmp \
  --tmpfs /etc/ssl/private \
  --cap-drop ALL \
  --cap-add SETUID --cap-add SETGID --cap-add CHOWN --cap-add DAC_OVERRIDE --cap-add FOWNER \
  --security-opt no-new-privileges \
  -v "$HERE/squid.conf:/etc/squid/squid.conf:ro" \
  "$SQUID_IMAGE" >/dev/null
docker network connect "$NET" "$PROXY"

# 3. Wait until the proxy answers on cotml-egress.
for _ in $(seq 1 30); do
  code="$(docker run --rm --network "$NET" "$CURL_IMAGE" \
            -s -o /dev/null -w '%{http_code}' --max-time 2 http://$PROXY:8888/ 2>/dev/null || true)"
  if [ -n "$code" ] && [ "$code" != "000" ]; then
    echo "proxy $PROXY up on $NET (probe HTTP $code)"
    exit 0
  fi
  sleep 1
done
echo "ERROR: proxy $PROXY did not answer. See: docker logs $PROXY" >&2
exit 1
