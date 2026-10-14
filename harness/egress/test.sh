#!/usr/bin/env bash
# Prove the egress allowlist. Prints one PASS/FAIL line per check.
# Exit status: 0 if all checks pass, 1 otherwise. Run up.sh first.
set -uo pipefail

NET=cotml-egress
PROXY_URL=http://cotml-proxy:8888
CURL_IMAGE=curlimages/curl:8.11.1
PROXY_ENV=(-e HTTPS_PROXY=$PROXY_URL -e https_proxy=$PROXY_URL
           -e HTTP_PROXY=$PROXY_URL -e http_proxy=$PROXY_URL
           -e NO_PROXY=localhost,127.0.0.1 -e no_proxy=localhost,127.0.0.1)
fails=0

# probe <env: proxy|none> <curl args...>
# Prints "<curl exit> <HTTP status> <CONNECT status>".
probe() {
  local mode=$1; shift
  local envs=()
  [ "$mode" = proxy ] && envs=("${PROXY_ENV[@]}")
  local out rc
  out="$(docker run --rm --network "$NET" "${envs[@]}" "$CURL_IMAGE" \
          -s -o /dev/null --max-time 10 -w '%{http_code} %{http_connect}' "$@")"
  rc=$?
  echo "$rc $out"
}

report() { # report <PASS|FAIL> <name> <detail>
  printf '%s  %-58s %s\n' "$1" "$2" "$3"
  [ "$1" = PASS ] || fails=$((fails + 1))
}

check_allowed() { # check_allowed <name> <url>
  read -r rc code conn < <(probe proxy "$2")
  if [ "$rc" = 0 ] && [ "$code" != 000 ]; then report PASS "$1" "(HTTP $code)"
  else report FAIL "$1" "(curl rc=$rc http=$code connect=$conn)"; fi
}

check_denied() { # check_denied <name> <curl args...>; expects proxy 403
  local name=$1; shift
  read -r rc code conn < <(probe proxy "$@")
  if [ "$conn" = 403 ] || { [ "$code" = 403 ] && [ "$conn" = 000 ]; }; then
    report PASS "$name" "(proxy 403, curl rc=$rc)"
  else report FAIL "$name" "(curl rc=$rc http=$code connect=$conn)"; fi
}

check_unreachable() { # check_unreachable <name> <url>; expects no connection
  read -r rc code conn < <(probe none "$2")
  if [ "$rc" != 0 ] && [ "$code" = 000 ]; then report PASS "$1" "(curl rc=$rc)"
  else report FAIL "$1" "(curl rc=$rc http=$code)"; fi
}

if ! docker inspect -f '{{.State.Running}}' cotml-proxy 2>/dev/null | grep -qx true; then
  echo "FAIL  cotml-proxy is not running. Run up.sh first."; exit 1
fi
if [ "$(docker network inspect -f '{{.Internal}}' "$NET" 2>/dev/null)" != true ]; then
  echo "FAIL  network $NET missing or not internal. Run up.sh first."; exit 1
fi

echo "== (1) allowed host via proxy"
check_allowed "1  https://api.anthropic.com/v1/models via proxy" https://api.anthropic.com/v1/models

echo "== (2) other HTTPS hosts via proxy"
check_denied "2a https://github.com via proxy refused" https://github.com
check_denied "2b https://example.com via proxy refused" https://example.com
check_denied "2c CONNECT to IP literal of api.anthropic.com refused" -k https://160.79.104.10/
check_denied "2d CONNECT api.anthropic.com:80 (non-443) refused" -p http://api.anthropic.com:80/

echo "== (3) no proxy env: no route, no DNS"
check_unreachable "3a https://api.anthropic.com direct fails" https://api.anthropic.com/v1/models
check_unreachable "3b https://example.com direct fails" https://example.com
check_unreachable "3c https://1.1.1.1 direct (no DNS needed) fails" https://1.1.1.1
check_unreachable "3d http://93.184.215.14 direct fails" http://93.184.215.14
if docker run --rm --network "$NET" --entrypoint nslookup "$CURL_IMAGE" example.com >/dev/null 2>&1; then
  report FAIL "3e external DNS lookup (example.com) fails" "(resolved)"
else report PASS "3e external DNS lookup (example.com) fails" "(nslookup rc!=0)"; fi

echo "== (4) plain HTTP via proxy"
check_denied "4a http://example.com via proxy refused" http://example.com/
check_denied "4b http://api.anthropic.com (non-CONNECT) refused" http://api.anthropic.com/

echo "== (5) denials logged"
if docker exec cotml-proxy grep -q 'TCP_DENIED/403 CONNECT github.com:443' /var/log/squid/access.log; then
  report PASS "5  proxy access.log records TCP_DENIED" ""
else report FAIL "5  proxy access.log records TCP_DENIED" ""; fi

echo
if [ "$fails" -eq 0 ]; then echo "ALL CHECKS PASSED"; exit 0
else echo "$fails CHECK(S) FAILED"; exit 1; fi
