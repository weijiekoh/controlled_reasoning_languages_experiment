# Egress allowlist for sandbox containers

Sandbox containers reach only `api.anthropic.com:443`, through a proxy. All other egress fails.

## Design

| Part | Function |
|---|---|
| Network `cotml-egress` | Docker bridge network made with `--internal`. It has no route off the host. Docker's embedded DNS does not forward external names on it. Host interface: `br-cotml-egress`. |
| Container `cotml-proxy` | Squid 6.13 (`ubuntu/squid:6.13-25.04_beta`). Attached to `bridge` (for egress) and `cotml-egress` (for clients). Listens on `8888`. No port is published on the host. |
| `squid.conf` | Allows only `CONNECT api.anthropic.com:443`. Denies everything else, including plain HTTP, other ports, subdomains, and IP literals (`dstdomain -n` does no reverse lookup). |

Squid was chosen over tinyproxy because tinyproxy cannot limit requests by method. Tinyproxy lets plain `GET http://api.anthropic.com/` through. Squid applies the method, port, and domain conditions in one rule.

## Use

```sh
harness/egress/up.sh     # create network (if missing), recreate proxy, wait until ready
harness/egress/test.sh   # PASS/FAIL per check; exit 1 on any FAIL
harness/egress/down.sh   # remove proxy and network
```

`up.sh` is idempotent. It refuses to continue if `cotml-egress` exists but is not internal. `down.sh` fails if containers are still attached to `cotml-egress`.

## Runner flags

Add these flags to the `docker run` command for the `cotml-sandbox` container:

```sh
--network cotml-egress \
-e HTTPS_PROXY=http://cotml-proxy:8888 -e https_proxy=http://cotml-proxy:8888 \
-e HTTP_PROXY=http://cotml-proxy:8888  -e http_proxy=http://cotml-proxy:8888 \
-e NO_PROXY=localhost,127.0.0.1        -e no_proxy=localhost,127.0.0.1
```

Optional, to stop denied requests from the `claude` CLI to telemetry or update hosts:

```sh
-e CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1
```

Rules for the runner:

- Set both cases of each variable. Tools read different cases (for example, curl ignores upper-case `HTTP_PROXY`).
- Do not add `api.anthropic.com` to `NO_PROXY`. Direct connections fail, so this mistake fails closed, but the agent then loses API access.
- Do not use `--network host`, do not attach a second network (`docker network connect`), and do not use `--dns` or `--add-host`. Each of these can give the sandbox a route or a resolver outside the allowlist.
- Give the API credentials as `ANTHROPIC_API_KEY`. OAuth or browser login needs other hosts, and the proxy denies them.
- Start `up.sh` before the sandbox. If the proxy stops, the sandbox has no egress (fail closed).

## Logs

Squid logs every request in `/var/log/squid/access.log` in the proxy container. The log is also copied to `docker logs cotml-proxy`. A denied request has status `TCP_DENIED/403`. An allowed tunnel has status `TCP_TUNNEL/200`.

```sh
docker exec cotml-proxy grep TCP_DENIED /var/log/squid/access.log
```

The log is on tmpfs. `up.sh` and container restarts delete it.

## What test.sh proves

Each check starts a new `curlimages/curl:8.11.1` container on `cotml-egress`.

| Check | Expected result |
|---|---|
| 1 | `https://api.anthropic.com/v1/models` through the proxy gives an HTTP response (401 without a key). |
| 2a-2b | `https://github.com`, `https://example.com` through the proxy: CONNECT refused, 403. |
| 2c | CONNECT to the IP address of `api.anthropic.com`: 403. |
| 2d | CONNECT to `api.anthropic.com:80`: 403. |
| 3a-3d | Without proxy variables: name resolution fails (curl rc 6). Connections to IP literals fail (curl rc 7). |
| 3e | `nslookup example.com` fails. No DNS path out. |
| 4a-4b | Plain `http://` through the proxy, for any host including `api.anthropic.com`: 403. |
| 5 | The denials are in `access.log`. |

## Residual risks

1. **Data exfiltration through the Anthropic API.** The proxy sees only the CONNECT host, not the TLS content. The agent can send any data to `api.anthropic.com`, and it can use any API key, including an attacker's key. Prevention needs TLS interception or key pinning at a gateway. This setup does not do that.
2. **TLS name in the tunnel.** Squid connects the tunnel to the address that it resolves for `api.anthropic.com`. The agent controls the TLS handshake in the tunnel, so it can send a different SNI or `Host` to that address. The agent can reach only the services that Anthropic's front end serves on that address. If that front end is shared and permits domain fronting, other sites become reachable. Squid `ssl_bump peek` with an SNI check can close this gap. It is not configured.
3. **Host services.** `cotml-egress` has a gateway address on the host (`br-cotml-egress`). The host receives packets addressed to its own addresses; Docker's internal-network rules filter only forwarded traffic. Observed: the sandbox got TCP RST (connection refused) from host addresses `172.17.0.1` and `172.20.10.11`, so packets reach the host. A host service bound to `0.0.0.0` is reachable from the sandbox. Services bound to `127.0.0.1` are not. Mitigation (not applied, needs root, not tested here):
   ```sh
   iptables -I INPUT -i br-cotml-egress -j DROP
   ```
   This rule does not affect sandbox-to-proxy traffic, because that traffic stays on the bridge.
4. **Containers on the same network.** Containers on `cotml-egress` can connect to each other. Two concurrent sandboxes can communicate. If this is a problem, run sandboxes one at a time, or use one internal network and one proxy for each sandbox.
5. **DNS.** None observed. Docker's embedded DNS on an internal network does not forward external names (check 3e). Sandbox names resolve only for containers on `cotml-egress`. The proxy resolves `api.anthropic.com` through the host resolver. A poisoned host resolver can redirect the tunnel.
6. **IPv6.** The network has no IPv6 (`--ipv6` is not set). If IPv6 is enabled later, run `test.sh` again and add IPv6 checks.
7. **Proxy compromise.** The proxy is the only container with egress. It runs with a read-only root filesystem, `--cap-drop ALL` plus the capabilities that Squid needs to drop to user `proxy`, and `no-new-privileges`. A Squid vulnerability reachable through a CONNECT request is a risk.
