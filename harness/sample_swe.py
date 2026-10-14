#!/usr/bin/env python3
"""Sample SWE-bench Verified instances, pull their eval images, and write task dirs.

Usage: python3 harness/sample_swe.py [--n 48] [--no-pull] [--pull-parallel 4]

Reads data/swebench_verified.jsonl (SWE-bench/SWE-bench_Verified, test split).
Selection: random.Random(20261014). Each repo gets a proportional share of --n
(largest remainder, at least 1 per repo). Each repo's instances are shuffled in
repo-name order; the first instances whose eval image has a registry manifest
are taken. A second shuffle of the selection (same RNG) splits it in two halves:
problems/swe_issue.txt (framing "issue") and problems/swe_debug.txt (framing "debug").
Writes data/swe/<instance_id>/task.json. Pulls the images (--pull-parallel at a
time) and prints their total size.

Docker Hub allows 100 manifest GETs per hour per IP (unauthenticated); a HEAD does
not count. The manifest check uses HEAD. --pull-mode ipv4 fetches the image over
IPv4 with the registry API and loads it with `docker load` (use it when the
daemon's address, often IPv6, has no quota left).

Image name: swebench/sweb.eval.x86_64.<instance_id>:latest, lower case, "__" -> "_1776_"
(swebench.task.checks.expected_image; equal to the dataset's "image" field).
"""
import argparse
import concurrent.futures as cf
import io
import json
import pathlib
import random
import socket
import subprocess
import sys
import tarfile
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = ROOT / "data/swebench_verified.jsonl"
TASKS = ROOT / "data/swe"
SEED = 20261014
FIELDS = ("instance_id", "repo", "base_commit", "problem_statement", "FAIL_TO_PASS", "PASS_TO_PASS",
          "version", "environment_setup_commit", "test_patch")   # test_patch: applied before a "debug" run


def image_name(instance_id: str) -> str:
    return f"swebench/sweb.eval.x86_64.{instance_id}:latest".lower().replace("__", "_1776_")


REGISTRY = "https://registry-1.docker.io"
ACCEPT = ", ".join(["application/vnd.docker.distribution.manifest.list.v2+json",
                    "application/vnd.oci.image.index.v1+json",
                    "application/vnd.docker.distribution.manifest.v2+json",
                    "application/vnd.oci.image.manifest.v1+json"])


def force_ipv4() -> None:
    orig = socket.getaddrinfo
    socket.getaddrinfo = lambda host, *a, **k: [x for x in orig(host, *a, **k) if x[0] == socket.AF_INET]


def split_image(image: str) -> tuple[str, str]:
    repo, tag = image.rsplit(":", 1)
    return repo, tag


def token(repo: str) -> str:
    url = f"https://auth.docker.io/token?service=registry.docker.io&scope=repository:{repo}:pull"
    with urllib.request.urlopen(url, timeout=60) as r:
        return json.load(r)["token"]


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *a, **k):
        return None


def registry_get(repo: str, path: str, tok: str, accept: str = ACCEPT, method: str = "GET"):
    """Open a registry URL; follow a blob redirect without the Authorization header."""
    req = urllib.request.Request(f"{REGISTRY}/v2/{repo}/{path}", method=method,
                                 headers={"Authorization": f"Bearer {tok}", "Accept": accept})
    try:
        return urllib.request.build_opener(NoRedirect).open(req, timeout=300)
    except urllib.error.HTTPError as e:
        if e.code in (301, 302, 303, 307, 308):
            return urllib.request.urlopen(e.headers["Location"], timeout=300)
        raise


def has_manifest(image: str) -> bool:
    repo, tag = split_image(image)
    try:
        registry_get(repo, f"manifests/{tag}", token(repo), method="HEAD").close()
        return True
    except urllib.error.HTTPError:
        return False


def pull_ipv4(image: str) -> None:
    """Fetch linux/amd64 manifest, config and layers; stream them to `docker load` as a docker-save tar."""
    repo, tag = split_image(image)
    tok = token(repo)
    with registry_get(repo, f"manifests/{tag}", tok) as r:
        man = json.load(r)
    if "manifests" in man:   # index: pick linux/amd64
        d = next(m["digest"] for m in man["manifests"]
                 if m.get("platform", {}).get("os") == "linux" and m["platform"].get("architecture") == "amd64")
        with registry_get(repo, f"manifests/{d}", tok) as r:
            man = json.load(r)
    cfg = man["config"]["digest"]
    layers = [x["digest"] for x in man["layers"]]
    p = subprocess.Popen(["docker", "load", "-q"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)
    try:
        with tarfile.open(fileobj=p.stdin, mode="w|") as tf:
            def add(name, digest, size=None):
                tok_now = token(repo)   # tokens expire after 5 minutes; large layers take longer
                with registry_get(repo, f"blobs/{digest}", tok_now, accept="*/*") as r:
                    ti = tarfile.TarInfo(name)
                    ti.size = int(r.headers["Content-Length"]) if size is None else size
                    tf.addfile(ti, r)
            add(cfg.split(":")[1] + ".json", cfg, man["config"]["size"])
            sizes = {x["digest"]: x["size"] for x in man["layers"]}
            for d in layers:
                add(d.split(":")[1] + ".tar.gz", d, sizes[d])
            meta = json.dumps([{"Config": cfg.split(":")[1] + ".json", "RepoTags": [image],
                                "Layers": [d.split(":")[1] + ".tar.gz" for d in layers]}]).encode()
            ti = tarfile.TarInfo("manifest.json")
            ti.size = len(meta)
            tf.addfile(ti, io.BytesIO(meta))
        p.stdin.close()
    finally:
        out = p.stdout.read().decode(errors="replace")
        rc = p.wait()
    if rc != 0:
        raise RuntimeError(f"docker load failed: {out[-300:]}")


def quotas(counts: dict[str, int], n: int) -> dict[str, int]:
    total = sum(counts.values())
    exact = {r: n * c / total for r, c in counts.items()}
    q = {r: max(1, int(e)) for r, e in exact.items()}
    rest = sorted(counts, key=lambda r: (-(exact[r] - int(exact[r])), r))
    i = 0
    while sum(q.values()) < n:
        if exact[rest[i % len(rest)]] >= 1:   # repos below 1 already got their minimum
            q[rest[i % len(rest)]] += 1
        i += 1
    while sum(q.values()) > n:   # minimums overshoot: take from the largest share
        r = max(q, key=lambda k: (q[k], k))
        q[r] -= 1
    return q


def as_list(v):
    return json.loads(v) if isinstance(v, str) else list(v)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=48)
    ap.add_argument("--no-pull", action="store_true")
    ap.add_argument("--pull-parallel", type=int, default=4)
    ap.add_argument("--pull-mode", choices=("docker", "ipv4"), default="docker")
    args = ap.parse_args()
    if args.pull_mode == "ipv4":
        force_ipv4()

    rows = [json.loads(line) for line in DATA.read_text().splitlines() if line.strip()]
    by_repo: dict[str, list[dict]] = {}
    for r in rows:
        by_repo.setdefault(r["repo"], []).append(r)
    q = quotas({k: len(v) for k, v in by_repo.items()}, args.n)
    rng = random.Random(SEED)
    chosen, skipped = [], []
    for repo in sorted(by_repo):
        cand = sorted(by_repo[repo], key=lambda r: r["instance_id"])
        rng.shuffle(cand)
        got = 0
        for r in cand:
            if got == q[repo]:
                break
            img = image_name(r["instance_id"])
            if r.get("image") and r["image"] != img:
                print(f"warning: {r['instance_id']}: dataset image {r['image']} != {img}", file=sys.stderr)
            if not has_manifest(img):
                skipped.append(img)
                continue
            chosen.append(r)
            got += 1
        print(f"{repo}: quota {q[repo]} of {len(cand)}, chose {got}", flush=True)
    if skipped:
        print("no manifest (excluded):", *skipped, sep="\n  ")

    chosen.sort(key=lambda r: r["instance_id"])
    rng.shuffle(chosen)
    half = len(chosen) // 2
    split = {"issue": chosen[:half], "debug": chosen[half:]}
    for framing, part in split.items():
        ids = sorted(r["instance_id"] for r in part)
        (ROOT / f"problems/swe_{framing}.txt").write_text("\n".join(ids) + "\n")
        for r in part:
            t = {k: r[k] for k in FIELDS}
            t["FAIL_TO_PASS"], t["PASS_TO_PASS"] = as_list(r["FAIL_TO_PASS"]), as_list(r["PASS_TO_PASS"])
            t["framing"], t["image"] = framing, image_name(r["instance_id"])
            d = TASKS / r["instance_id"]
            d.mkdir(parents=True, exist_ok=True)
            (d / "task.json").write_text(json.dumps(t, indent=1) + "\n")
    print(f"wrote {len(chosen)} tasks: issue {half}, debug {len(chosen) - half}")

    if args.no_pull:
        return 0
    images = [image_name(r["instance_id"]) for r in chosen]

    def pull(img):
        if subprocess.run(["docker", "image", "inspect", img], capture_output=True).returncode == 0:
            return img, 0, ""
        if args.pull_mode == "ipv4":
            try:
                pull_ipv4(img)
                return img, 0, ""
            except Exception as e:
                return img, 1, repr(e)[-300:]
        p = subprocess.run(["docker", "pull", "-q", img], capture_output=True, text=True)
        return img, p.returncode, p.stderr.strip()[-300:]

    failed = []
    with cf.ThreadPoolExecutor(max_workers=args.pull_parallel) as ex:
        for i, (img, rc, err) in enumerate(ex.map(pull, images), 1):
            print(f"[{i}/{len(images)}] pull {img}: {'ok' if rc == 0 else 'FAILED ' + err}", flush=True)
            if rc:
                failed.append(img)
    size = 0
    for img in images:
        p = subprocess.run(["docker", "image", "inspect", "-f", "{{.Size}}", img], capture_output=True, text=True)
        if p.returncode == 0:
            size += int(p.stdout.strip())
    print(f"pulled {len(images) - len(failed)}/{len(images)}; sum of image sizes {size / 1e9:.1f} GB "
          f"(shared layers counted once per image)")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
