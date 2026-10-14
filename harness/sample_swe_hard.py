"""Sample a harder SWE-bench Verified set: non-django instances not already in data/swe.

Usage: python3 harness/sample_swe_hard.py [--n 48] [--pull-mode ipv4|docker] [--no-pull]
Selection: random.Random(20261015), proportional by repo (largest remainder, at least 1 per
repo), excluding django/django and instances that already have data/swe/<id>/task.json.
Writes problems/swe_hard.txt (framing "issue") and data/swe/<id>/task.json; pulls images.
"""
import argparse
import json
import pathlib
import random
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import sample_swe as S  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
FIELDS = ["instance_id", "repo", "base_commit", "problem_statement", "FAIL_TO_PASS", "PASS_TO_PASS",
          "version", "environment_setup_commit", "test_patch"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=48)
    ap.add_argument("--no-pull", action="store_true")
    ap.add_argument("--pull-mode", choices=["docker", "ipv4"], default="ipv4")
    ap.add_argument("--pull-parallel", type=int, default=4)
    a = ap.parse_args()
    rows = [json.loads(l) for l in open(ROOT / "data/swebench_verified.jsonl")]
    have = {p.name for p in (ROOT / "data/swe").iterdir() if (p / "task.json").exists()}
    pool = [r for r in rows if r["repo"] != "django/django" and r["instance_id"] not in have]
    rng = random.Random(20261015)
    by_repo = {}
    for r in pool:
        by_repo.setdefault(r["repo"], []).append(r)
    counts = {k: len(v) for k, v in by_repo.items()}
    quota = S.quotas(counts, a.n)
    chosen = []
    for repo in sorted(by_repo):
        rs = by_repo[repo]
        rng.shuffle(rs)
        k = quota.get(repo, 0)
        chosen += [r for r in rs if S.has_manifest(S.image_name(r["instance_id"]))][:k]
    chosen.sort(key=lambda r: r["instance_id"])
    (ROOT / "problems/swe_hard.txt").write_text("".join(r["instance_id"] + "\n" for r in chosen))
    for r in chosen:
        d = ROOT / "data/swe" / r["instance_id"]
        d.mkdir(parents=True, exist_ok=True)
        task = {k: r[k] for k in FIELDS}
        task["framing"] = "issue"
        task["image"] = S.image_name(r["instance_id"])
        (d / "task.json").write_text(json.dumps(task, indent=1) + "\n")
    print(f"selected {len(chosen)}: " + ", ".join(f"{k}:{v}" for k, v in sorted(quota.items()) if v))
    if a.no_pull:
        return 0
    import concurrent.futures as cf
    import subprocess
    present = set(subprocess.run(["docker", "images", "--format", "{{.Repository}}:{{.Tag}}"],
                                 capture_output=True, text=True).stdout.split())
    todo = [S.image_name(r["instance_id"]) for r in chosen if S.image_name(r["instance_id"]) not in present]
    print(f"pulling {len(todo)} images, mode {a.pull_mode}", flush=True)
    def pull(img):
        try:
            if a.pull_mode == "ipv4":
                S.pull_ipv4(img)
            else:
                subprocess.run(["docker", "pull", "-q", img], check=True, capture_output=True, text=True)
            return img, "ok"
        except Exception as e:  # noqa: BLE001
            return img, f"FAIL {str(e)[:120]}"
    with cf.ThreadPoolExecutor(a.pull_parallel) as ex:
        for i, (img, st) in enumerate(ex.map(pull, todo), 1):
            print(f"[{i}/{len(todo)}] {img}: {st}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
