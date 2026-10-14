#!/usr/bin/env python3
"""Summarize run results per (bench, condition, effort).

Usage: python3 harness/summarize.py [PATH ...] [--include-dry-run]
PATH is a results.jsonl file or a batch directory. Default: runs/*/results.jsonl.
Duplicate (bench, problem, condition, effort, batch) records keep the last line.

Pass rate excludes runs with outcome "error" (infrastructure or API failure);
column "err" shows their count. CI is the Wilson 95% interval.
srch_solved: share of solved runs with search_tactic_uses > 0.
srch_final: share of solved runs whose final file still contains a search tactic.
"""
import argparse
import json
import math
import pathlib
import statistics
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUTCOMES = ["solved", "gave_up", "hit_cap", "timeout", "error"]


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    if n == 0:
        return float("nan"), float("nan")
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return max(0.0, c - h), min(1.0, c + h)


def mean(xs):
    xs = [x for x in xs if x is not None]
    return statistics.fmean(xs) if xs else None


def median(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None


def fmt(x, spec):
    return "-" if x is None or (isinstance(x, float) and math.isnan(x)) else format(x, spec)


def load(paths: list[pathlib.Path], dry: bool) -> list[dict]:
    recs = {}
    for p in paths:
        f = p / "results.jsonl" if p.is_dir() else p
        if not f.exists():
            print(f"skip: {f} not found", file=sys.stderr)
            continue
        for line in f.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get("dry_run") and not dry:
                continue
            recs[(r.get("bench"), r.get("problem"), r.get("condition"), r.get("effort"), r.get("batch"))] = r
    return list(recs.values())


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", type=pathlib.Path)
    ap.add_argument("--include-dry-run", action="store_true")
    a = ap.parse_args()
    paths = a.paths or sorted((ROOT / "runs").glob("*/results.jsonl"))
    recs = load(paths, a.include_dry_run)
    if not recs:
        print("no records")
        return 1

    groups: dict[tuple, list[dict]] = {}
    for r in recs:
        groups.setdefault((r["bench"], r["condition"], r["effort"]), []).append(r)

    cols = ["bench", "cond", "effort", "n", "err", "pass", "95% CI", "mean_out", "med_out",
            "mean_cost", "mean_turns", "srch_solved", "srch_final"] + OUTCOMES
    rows = []
    for key in sorted(groups):
        g = groups[key]
        cnt = {o: sum(1 for r in g if r["outcome"] == o) for o in OUTCOMES}
        valid = len(g) - cnt["error"]
        k = cnt["solved"]
        lo, hi = wilson(k, valid)
        solved = [r for r in g if r["outcome"] == "solved"]
        srch = sum(1 for r in solved if (r.get("search_tactic_uses") or 0) > 0) / len(solved) if solved else None
        srch_f = sum(1 for r in solved if r.get("search_tactic_in_final")) / len(solved) if solved else None
        rows.append([*key, str(len(g)), str(cnt["error"]),
                     fmt(k / valid if valid else None, ".1%"),
                     f"[{fmt(lo, '.1%')}, {fmt(hi, '.1%')}]",
                     fmt(mean(r.get("output_tokens") for r in g), ".0f"),
                     fmt(median(r.get("output_tokens") for r in g), ".0f"),
                     fmt(mean(r.get("total_cost_usd") for r in g), ".3f"),
                     fmt(mean(r.get("num_turns") for r in g), ".1f"),
                     fmt(srch, ".0%"), fmt(srch_f, ".0%"),
                     *(str(cnt[o]) for o in OUTCOMES)])
    w = [max(len(c), *(len(r[i]) for r in rows)) for i, c in enumerate(cols)]
    print("  ".join(c.ljust(w[i]) for i, c in enumerate(cols)))
    print("  ".join("-" * x for x in w))
    for r in rows:
        print("  ".join(v.ljust(w[i]) for i, v in enumerate(r)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
