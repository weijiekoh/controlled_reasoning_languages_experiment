"""Analyze benchmark runs and draw the Pareto plots.

Usage: python3 harness/analyze.py --out analysis/ runs/<batch> [runs/<batch> ...]
Reads every result.json under the batch dirs (dry runs excluded). Writes:
  analysis/results.csv            one row per run
  analysis/summary.md             per (model, bench, condition, effort) table + paired tests
  analysis/pareto_tokens.png      pass rate (x) vs mean output tokens (y), one point per condition
  analysis/pareto_cost.png        pass rate (x) vs mean cost (y)
  analysis/budget_curves.png      share solved within an output-token budget, per condition
  analysis/turn_curves.png        share solved within a turn cap, per condition
"""
import argparse
import collections
import csv
import json
import math
import pathlib

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

# Categorical slots in fixed order (validated palette, light surface).
COLORS = {"bare": "#2a78d6", "cod": "#eb6834", "sponge": "#1baf7a", "caveman": "#eda100", "jellyfish": "#e87ba4"}
ORDER = ["bare", "cod", "sponge", "caveman", "jellyfish"]
INK, INK2, MUTED, GRID, SURFACE = "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#fcfcfb"
MODEL_SHORT = {"claude-sonnet-5-5": "Sonnet 5.5", "claude-haiku-5-5": "Haiku 5.5"}


def wilson(k: int, n: int, z: float = 1.96) -> tuple[float, float, float]:
    if n == 0:
        return float("nan"), float("nan"), float("nan")
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return p, c - h, c + h


def mcnemar(b: int, c: int) -> float:
    """Exact two-sided McNemar p-value for discordant counts b (A solved, B not) and c (B solved, A not)."""
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    p = sum(math.comb(n, i) for i in range(0, k + 1)) / 2 ** n
    return min(1.0, 2 * p)


def sign_test(diffs: list[float]) -> float:
    pos = sum(1 for d in diffs if d > 0)
    neg = sum(1 for d in diffs if d < 0)
    return mcnemar(pos, neg)


def load(batches: list[pathlib.Path]) -> list[dict]:
    rows = []
    for b in batches:
        for rj in sorted(b.glob("*/result.json")):
            r = json.loads(rj.read_text())
            if r.get("dry_run"):
                continue
            r["model_short"] = MODEL_SHORT.get(r.get("model"), r.get("model"))
            b = r.get("batch") or ""
            r["rep"] = 2 if "rep2" in b else 3 if "rep3" in b else 1   # repeat index; pairs are (problem, rep)
            mt = (r.get("limits") or {}).get("max_turns")
            if r["outcome"] == "gave_up" and mt and (r.get("num_turns") or 0) >= mt:
                r["outcome"] = "hit_cap"   # Claude Code reports subtype success at the turn cap
            rows.append(r)
    return rows


def style(ax, title: str, xlabel: str, ylabel: str):
    ax.set_facecolor(SURFACE)
    ax.set_title(title, color=INK, fontsize=12, loc="left", pad=12)
    ax.set_xlabel(xlabel, color=INK2)
    ax.set_ylabel(ylabel, color=INK2)
    ax.grid(True, color=GRID, linewidth=0.8)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    for s in ("left", "bottom"):
        ax.spines[s].set_color(GRID)
    ax.tick_params(colors=MUTED, labelsize=9)


def groups_of(rows):
    g = collections.defaultdict(list)
    for r in rows:
        g[(r["model_short"], r["bench"], r["condition"], r["effort"])].append(r)
    return g


def pareto(rows, ykey, ylabel, path, title):
    g = groups_of(rows)
    panels = sorted({(m, b, e) for (m, b, _, e) in g})
    fig, axes = plt.subplots(1, len(panels), figsize=(max(6.5, 5.2 * len(panels)), 4.6), squeeze=False)
    fig.patch.set_facecolor(SURFACE)
    for ax, (m, b, e) in zip(axes[0], panels):
        style(ax, f"{m}, {b}, effort {e}", "pass rate", ylabel)
        for ci, cond in enumerate(ORDER):
            xs = g.get((m, b, cond, e))
            if not xs:
                continue
            k = sum(r["outcome"] == "solved" for r in xs)
            p, lo, hi = wilson(k, len(xs))
            ys = [r[ykey] or 0 for r in xs]
            y = float(np.mean(ys))
            se = float(np.std(ys, ddof=1) / math.sqrt(len(ys))) if len(ys) > 1 else 0
            ax.errorbar(p, y, xerr=[[p - lo], [hi - p]], yerr=se, fmt="o", ms=9, color=COLORS[cond],
                        ecolor=COLORS[cond], elinewidth=1.5, capsize=3, label=f"{cond} (n={len(xs)})")
        ax.set_xlim(0, 1.02)
        ax.set_ylim(bottom=0)
        ax.legend(frameon=False, fontsize=9, labelcolor=INK2)
    fig.suptitle(title, color=INK, fontsize=12, x=0.01, ha="left")
    fig.tight_layout()
    fig.savefig(path, dpi=160)
    plt.close(fig)


def curves(rows, key, xlabel, path, title, log=False):
    """Share of problems solved within a budget on `key` (per run), per condition."""
    g = groups_of(rows)
    panels = sorted({(m, b, e) for (m, b, _, e) in g})
    fig, axes = plt.subplots(1, len(panels), figsize=(5.2 * len(panels), 4.4), squeeze=False)
    fig.patch.set_facecolor(SURFACE)
    for ax, (m, b, e) in zip(axes[0], panels):
        style(ax, f"{m}, {b}, effort {e}", xlabel, "share of problems solved within budget")
        allv = [r[key] for r in rows if r.get(key)]
        xmax = max(allv) if allv else 1
        grid = np.geomspace(max(1, min(allv)), xmax, 200) if log else np.linspace(0, xmax, 200)
        for cond in ORDER:
            xs = g.get((m, b, cond, e))
            if not xs:
                continue
            solved_v = [r[key] or 0 for r in xs if r["outcome"] == "solved"]
            ys = [sum(1 for v in solved_v if v <= t) / len(xs) for t in grid]
            ax.plot(grid, ys, color=COLORS[cond], linewidth=2, label=cond)
            ax.annotate(cond, (grid[-1], ys[-1]), textcoords="offset points", xytext=(4, 0),
                        color=INK2, fontsize=9, va="center")
        if log:
            ax.set_xscale("log")
        ax.set_ylim(0, 1.02)
        ax.legend(frameon=False, fontsize=9, labelcolor=INK2, loc="lower right")
    fig.suptitle(title, color=INK, fontsize=13, x=0.01, ha="left")
    fig.tight_layout()
    fig.savefig(path, dpi=160)
    plt.close(fig)


def summary(rows, out: pathlib.Path):
    g = groups_of(rows)
    lines = ["# Summary", "", "| model | bench | cond | effort | n | pass | 95% CI | mean out tok | median out tok | mean cost | mean turns | untouched | attempted-fail | hit_cap | timeout | error |",
             "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for (m, b, c, e), xs in sorted(g.items(), key=lambda kv: (kv[0][0], kv[0][1], ORDER.index(kv[0][2]) if kv[0][2] in ORDER else 9, kv[0][3])):
        k = sum(r["outcome"] == "solved" for r in xs)
        p, lo, hi = wilson(k, len(xs))
        oc = collections.Counter(r["outcome"] for r in xs)
        untouched = sum(1 for r in xs if r["outcome"] == "gave_up" and ("uses sorry" in (r.get("verify_detail") or "") or r.get("verify_stage") == "no_patch"))
        ot = [r["output_tokens"] or 0 for r in xs]
        lines.append(f"| {m} | {b} | {c} | {e} | {len(xs)} | {p:.0%} | [{lo:.0%}, {hi:.0%}] | {np.mean(ot):.0f} | {np.median(ot):.0f} | "
                     f"${np.mean([r['total_cost_usd'] or 0 for r in xs]):.3f} | {np.mean([r['num_turns'] or 0 for r in xs]):.1f} | "
                     f"{untouched} | {oc['gave_up'] - untouched} | {oc['hit_cap']} | {oc['timeout']} | {oc['error']} |")
    lines += ["", "# Paired comparisons vs bare (same model, bench, effort, problem)", "",
              "| model | bench | effort | cond | common n | bare pass | cond pass | discordant (bare only / cond only) | McNemar p | both-solved n | median token ratio cond/bare | sign-test p | median cost ratio |",
              "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    by = collections.defaultdict(dict)
    for r in rows:
        by[(r["model_short"], r["bench"], r["effort"], r["condition"])][(r["problem"], r["rep"])] = r
    for (m, b, e, c), d in sorted(by.items()):
        if c == "bare":
            continue
        base = by.get((m, b, e, "bare"), {})
        common = sorted(set(base) & set(d))
        if not common:
            continue
        bs = {p: base[p]["outcome"] == "solved" for p in common}
        cs = {p: d[p]["outcome"] == "solved" for p in common}
        b_only = sum(bs[p] and not cs[p] for p in common)
        c_only = sum(cs[p] and not bs[p] for p in common)
        both = [p for p in common if bs[p] and cs[p]]
        ratios = [(d[p]["output_tokens"] or 1) / (base[p]["output_tokens"] or 1) for p in both]
        cratios = [(d[p]["total_cost_usd"] or 1e-9) / (base[p]["total_cost_usd"] or 1e-9) for p in both]
        lines.append(f"| {m} | {b} | {e} | {c} | {len(common)} | {sum(bs.values())/len(common):.0%} | {sum(cs.values())/len(common):.0%} | "
                     f"{b_only} / {c_only} | {mcnemar(b_only, c_only):.3f} | {len(both)} | "
                     f"{np.median(ratios) if ratios else float('nan'):.2f} | {sign_test([math.log(x) for x in ratios]) if ratios else float('nan'):.3f} | "
                     f"{np.median(cratios) if cratios else float('nan'):.2f} |")
    (out / "summary.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--bench", default=None, help="comma list of benches to keep")
    ap.add_argument("--min-n", type=int, default=1, help="drop (model, bench, cond, effort) groups with fewer runs")
    ap.add_argument("batches", nargs="+")
    a = ap.parse_args()
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    rows = load([pathlib.Path(b) for b in a.batches])
    if a.bench:
        keep = set(a.bench.split(","))
        rows = [r for r in rows if r["bench"] in keep]
    if a.min_n > 1:
        import collections as _c
        cnt = _c.Counter((r["model_short"], r["bench"], r["condition"], r["effort"]) for r in rows)
        rows = [r for r in rows if cnt[(r["model_short"], r["bench"], r["condition"], r["effort"])] >= a.min_n]
    keys = ["model_short", "bench", "condition", "effort", "problem", "outcome", "verify_stage", "num_turns",
            "output_tokens", "thinking_tokens", "cache_read_tokens", "cache_creation_tokens", "total_cost_usd",
            "duration_s", "lean_compile_count", "search_tactic_uses", "proof_lines", "agent_said_give_up", "batch"]
    with open(out / "results.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)
    summary(rows, out)
    pareto(rows, "output_tokens", "mean output tokens per run", out / "pareto_tokens.png",
           "Pass rate vs output tokens (error bars: Wilson 95% CI, SE)")
    pareto(rows, "total_cost_usd", "mean cost per run (USD)", out / "pareto_cost.png",
           "Pass rate vs cost per run")
    curves(rows, "output_tokens", "output-token budget per run", out / "budget_curves.png",
           "Share of problems solved within an output-token budget", log=True)
    curves(rows, "num_turns", "turn cap", out / "turn_curves.png",
           "Share of problems solved within a turn cap")
    print(f"\nwrote {out}/ ({len(rows)} runs)")


if __name__ == "__main__":
    main()
