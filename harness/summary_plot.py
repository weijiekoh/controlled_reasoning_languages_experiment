"""One figure for the slides: per domain, pass rate (left) and output-token ratio vs bare on commonly solved tasks (right).

Usage: python3 harness/summary_plot.py analysis/summary_all.png analysis/putnam analysis/verus analysis/swe
Reads <dir>/results.csv written by analyze.py. Haiku 5.5 rows only.
"""
import csv
import math
import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

COLORS = {"bare": "#2a78d6", "cod": "#eb6834", "sponge": "#1baf7a", "caveman": "#eda100", "jellyfish": "#e87ba4"}
ORDER = ["bare", "cod", "sponge", "caveman", "jellyfish"]
LABEL = {"putnam": "Lean: hard Putnam (60)", "verus": "Verus: AlgoVeri (20)", "swe": "SWE-bench Verified (96)"}
INK, INK2, MUTED, GRID, SURFACE = "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#fcfcfb"


def wilson(k, n, z=1.96):
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return p, c - h, c + h


def load(d):
    rows = [r for r in csv.DictReader(open(pathlib.Path(d) / "results.csv")) if r["model_short"] == "Haiku 5.5"]
    bench = rows[0]["bench"]
    by = {}
    for r in rows:
        by.setdefault(r["condition"], {}).setdefault((r["problem"], r["batch"]), r)
    return bench, by


def main():
    out, dirs = sys.argv[1], sys.argv[2:]
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.2))
    fig.patch.set_facecolor(SURFACE)
    for ax, title, xlabel in [(axes[0], "Pass rate (Wilson 95% CI)", "pass rate"),
                              (axes[1], "Output tokens vs bare, same problem, both solved", "token ratio")]:
        ax.set_facecolor(SURFACE); ax.set_title(title, color=INK, fontsize=11, loc="left", pad=10)
        ax.set_xlabel(xlabel, color=INK2); ax.grid(True, axis="x", color=GRID, linewidth=0.8)
        for s in ("top", "right"): ax.spines[s].set_visible(False)
        for s in ("left", "bottom"): ax.spines[s].set_color(GRID)
        ax.tick_params(colors=MUTED, labelsize=9)
    yt, yl = [], []
    y = 0
    for d in dirs:
        bench, by = load(d)
        conds = [c for c in ORDER if c in by]
        base = {k: v for k, v in by.get("bare", {}).items()}
        for c in conds:
            runs = list(by[c].values())
            k = sum(r["outcome"] == "solved" for r in runs)
            p, lo, hi = wilson(k, len(runs))
            axes[0].errorbar(p, y, xerr=[[p - lo], [hi - p]], fmt="o", ms=8, color=COLORS[c], ecolor=COLORS[c], capsize=3)
            axes[0].annotate(f"{p:.0%}", (hi, y), textcoords="offset points", xytext=(6, -3), color=INK2, fontsize=8)
            if c != "bare":
                pairs = []
                for key, r in by[c].items():
                    b = base.get(key)
                    if b and r["outcome"] == "solved" and b["outcome"] == "solved":
                        pairs.append(float(r["output_tokens"] or 1) / float(b["output_tokens"] or 1))
                if pairs:
                    pairs.sort(); med = pairs[len(pairs) // 2]
                    axes[1].plot(med, y, "o", ms=8, color=COLORS[c])
                    axes[1].annotate(f"{med:.2f} (n={len(pairs)})", (med, y), textcoords="offset points", xytext=(8, -3), color=INK2, fontsize=8)
            yt.append(y); yl.append(f"{LABEL.get(bench, bench)}  ·  {c}")
            y += 1
        y += 0.7
    for ax in axes:
        ax.set_yticks(yt); ax.invert_yaxis()
    axes[0].set_yticklabels(yl, fontsize=8, color=INK2); axes[1].set_yticklabels([""] * len(yt))
    axes[0].set_xlim(0, 1.0); axes[1].set_xlim(0.5, 1.6); axes[1].axvline(1, color=MUTED, linewidth=1, linestyle="--")
    fig.suptitle("Controlled reasoning languages vs bare agent, Claude Haiku 5.5, low effort", color=INK, fontsize=12, x=0.01, ha="left")
    fig.tight_layout()
    fig.savefig(out, dpi=170)
    print("wrote", out)


if __name__ == "__main__":
    main()
