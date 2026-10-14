"""Sample a stratified subset of benchmark problems.

Usage:
  python3 harness/sample.py --bench minif2f|putnam --n N --seed S --out FILE

Writes the sampled problem names, sorted, one per line, to FILE.
Prints the strata table (population and sample counts) to stdout.

Strata:
  minif2f  source prefix: the name part before the first `_`; `mathd_algebra`
           and `mathd_numbertheory` are two separate strata.
  putnam   decade x answer flag. A problem is an answer problem if its file
           defines `<name>_solution`.

Eligibility:
  minif2f  OK row in data/minif2f_check.tsv and exactly one `sorry`.
  putnam   file in data/putnam_subst/ with exactly one `sorry`.

Design (nested by construction):
  1. rng = random.Random(seed). Shuffle each stratum (strata in sorted order).
  2. Allocate slots one by one with the Webster/Sainte-Lague divisor method:
     the next slot goes to the non-full stratum with the largest
     size / (taken + 0.5). A seeded random key breaks ties.
  3. Each slot takes the next problem of that stratum's shuffled list.
  The sample of size n is the first n problems of this sequence. A divisor
  method is house-monotone, so for one seed the sample for n is a subset of
  the sample for any m > n. Within a stratum, each subset of a given size is
  equally likely.
"""
import argparse
import collections
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MINIF2F_DIR = ROOT / "data/miniF2F-lean4/MiniF2F/Test"
MINIF2F_CHECK = ROOT / "data/minif2f_check.tsv"
PUTNAM_DIR = ROOT / "data/putnam_subst"
SORRY = re.compile(r"\bsorry\b")


def n_sorry(path):
    return len(SORRY.findall(path.read_text()))


def minif2f_pool():
    ok = set()
    for line in MINIF2F_CHECK.read_text().splitlines():
        cols = line.split("\t")
        if len(cols) >= 2 and cols[1] == "OK":
            ok.add(cols[0])
    pool, skipped = {}, []
    for f in sorted(MINIF2F_DIR.glob("*.lean")):
        name = f.stem
        if name not in ok or n_sorry(f) != 1:
            skipped.append(name)
            continue
        parts = name.split("_")
        pool[name] = "_".join(parts[:2]) if parts[0] == "mathd" else parts[0]
    return pool, skipped


def putnam_pool():
    pool, skipped = {}, []
    for f in sorted(PUTNAM_DIR.glob("putnam_*.lean")):
        name = f.stem
        text = f.read_text()
        m = re.match(r"putnam_(\d{4})_[ab]\d+$", name)
        if not m or len(SORRY.findall(text)) != 1:
            skipped.append(name)
            continue
        decade = f"{int(m.group(1)) // 10 * 10}s"
        kind = "answer" if re.search(rf"\b{name}_solution\b", text) else "proof"
        pool[name] = f"{decade}/{kind}"
    return pool, skipped


def order(pool, seed):
    """Return all problems in sampling order (prefix of length n = sample)."""
    rng = random.Random(seed)
    strata = collections.defaultdict(list)
    for name, s in pool.items():
        strata[s].append(name)
    keys = sorted(strata)
    for s in keys:
        strata[s].sort()
        rng.shuffle(strata[s])
    tie = {s: rng.random() for s in keys}
    taken = dict.fromkeys(keys, 0)
    seq = []
    for _ in range(len(pool)):
        s = max((k for k in keys if taken[k] < len(strata[k])),
                key=lambda k: (len(strata[k]) / (taken[k] + 0.5), tie[k]))
        seq.append(strata[s][taken[s]])
        taken[s] += 1
    return seq


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--bench", required=True, choices=["minif2f", "putnam"])
    ap.add_argument("--n", required=True, type=int)
    ap.add_argument("--seed", required=True, type=int)
    ap.add_argument("--out", required=True, type=Path)
    a = ap.parse_args()

    pool, skipped = minif2f_pool() if a.bench == "minif2f" else putnam_pool()
    if not 0 < a.n <= len(pool):
        sys.exit(f"--n must be in 1..{len(pool)}")
    sample = sorted(order(pool, a.seed)[: a.n])
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text("".join(f"{x}\n" for x in sample))

    pop = collections.Counter(pool.values())
    got = collections.Counter(pool[x] for x in sample)
    w = max(len(s) for s in pop)
    print(f"{a.bench} n={a.n} seed={a.seed} -> {a.out}")
    print(f"eligible {len(pool)}, skipped {len(skipped)}: {skipped}")
    print(f"{'stratum':<{w}}  {'pool':>4}  {'sample':>6}")
    for s in sorted(pop):
        print(f"{s:<{w}}  {pop[s]:>4}  {got[s]:>6}")
    print(f"{'total':<{w}}  {len(pool):>4}  {len(sample):>6}")


if __name__ == "__main__":
    main()
