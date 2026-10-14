"""Substitute CombiBench reference answers into `<name>_solution ... := sorry` placeholders.

Usage: python -I combi_substitute.py <combibench_lean_dir> <out_dir>
  <combibench_lean_dir> = data/CombiBench/lean/CombiBench (has metadata.csv, with_solution/).
Writes out_dir/combi_<name>.lean. Each output file has exactly one `sorry` (the proof).
Answer source: `answer` column of metadata.csv. Cross-check: the answer must also appear
as `((<answer>) : <type> )` in with_solution/<name>_sol.lean; a mismatch excludes the problem.
Prints exclusions and the reason for each.
"""
import csv
import pathlib
import re
import sys

SOL = re.compile(r"^(\s*(?:noncomputable\s+)?abbrev\s+(\S+_solution)\b.*:=)\s*sorry\s*$")
SORRY = re.compile(r"\bsorry\b")
# Upstream contamination: an unrelated theorem appended to a problem file (absent from with_solution/).
STRAY = {"imo_2010_p5": "mba_challenge_6f99807f"}


def ws(s: str) -> str:
    return re.sub(r"\s+", "", s)


def split_list(ans: str) -> list[str]:
    """Split `[a, b, c]` at top-level commas."""
    body, parts, depth, cur = ans.strip()[1:-1], [], 0, ""
    for ch in body:
        depth += ch in "([{"
        depth -= ch in ")]}"
        if ch == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    return parts + [cur.strip()]


def drop_stray(lines: list[str], thm: str) -> list[str] | None:
    """Remove `/-- ... -/ theorem <thm> ...` when it runs to end of file."""
    k = next((i for i, l in enumerate(lines) if l.startswith(f"theorem {thm} ")), None)
    if k is None:
        return None
    j = k
    while j > 0 and not lines[j].startswith("/--"):
        j -= 1
    rest = lines[k + 1:]
    if any(re.match(r"(theorem|lemma|def|abbrev|structure|inductive|instance)\b", l) for l in rest):
        return None
    return lines[:j]


def main() -> None:
    src, out = map(pathlib.Path, sys.argv[1:3])
    out.mkdir(parents=True, exist_ok=True)
    meta = {r["theorem_name"]: r for r in csv.DictReader(open(src / "metadata.csv", encoding="utf-8"))}
    wrote, excluded, filled = 0, [], []
    for f in sorted(src.glob("*.lean")):
        name = f.stem
        lines = f.read_text(encoding="utf-8").splitlines()
        if name in STRAY:
            lines = drop_stray(lines, STRAY[name])
            if lines is None:
                excluded.append((name, "stray theorem not removable"))
                continue
        holes = [i for i, l in enumerate(lines) if SOL.match(l)]
        if holes:
            ans = (meta.get(name) or {}).get("answer", "").strip()
            if not ans:
                excluded.append((name, "no reference answer in metadata.csv"))
                continue
            answers = split_list(ans) if len(holes) > 1 else [ans]
            if len(answers) != len(holes):
                excluded.append((name, f"{len(holes)} placeholders, {len(answers)} answers"))
                continue
            solf = src / "with_solution" / f"{name}_sol.lean"
            sol = ws(solf.read_text(encoding="utf-8")) if solf.exists() else ""
            bad = [a for a in answers if ws(f"(({a}) :") not in sol]
            if bad:
                excluded.append((name, f"answer not found in {solf.name}: {bad}"))
                continue
            for i, a in zip(holes, answers):
                head = SOL.match(lines[i]).group(1)
                if "noncomputable" not in head:   # some answers use Real.sqrt, Real.logb, ...
                    head = re.sub(r"^(\s*)", r"\1noncomputable ", head, count=1)
                lines[i] = f"{head} {a}"
            filled.append(name)
        text = "\n".join(lines).rstrip() + "\n"
        n = len(SORRY.findall(text))
        if n != 1:
            excluded.append((name, f"{n} sorry after substitution"))
            continue
        (out / f"combi_{name}.lean").write_text(text, encoding="utf-8")
        wrote += 1
    print(f"wrote {wrote} ({len(filled)} with substituted answers), excluded {len(excluded)}")
    for n, why in excluded:
        print(f"  excluded {n}: {why}")


if __name__ == "__main__":
    main()
