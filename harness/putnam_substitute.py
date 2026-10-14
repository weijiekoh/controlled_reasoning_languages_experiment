"""Replace each `..._solution ... := sorry` in PutnamBench with the answer from the next comment line.

Usage: python -I putnam_substitute.py <src_dir> <out_dir>
Writes one file per problem to out_dir. Prints problems it cannot substitute.
"""
import pathlib
import re
import sys

SOL = re.compile(r"^(\s*(?:noncomputable\s+)?(?:abbrev|def)\s+\S+_solution\b.*:=)\s*sorry\s*$")

src, out = map(pathlib.Path, sys.argv[1:3])
out.mkdir(parents=True, exist_ok=True)
skipped = []
for f in sorted(src.glob("*.lean")):
    lines = f.read_text().splitlines()
    new, ok, i = [], True, 0
    while i < len(lines):
        m = SOL.match(lines[i])
        if m:
            nxt = lines[i + 1] if i + 1 < len(lines) else ""
            if not nxt.startswith("--") or nxt.startswith("--/") :
                ok = False
                break
            head = m.group(1)
            if "noncomputable" not in head:  # some answers use Real.exp, Real.log, ...
                head = re.sub(r"^(\s*)", r"\1noncomputable ", head, count=1)
            new.append(f"{head} {nxt[2:].strip()}")
            i += 2
            continue
        new.append(lines[i])
        i += 1
    if ok:
        (out / f.name).write_text("\n".join(new) + "\n")
    else:
        skipped.append(f.stem)
print(f"wrote {len(list(out.glob('*.lean')))}, skipped {len(skipped)}: {skipped[:10]}")
