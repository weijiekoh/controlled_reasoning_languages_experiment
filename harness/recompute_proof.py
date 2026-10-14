"""Recompute proof_chars/proof_lines/statement_prefix_changed in existing result.json and results.jsonl.
Usage: python3 harness/recompute_proof.py runs/<batch>
"""
import json, pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import run as R

batch = pathlib.Path(sys.argv[1])
rows = []
for d in sorted(batch.iterdir()):
    rj = d / "result.json"
    if not rj.exists():
        continue
    r = json.loads(rj.read_text())
    sub = d / "work" / f"{r['problem']}.lean"
    orig = (R.BENCH_DIRS[r["bench"]] / f"{r['problem']}.lean").read_text()
    if not sub.exists():
        rows.append(r); continue
    body, changed = R.proof_text(orig, sub.read_text(), r["problem"])
    r["proof_chars"] = len(body) if body is not None else None
    r["proof_lines"] = sum(1 for x in body.splitlines() if x.strip()) if body is not None else None
    r["statement_prefix_changed"] = changed
    rj.write_text(json.dumps(r, indent=1))
    rows.append(r)
(batch / "results.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
print(f"{len(rows)} rows; proof_lines missing: {sum(r['proof_lines'] is None for r in rows)}")
