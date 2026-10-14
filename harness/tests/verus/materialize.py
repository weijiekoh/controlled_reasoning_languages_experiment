"""Materialize AlgoVeri Verus tasks into data/verus/<task>/ and write problem lists.

Usage: python3 -I harness/tests/verus/materialize.py

For each data/algoveri/algoveri_data/<task>/verus_spec.rs:
  data/verus/<task>/<task>.rs       stub the agent edits (verbatim; see PATCHES)
  data/verus/<task>/description.md  verus_nl.txt (the authors give it in the prompt)
  data/verus/<task>/task.json       id, entry, main_fn, regions, source hash
Then splice `{ assume(false); vstd::pervasive::unreached() }` into <code> of every
stub and run verus once in cotml-verus (no network). Tasks with 0 errors go to
problems/verus_ok.txt. problems/probe_verus.txt = 20 tasks from
random.Random(20261013).shuffle(sorted(ok)), then sorted.
"""
import hashlib
import json
import pathlib
import random
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "harness"))
import verify_verus as vv  # noqa: E402

SRC = ROOT / "data/algoveri/algoveri_data"
DST = ROOT / "data/verus"
HOLE = "    {\n        assume(false);\n        vstd::pervasive::unreached()\n    }\n    "
# Typo fixes in upstream stubs. Each keeps the spec text and repairs a marker only.
PATCHES = {
    "longest_increasing_subsequence": [
        ("            exists|sub: Seq<int>| is_valid_is(seq@, sub) && sub.len() == result,\n    // <spec>\n",
         "            exists|sub: Seq<int>| is_valid_is(seq@, sub) && sub.len() == result,\n    // </spec>\n",
         "closing marker written as `// <spec>`; upstream parse_llm_response cannot find <spec>...</spec>, "
         "so this task can never pass in the authors' pipeline"),
    ],
}
FIXED_DESC = ("Everything outside the three editable regions is fixed: the `use` lines, the "
              "<preamble> block (definitions, spec fns, and any exec fns given there), the <spec> "
              "block (signature, requires, ensures of the function under test), fn main, and all "
              "marker comments. Compared token-wise; comments and whitespace are ignored.")


def build() -> list[str]:
    tasks = sorted(p.name for p in SRC.iterdir() if (p / "verus_spec.rs").is_file())
    for t in tasks:
        raw = (SRC / t / "verus_spec.rs").read_text()
        text, notes = raw, []
        for old, new, why in PATCHES.get(t, []):
            assert text.count(old) == 1, (t, old)
            text = text.replace(old, new)
            notes.append(why)
        fixed, regions = vv.split(text)
        d = DST / t
        d.mkdir(parents=True, exist_ok=True)
        (d / f"{t}.rs").write_text(text)
        (d / "description.md").write_text((SRC / t / "verus_nl.txt").read_text().strip() + "\n")
        meta = {
            "id": t, "entry": f"{t}.rs", "description": "description.md",
            "main_fn": vv.main_fn_name(fixed[2]),
            "editable_regions": {
                "helpers": "between `// <helpers>` and `// </helpers>`: helper spec fns and exec helpers",
                "proofs": "between `// <proofs>` and `// </proofs>`: lemmas (proof fns)",
                "code": "between `// <code>` and `// </code>`: exactly one block `{ ... }`, the body "
                        "of the function under spec",
            },
            "fixed": FIXED_DESC,
            "source": f"data/algoveri/algoveri_data/{t}/verus_spec.rs",
            "source_sha256": hashlib.sha256(raw.encode()).hexdigest(),
            "patches": notes,
        }
        (d / "task.json").write_text(json.dumps(meta, indent=1) + "\n")
    return tasks


def hole_check(tasks: list[str]) -> dict[str, str]:
    """Return {task: 'ok' | error excerpt} for the stub with a hole body."""
    with tempfile.TemporaryDirectory(prefix="verus_mat_", dir=ROOT / "runs") as tmp:
        for t in tasks:
            text = (DST / t / f"{t}.rs").read_text()
            fixed, reg = vv.split(text)
            spliced = fixed[0] + reg["helpers"] + fixed[1] + reg["proofs"] + fixed[2] + HOLE + fixed[3]
            pathlib.Path(tmp, f"{t}.rs").write_text(spliced)
            pathlib.Path(tmp, f"{t}.rs").chmod(0o644)
        pathlib.Path(tmp).chmod(0o755)
        script = ("cd /tmp; for f in /v/*.rs; do s=$(date +%s.%N); timeout 300 verus $f > /tmp/o 2>&1; "
                  "rc=$?; e=$(date +%s.%N); echo \"@@ $(basename $f .rs) $rc $s $e\"; "
                  "grep -E '^error|verification results' /tmp/o | head -3; done")
        r = subprocess.run(["docker", "run", "--rm", "--network", "none", "--user", "1000:1000",
                            "--read-only", "--tmpfs", "/tmp:exec,mode=1777", "-e", "HOME=/tmp",
                            "-v", f"{tmp}:/v:ro", vv.IMAGE, "bash", "-c", script],
                           capture_output=True, text=True, timeout=7200)
    res, cur, lines = {}, None, []
    for line in (r.stdout + "\n@@ END 0 0 0").splitlines():
        if line.startswith("@@ "):
            if cur:
                ok = cur[1] == "0" and any(re.search(r"verified, 0 errors", x) for x in lines)
                res[cur[0]] = "ok" if ok else " | ".join(lines)[:300]
                print(f"{cur[0]:34s} {'ok' if ok else 'FAIL'} {float(cur[3]) - float(cur[2]):.1f}s")
            cur, lines = line.split()[1:], []
        else:
            lines.append(line)
    return res


def main() -> None:
    tasks = build()
    res = hole_check(tasks)
    ok = sorted(t for t in tasks if res.get(t) == "ok")
    bad = {t: res.get(t, "no result") for t in tasks if t not in ok}
    hdr = ("# AlgoVeri Verus tasks whose stub verifies with the body replaced by "
           "`{ assume(false); unreached() }` (verus 0.2025.01.13.da1c777).\n")
    for t, why in bad.items():
        hdr += f"# excluded {t}: {why}\n"
    (ROOT / "problems/verus_ok.txt").write_text(hdr + "".join(t + "\n" for t in ok))
    shuf = list(ok)
    random.Random(20261013).shuffle(shuf)
    probe = sorted(shuf[:20])
    (ROOT / "problems/probe_verus.txt").write_text(
        "# 20 tasks: random.Random(20261013).shuffle(sorted(verus_ok)), first 20, sorted\n"
        + "".join(t + "\n" for t in probe))
    print(f"{len(tasks)} tasks, {len(ok)} ok, excluded: {sorted(bad)}")


if __name__ == "__main__":
    main()
