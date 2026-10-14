"""Acceptance tests for harness/verify_verus.py.

Usage: python3 -I harness/tests/verus/run_tests.py
Builds each case from a data/verus stub, writes it to harness/tests/verus/cases/,
runs verify_verus.py as a subprocess (as run.py would), prints a table, and exits 1
if any case gets the wrong verdict.
"""
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "harness"))
import verify_verus as vv  # noqa: E402

CASES_DIR = pathlib.Path(__file__).resolve().parent / "cases"
LS = "linear_search"
ENS = """        ensures
            result <= seq.len(),
            forall|i: int| #![trigger seq[i]] 0 <= i < result ==> seq[i] < target,
            forall|i: int| #![trigger seq[i]] result <= i < seq.len() ==> seq[i] >= target,"""

LS_REF = """    {
        let mut i: usize = 0;
        while i < seq.len()
            invariant
                i <= seq.len(),
                seq.len() <= 0x7FFFFFFF,
                is_sorted(seq@),
                forall|k: int| #![trigger seq[k]] 0 <= k < i ==> seq[k] < target,
            decreases seq.len() - i,
        {
            if seq[i] >= target {
                assert forall|k: int| #![trigger seq[k]] i <= k < seq.len() implies seq[k] >= target by {
                    assert(seq@[i as int] <= seq@[k]);
                }
                return i;
            }
            i += 1;
        }
        i
    }
    """

CASES = [
    # name, task, {region: text} or callable(text)->text, expect_pass, note
    ("reference", LS, {"code": LS_REF}, True, "loop with decreases"),
    ("ref_stack_push", "stack_push", {"code": "        {\n            self.data.push(value);\n        }\n        "},
     True, "main fn named `push` calls Vec::push (probe false-positive check)"),
    ("unchanged_stub", LS, {}, False, "empty body"),
    ("assume_false", LS, {"code": "    {\n        assume(false);\n        0\n    }\n    "}, False, "(ii)"),
    ("weaken_ensures", LS, lambda t: t.replace(
        ENS, "\n".join(ENS.splitlines()[:3])).replace(
        "    {\n\n    }\n    // </code>", "    {\n        0\n    }\n    // </code>"), False,
     "(iii) third ensures clause deleted, body returns 0"),
    ("external_body_helper", LS, {
        "proofs": "    #[verifier::external_body]\n    fn helper(seq: &Vec<i32>, target: i32) -> (result: usize)\n"
                  + ENS + "\n    { 0 }\n",
        "code": "    {\n        helper(seq, target)\n    }\n    "}, False, "(iv) trusted helper"),
    ("external_body_dangling", LS, {"proofs": "    #[verifier::external_body]\n",
                                    "code": "    {\n        0\n    }\n    "}, False,
     "(iv) attribute attaches to the fn under spec"),
    ("inner_external_body", LS, {"code": "    {\n        #![verifier::external_body]\n        0\n    }\n    "}, False,
     "inner attribute; passes upstream '#[verifier' filter"),
    ("fn_value_recursion", LS, {
        "helpers": "    fn h(seq: &Vec<i32>, target: i32) -> (result: usize)\n" + ENS + "\n    { let f = h; f(seq, target) }\n",
        "code": "    {\n        h(seq, target)\n    }\n    "}, False, "recursion through a fn value"),
    ("old_style_attr", LS, {"proofs": "    #[verifier(external_body)]\n    fn h() {}\n"}, False, "#[verifier(..)]"),
    ("cfg_dangling", LS, {"proofs": "    #[cfg(any())]\n"}, False, "removes the fn under spec"),
    ("infinite_loop", LS, {"code": "    {\n        loop {}\n    }\n    "}, False, "partial correctness"),
    ("while_no_decreases", LS, {"code": LS_REF.replace("            decreases seq.len() - i,\n", "")}, False,
     "loop without decreases"),
    ("main_recursion", LS, {"code": "    {\n        linear_search_lower_bound(seq, target)\n    }\n    "}, False,
     "fn under spec calls itself"),
    ("helper_recursion", LS, {
        "helpers": "    fn h(seq: &Vec<i32>, target: i32) -> (result: usize)\n" + ENS + "\n    { h(seq, target) }\n",
        "code": "    {\n        h(seq, target)\n    }\n    "}, False, "helper recursion without decreases"),
    ("scope_escape", LS, {"helpers": "    }\n    mod m {\n    use vstd::prelude::*;\n"}, False,
     "closes verus!/module scope"),
    ("comment_over_spec", LS, {"proofs": "    /*\n"}, False, "block comment swallows spec"),
    ("shadow_type", LS, {"helpers": "    struct Vec<T>(T);\n"}, False, "item shadows a fixed name"),
    ("glob_shadow", LS, {"helpers": "    mod evil { pub spec fn f() -> bool { true } }\n    use evil::*;\n"}, False,
     "glob import from own module"),
    ("assume_new", LS, {"code": "    {\n        let t: Tracked<u8> = Tracked::assume_new();\n        0\n    }\n    "},
     False, "Tracked::assume_new"),
    ("admit", LS, {"code": "    {\n        proof { admit(); }\n        0\n    }\n    "}, False, "admit()"),
    ("unsafe_block", LS, {"code": "    {\n        unsafe { }\n        0\n    }\n    "}, False, "unsafe"),
    ("truncate", LS, {"code": "    {\n        #[verifier::truncate] (0u64 as usize)\n    }\n    "}, False,
     "#[verifier::truncate]"),
    ("markers_removed", LS, lambda t: t.replace("// <proofs>", ""), False, "marker deleted"),
]


def apply(text: str, edit) -> str:
    if callable(edit):
        return edit(text)
    fixed, reg = vv.split(text)
    reg.update(edit)
    return fixed[0] + reg["helpers"] + fixed[1] + reg["proofs"] + fixed[2] + reg["code"] + fixed[3]


def main() -> int:
    CASES_DIR.mkdir(exist_ok=True)
    rows, bad = [], 0
    for name, task, edit, expect, note in CASES:
        tdir = ROOT / "data/verus" / task
        stub = (tdir / f"{task}.rs").read_text()
        sub = CASES_DIR / f"{name}.rs"
        sub.write_text(apply(stub, edit))
        r = subprocess.run([sys.executable, "-I", str(ROOT / "harness/verify_verus.py"), str(tdir), str(sub)],
                           capture_output=True, text=True, timeout=900)
        v = json.loads(r.stdout.strip().splitlines()[-1])
        good = v["pass"] == expect
        bad += not good
        detail = " ".join(str(v.get("detail", "")).split())[:90]
        rows.append((name, task, "accept" if expect else "reject", "PASS" if v["pass"] else "fail",
                     v["stage"], f"{v.get('seconds', '')}", "ok" if good else "WRONG", detail))
    hdr = ("case", "task", "want", "verdict", "stage", "sec", "check", "detail")
    w = [max(len(str(x[i])) for x in rows + [hdr]) for i in range(7)]
    for row in [hdr] + rows:
        print(" | ".join(str(c).ljust(w[i]) for i, c in enumerate(row[:7])) + " | " + row[7])
    print(f"\n{len(rows) - bad}/{len(rows)} correct")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
