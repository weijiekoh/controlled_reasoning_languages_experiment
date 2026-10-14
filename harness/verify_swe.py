"""Verify a model patch for a SWE-bench Verified instance with the official harness.

Usage: python3 -I verify_swe.py <task_dir> <model_patch.diff>
Prints one JSON object: {"pass": bool, "stage": str, "detail": str, "seconds": float}.

<task_dir> holds task.json (instance_id). The evaluation runs
data/.venv-swe/bin/python -m swebench.harness.run_evaluation (swebench 5.0.2) on
data/swebench_verified.jsonl in a new container of the instance's eval image.
That container is on the default Docker bridge network (the harness sets no
network mode). Logs and reports go to <patch dir>/swe_eval/.

Stages:
  no_patch      patch file absent or empty
  patch_apply   no `git apply` / `patch` variant applied the patch
  tests         patch applied; FAIL_TO_PASS or PASS_TO_PASS tests failed, or tests timed out
  verify_error  harness failure (no report, infrastructure failure, exception)
  ok            resolved
"""
import json
import pathlib
import subprocess
import sys
import time
import uuid

ROOT = pathlib.Path(__file__).resolve().parent.parent
PY = ROOT / "data/.venv-swe/bin/python"
DATASET = ROOT / "data/swebench_verified.jsonl"
MODEL_NAME = "cotml"
TEST_TIMEOUT = 1800


def verify(task_dir: pathlib.Path, patch_path: pathlib.Path) -> dict:
    iid = json.loads((task_dir / "task.json").read_text())["instance_id"]
    patch = patch_path.read_text(errors="replace") if patch_path.is_file() else ""
    if not patch.strip():
        return {"pass": False, "stage": "no_patch", "detail": "empty patch"}
    if not patch.endswith("\n"):
        patch += "\n"
    work = patch_path.resolve().parent / "swe_eval"
    work.mkdir(exist_ok=True)
    run_id = f"{MODEL_NAME}-{time.strftime('%Y%m%d%H%M%S')}-{uuid.uuid4().hex[:8]}"
    preds = work / f"preds.{run_id}.jsonl"
    preds.write_text(json.dumps({"instance_id": iid, "model_name_or_path": MODEL_NAME,
                                 "model_patch": patch}) + "\n")
    cmd = [str(PY), "-m", "swebench.harness.run_evaluation", "--dataset_name", str(DATASET),
           "--split", "test", "--predictions_path", str(preds), "--instance_ids", iid,
           "--max_workers", "1", "--run_id", run_id, "--timeout", str(TEST_TIMEOUT),
           "--report_dir", str(work)]
    try:
        r = subprocess.run(cmd, cwd=work, capture_output=True, text=True, timeout=TEST_TIMEOUT + 900)
    except subprocess.TimeoutExpired:
        return {"pass": False, "stage": "verify_error", "detail": "run_evaluation did not finish"}
    (work / f"harness.{run_id}.log").write_text(r.stdout + "\n--- stderr\n" + r.stderr)

    report_file = work / f"{MODEL_NAME}.{run_id}.json"
    inst_dir = work / "logs/run_evaluation" / run_id / MODEL_NAME / iid
    inst_log = inst_dir / "run_instance.log"
    log_text = inst_log.read_text(errors="replace") if inst_log.is_file() else ""
    if not report_file.is_file():
        return {"pass": False, "stage": "verify_error",
                "detail": f"no run report; rc={r.returncode}; {(r.stdout + r.stderr)[-600:]}"}
    rep = json.loads(report_file.read_text())
    if iid in rep.get("resolved_ids", []):
        return {"pass": True, "stage": "ok", "detail": f"resolved (run_id {run_id})"}
    if ">>>>> Patch Apply Failed" in log_text:
        tail = log_text.split(">>>>> Patch Apply Failed", 1)[1].strip()
        return {"pass": False, "stage": "patch_apply", "detail": tail[:600]}
    if iid in rep.get("infra_failure_ids", []):
        return {"pass": False, "stage": "verify_error",
                "detail": f"infra failure: {rep.get('failure_reasons', {}).get(iid)}"}
    if "Test timed out after" in log_text:
        return {"pass": False, "stage": "tests", "detail": f"tests timed out after {TEST_TIMEOUT}s"}
    inst_report = inst_dir / "report.json"
    if not inst_report.is_file():
        return {"pass": False, "stage": "verify_error",
                "detail": f"no instance report; {log_text[-600:] or (r.stdout + r.stderr)[-600:]}"}
    st = json.loads(inst_report.read_text()).get(iid, {}).get("tests_status") or {}
    parts = []
    for k in ("FAIL_TO_PASS", "PASS_TO_PASS"):
        s = st.get(k) or {}
        ok, bad = s.get("success") or [], s.get("failure") or []
        parts.append(f"{k} {len(ok)}/{len(ok) + len(bad)}" + (f" failing: {', '.join(bad[:3])}" if bad else ""))
    return {"pass": False, "stage": "tests", "detail": "; ".join(parts)[:800]}


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    t0 = time.monotonic()
    try:
        v = verify(pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]))
    except Exception as e:   # the caller reads one JSON line; never die without it
        v = {"pass": False, "stage": "verify_error", "detail": repr(e)[:800]}
    v["seconds"] = round(time.monotonic() - t0, 1)
    print(json.dumps(v))
    return 0


if __name__ == "__main__":
    sys.exit(main())
