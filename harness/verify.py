"""Verify a Lean submission against a target statement file.

Usage: python3 -I verify.py <target.lean> <submission.lean>
Prints one JSON object: {"pass": bool, "stage": str, "detail": str}.

Stages: source (banned tokens or changed imports), compile (submission fails to
build), safeverify (statement changed, extra axioms, kernel rejects), ok.
Every Lean process runs in the cotml-sandbox image with no network.
"""
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
TC = os.environ.get("COTML_TC") or str(pathlib.Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1")
LEAN_ENV = str(ROOT / "lean_env")
SAFE_VERIFY = str(ROOT / "harness/safeverify/.lake/build/bin/safe_verify")
TARGET_CACHE = ROOT / "runs/targets"
COMPILE_TIMEOUT = 600
SAFEVERIFY_TIMEOUT = 1800   # kernel replay of decide-heavy proofs can exceed 10 min

BANNED = [
    r"implemented_by", r"@\[\s*extern", r"\bunsafe\b", r"skipKernelTC", r"run_cmd",
    r"#eval", r"run_tac", r"\bopaque\b", r"debug\.", r"Lean\.Elab", r"Lean\.Meta\.",
    r"addDecl", r"Environment",
]


def sandbox(mounts: dict[str, str], cmd: str, timeout: int) -> subprocess.CompletedProcess:
    """Run cmd in a fresh no-network container. mounts maps host path to 'ro' or 'rw'."""
    args = ["docker", "run", "--rm", "--network", "none", "--memory", "12g",
            "-v", f"{TC}:{TC}:ro", "-v", f"{LEAN_ENV}:{LEAN_ENV}:ro"]
    for path, mode in mounts.items():
        args += ["-v", f"{path}:{path}:{mode}"]
    args += ["cotml-sandbox", "bash", "-c", cmd]
    try:
        return subprocess.run(args, capture_output=True, text=True, timeout=timeout + 30)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(args, 124, "", "timeout")


def imports(text: str) -> list[str]:
    return [line.strip() for line in text.splitlines() if line.startswith("import ")]


def target_olean(target: pathlib.Path) -> pathlib.Path:
    """Compile the trusted target once and cache its olean."""
    out = TARGET_CACHE / f"{target.stem}_{hashlib.sha256(str(target).encode()).hexdigest()[:8]}"
    olean = out / "Target.olean"
    if not olean.exists():
        out.mkdir(parents=True, exist_ok=True)
        shutil.copy(target, out / "Target.lean")
        r = sandbox({str(out): "rw"}, f"cd {out} && lean -o Target.olean Target.lean", COMPILE_TIMEOUT)
        if not olean.exists():
            raise RuntimeError(f"target {target} failed to compile: {r.stdout[-500:]} {r.stderr[-500:]}")
    return olean


def verify(target: pathlib.Path, submission: pathlib.Path) -> dict:
    sub_text = submission.read_text()
    for pat in BANNED:
        if re.search(pat, sub_text):
            return {"pass": False, "stage": "source", "detail": f"banned token: {pat}"}
    if imports(sub_text) != imports(target.read_text()):
        return {"pass": False, "stage": "source", "detail": "imports differ from target"}

    t_olean = target_olean(target)
    with tempfile.TemporaryDirectory(dir=ROOT / "runs") as tmp:
        shutil.copy(submission, f"{tmp}/Submission.lean")
        r = sandbox({tmp: "rw"}, f"cd {tmp} && lean -o Submission.olean Submission.lean", COMPILE_TIMEOUT)
        log = r.stdout + r.stderr
        if r.returncode != 0 or not pathlib.Path(f"{tmp}/Submission.olean").exists():
            return {"pass": False, "stage": "compile", "detail": log[-1500:]}
        if "declaration uses `sorry`" in log:
            return {"pass": False, "stage": "compile", "detail": "uses sorry"}
        r = sandbox({tmp: "ro", str(t_olean.parent): "ro", SAFE_VERIFY: "ro"},
                    f"{SAFE_VERIFY} {t_olean} {tmp}/Submission.olean", SAFEVERIFY_TIMEOUT)
        if r.returncode != 0:
            return {"pass": False, "stage": "safeverify", "detail": (r.stdout + r.stderr)[-1500:]}
    return {"pass": True, "stage": "ok", "detail": ""}


if __name__ == "__main__":
    print(json.dumps(verify(pathlib.Path(sys.argv[1]).resolve(), pathlib.Path(sys.argv[2]).resolve())))
