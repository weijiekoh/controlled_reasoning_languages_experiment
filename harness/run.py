#!/usr/bin/env python3
"""Run Claude Code on Lean 4 problems in isolated containers and verify the results.

Usage:
  python3 harness/run.py --bench minif2f --problems names.txt --condition bare,cod \
      --effort medium --max-turns 60 --max-budget-usd 3 --timeout-min 30 --parallel 4 \
      --out runs/pilot1/ [--network bridge] [--proxy URL] [--dry-run]

--problems is a file (one name per line, '#' comments) or a comma-separated list.
--condition and --effort take comma-separated lists. Each (problem, condition,
effort) gets runs/<batch>/<problem>__<condition>__<effort>/ with work/, agent.jsonl,
agent.stderr, prompt.txt, cmd.json and result.json. A run with result.json is
skipped. Each finished run appends one line to runs/<batch>/results.jsonl.

--enforce-min-checks N resumes (at most --enforce-rounds times) a run that ends with
GIVEUP after fewer than N lean compiles; agent.jsonl then holds all invocations and
enforce.json records the decisions.
"""
import argparse
import concurrent.futures as cf
import datetime
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import threading
import time
import uuid

import verify_verus   # harness/ is sys.path[0] when run as a script

ROOT = pathlib.Path(__file__).resolve().parent.parent
RUNS = ROOT / "runs"
TC = os.environ.get("COTML_TC") or str(pathlib.Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1")
LAKE = ROOT / "lean_env/.lake"
IMAGE = "cotml-sandbox"
MODEL = "claude-sonnet-5-5"   # default; override with --model
BENCH_DIRS = {"minif2f": ROOT / "data/miniF2F-lean4/MiniF2F/Test", "putnam": ROOT / "data/putnam_subst",
              "fateh": ROOT / "data/fateh", "fatex": ROOT / "data/fatex", "combi": ROOT / "data/combi",
              "cam": ROOT / "data/cam", "verus": ROOT / "data/verus", "swe": ROOT / "data/swe"}
VERIFY = ROOT / "harness/verify.py"
PROMPT = ROOT / "harness/prompt.md"
VERUS_IMAGE = "cotml-verus"
VERIFY_VERUS = ROOT / "harness/verify_verus.py"
PROMPT_VERUS = ROOT / "harness/prompt_verus.md"
VERIFY_SWE = ROOT / "harness/verify_swe.py"
PROMPT_SWE = ROOT / "harness/prompt_swe.md"
CLAUDE_BIN = ROOT / "harness/docker/claude"
SWE_VERIFY_TIMEOUT = 3600
# The SWE-bench eval images keep the project in the conda env "testbed"; the eval script activates it.
SWE_PATH = "/opt/miniconda3/envs/testbed/bin:/opt/miniconda3/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
COND_DIR = ROOT / "conditions"
COND_MOUNT = "/opt/cotml/condition.md"
VERIFY_TIMEOUT = 1800
EFFORTS = ["low", "medium", "high", "xhigh", "max"]

# Any .lean file outside /work is a leak of Lean core or Mathlib source.
ISOLATION_CMD = ("find / \\( -path /proc -o -path /sys -o -path /dev -o -path /work \\) -prune "
                 "-o -name '*.lean' -print 2>/dev/null | head -20")
LEAN_RE = re.compile(r"(?<![\w.\-])lean\s")
VERUS_RE = re.compile(r"(?<![\w.\-])verus\s")
TEST_RE = re.compile(r"pytest|tox|python -m|runtests")
# A path component or file name that marks a test file in a SWE-bench repo.
TEST_PATH_RE = re.compile(r"(^|/)(tests?|testing)/|(^|/)(test_[^/]*|[^/]*_tests?\.py|conftest\.py)$")
SEARCH_RE = re.compile(r"(?<![\w.'])(?:(?:exact|apply|rw|simp)\?|hint(?![\w'?]))")
SORRY_RE = re.compile(r"\bsorry\b")
COMMENT_RE = re.compile(r"/-.*?-/|--[^\n]*", re.S)

RUNNING: set[str] = set()          # names of live agent containers
VERIFY_LOCKS: dict[str, threading.Lock] = {}
LOCKS_GUARD = threading.Lock()


# ---------------------------------------------------------------- docker

def lean_mounts() -> list[str]:
    """Read-only mounts of compiled Lean and Mathlib output only (no .lean source)."""
    dirs = [f"{TC}/bin", f"{TC}/lib"]
    dirs += sorted(str(p) for p in LAKE.glob("packages/*/.lake/build/lib/lean") if p.is_dir())
    if (LAKE / "build/lib/lean").is_dir():
        dirs.append(str(LAKE / "build/lib/lean"))
    args = []
    for d in dirs:
        args += ["-v", f"{d}:{d}:ro"]
    return args


def docker_args(name: str, args, work: pathlib.Path | None, cond: pathlib.Path | None,
                image: str | None = None) -> list[str]:
    if args.bench == "swe":   # the task's eval image, as root (the images expect it), project in /testbed
        a = ["docker", "run", "--rm", "--name", name, "--network", args.network,
             "--memory", "8g", "--cpus", "4", "-w", "/testbed", "-e", f"PATH={SWE_PATH}",
             "-e", "HOME=/tmp/home", "--tmpfs", "/tmp/home:mode=0700", "-e", "IS_SANDBOX=1",
             "-v", f"{CLAUDE_BIN}:/usr/local/bin/claude:ro"]   # IS_SANDBOX: claude refuses root otherwise
    else:
        a = ["docker", "run", "--rm", "--name", name, "--network", args.network,
             "--user", "1000:1000", "--memory", "8g", "--cpus", "4",
             "-e", "HOME=/tmp/home", "--tmpfs", "/tmp/home:uid=1000,gid=1000,mode=0700"]
    if os.environ.get("ANTHROPIC_API_KEY"):
        a += ["-e", "ANTHROPIC_API_KEY"]   # value passed from host env, not on the command line
    if args.proxy:
        for k in ("HTTPS_PROXY", "HTTP_PROXY", "https_proxy", "http_proxy"):
            a += ["-e", f"{k}={args.proxy}"]
        a += ["-e", "NO_PROXY=localhost,127.0.0.1", "-e", "no_proxy=localhost,127.0.0.1",
              "-e", "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1"]
    if args.bench not in ("verus", "swe"):
        a += lean_mounts()
    if work is not None:
        a += ["-v", f"{work}:/work:rw"]
    if cond is not None:
        a += ["-v", f"{cond}:{COND_MOUNT}:ro"]
    return a + [image or (VERUS_IMAGE if args.bench == "verus" else IMAGE)]


def container_name(batch: str) -> str:
    return "cotml-" + re.sub(r"[^A-Za-z0-9_.-]", "_", batch)[:40] + "-" + uuid.uuid4().hex[:10]


def run_container(cmd: list[str], name: str, out: pathlib.Path, err: pathlib.Path, timeout_s: float,
                  mode: str = "wb"):
    """Run cmd, stream stdout to out. Kill the container after timeout_s. Return (rc, timed_out, seconds)."""
    t0 = time.monotonic()
    timed_out = False
    with open(out, mode) as fo, open(err, mode) as fe:
        p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=fo, stderr=fe)
        owner = name not in RUNNING   # a detached container stays registered by its owner
        RUNNING.add(name)
        try:
            rc = p.wait(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            timed_out = True
            subprocess.run(["docker", "kill", name], capture_output=True)
            try:
                rc = p.wait(timeout=60)
            except subprocess.TimeoutExpired:
                p.kill()
                rc = p.wait()
        finally:
            if owner:
                RUNNING.discard(name)
    return rc, timed_out, time.monotonic() - t0


def isolation_check(args) -> list[str]:
    """Return the .lean files visible in a fresh agent container (must be empty)."""
    cmd = docker_args(container_name("preflight"), args, None, None) + ["bash", "-c", ISOLATION_CMD]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        raise RuntimeError(f"isolation check failed to run: {r.stderr[-500:]}")
    return [line for line in r.stdout.splitlines() if line.strip()]


# ---------------------------------------------------------------- parsing

USAGE_KEYS = ("input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens")


def merge_results(results: list[dict]) -> dict | None:
    """Combine the result events of resumed invocations of one session.

    usage, num_turns and duration_ms are per invocation: sum them. total_cost_usd, modelUsage and
    duration_api_ms are cumulative over the resumed session: the last event has the total.
    Take the last event for all other fields.
    """
    if len(results) <= 1:
        return results[0] if results else None
    r = dict(results[-1])
    usage = dict(r.get("usage") or {})
    for k in USAGE_KEYS:
        usage[k] = sum((x.get("usage") or {}).get(k) or 0 for x in results)
    usage["output_tokens_details"] = {"thinking_tokens": sum(
        ((x.get("usage") or {}).get("output_tokens_details") or {}).get("thinking_tokens") or 0 for x in results)}
    r["usage"] = usage
    for k in ("num_turns", "duration_ms"):
        r[k] = sum(x.get(k) or 0 for x in results)
    r["permission_denials"] = [d for x in results for d in x.get("permission_denials") or []]
    return r


def parse_stream(path: pathlib.Path) -> dict:
    """Extract the result events (merged), usage, and tool calls from a stream-json log."""
    results, init = [], None
    usage_by_msg: dict[str, dict] = {}
    seen_tools: set[str] = set()
    tool_counts: dict[str, int] = {}
    bash_cmds: list[str] = []
    edit_texts: list[str] = []
    if path.exists():
        for line in path.read_text(errors="replace").splitlines():
            try:
                ev = json.loads(line)
            except ValueError:
                continue
            if not isinstance(ev, dict):
                continue
            t = ev.get("type")
            if t == "system" and ev.get("subtype") == "init":
                init = ev
            elif t == "result":
                results.append(ev)
            elif t == "assistant":
                msg = ev.get("message") or {}
                if msg.get("id") and msg.get("usage"):
                    usage_by_msg[msg["id"]] = msg["usage"]   # keep the last usage per message
                for c in msg.get("content") or []:
                    if not isinstance(c, dict) or c.get("type") != "tool_use":
                        continue
                    if c.get("id") in seen_tools:
                        continue
                    seen_tools.add(c.get("id"))
                    tool = c.get("name", "?")
                    inp = c.get("input") or {}
                    tool_counts[tool] = tool_counts.get(tool, 0) + 1
                    if tool == "Bash":
                        bash_cmds.append(str(inp.get("command", "")))
                    elif tool in ("Edit", "Write", "MultiEdit"):
                        parts = [inp.get("new_string"), inp.get("content")]
                        parts += [e.get("new_string") for e in inp.get("edits") or [] if isinstance(e, dict)]
                        edit_texts.append("\n".join(str(x) for x in parts if x))
    return {"result": merge_results(results), "n_results": len(results), "init": init,
            "usage_by_msg": usage_by_msg, "tool_counts": tool_counts,
            "bash_cmds": bash_cmds, "edit_texts": edit_texts}


def strip_comments(text: str) -> str:
    return COMMENT_RE.sub(" ", text)


def proof_text(orig: str, sub: str, name: str):
    """Return (proof body after the theorem statement, statement_prefix_changed)."""
    m = list(SORRY_RE.finditer(orig))[-1]
    prefix, suffix = orig[:m.start()].rstrip(), orig[m.end():]   # `:= by sorry` -> prefix ends `by`
    changed = False
    if sub.startswith(prefix):
        body = sub[len(prefix):]
    else:
        changed = True
        k = prefix.rfind(f"theorem {name}")
        stmt = prefix[k:] if k >= 0 else ""
        j = sub.find(stmt) if stmt else -1
        if j < 0:
            return None, changed
        body = sub[j + len(stmt):]
    if suffix.strip() and body.endswith(suffix):
        body = body[: -len(suffix)]
    return body.strip(), changed


# ---------------------------------------------------------------- verify

def run_verify(target: pathlib.Path, sub: pathlib.Path) -> dict:
    if not sub.exists():
        return {"pass": False, "stage": "missing", "detail": f"{sub.name} not found in work/"}
    if target.parent.parent == BENCH_DIRS["swe"]:   # target = data/swe/<id>/task.json, sub = model_patch.diff
        try:
            r = subprocess.run([sys.executable, "-I", str(VERIFY_SWE), str(target.parent), str(sub)],
                               capture_output=True, text=True, timeout=SWE_VERIFY_TIMEOUT)
            return json.loads(r.stdout.strip().splitlines()[-1])
        except (subprocess.TimeoutExpired, ValueError, IndexError):
            return {"pass": False, "stage": "verify_error", "detail": "verify_swe.py failed"}
    if target.parent.parent == BENCH_DIRS["verus"]:   # target = data/verus/<task>/<task>.rs
        try:
            r = subprocess.run([sys.executable, "-I", str(VERIFY_VERUS), str(target.parent), str(sub)],
                               capture_output=True, text=True, timeout=VERIFY_TIMEOUT)
            return json.loads(r.stdout.strip().splitlines()[-1])
        except (subprocess.TimeoutExpired, ValueError, IndexError):
            return {"pass": False, "stage": "verify_error", "detail": "verify_verus.py failed"}
    with LOCKS_GUARD:
        lock = VERIFY_LOCKS.setdefault(target.stem, threading.Lock())
    with lock:   # verify.py caches the target olean per problem; avoid concurrent first compiles
        try:
            r = subprocess.run([sys.executable, "-I", str(VERIFY), str(target), str(sub)],
                               capture_output=True, text=True, timeout=VERIFY_TIMEOUT)
        except subprocess.TimeoutExpired:
            return {"pass": False, "stage": "verify_error", "detail": "verify.py timeout"}
    try:
        v = json.loads(r.stdout.strip().splitlines()[-1])
        if isinstance(v, dict) and "pass" in v:
            return v
    except (ValueError, IndexError):
        pass
    return {"pass": False, "stage": "verify_error", "detail": (r.stdout + r.stderr)[-1500:]}


def classify(v: dict, timed_out: bool, result: dict | None, max_turns: int | None = None) -> str:
    if v.get("pass"):
        return "solved"
    if v.get("stage") == "verify_error":
        return "error"
    if timed_out:
        return "timeout"
    if result is None:
        return "error"
    subtype = str(result.get("subtype", ""))
    # Claude Code reports subtype "success" at the turn cap; detect the cap from the turn count.
    if subtype.startswith("error_max") or (max_turns and (result.get("num_turns") or 0) >= max_turns):
        return "hit_cap"
    if subtype == "success" and not result.get("is_error"):
        return "gave_up"
    return "error"


# ---------------------------------------------------------------- one run

def fake_stream(path: pathlib.Path, fname: str) -> None:
    """Write a synthetic stream-json log for --dry-run."""
    sid = "dry-run"
    usage = {"input_tokens": 0, "output_tokens": 0, "cache_read_input_tokens": 0,
             "cache_creation_input_tokens": 0}
    events = [
        {"type": "system", "subtype": "init", "session_id": sid, "model": MODEL, "dry_run": True},
        {"type": "assistant", "session_id": sid, "message": {
            "id": "msg_dry", "role": "assistant", "usage": usage, "content": [
                {"type": "tool_use", "id": "tu_dry", "name": "Bash",
                 "input": {"command": f"lean /work/{fname}"}}]}},
        {"type": "result", "subtype": "success", "is_error": False, "num_turns": 1,
         "duration_ms": 0, "total_cost_usd": 0.0, "stop_reason": "end_turn",
         "terminal_reason": "dry_run", "result": "dry run", "usage": usage, "session_id": sid},
    ]
    path.write_text("".join(json.dumps(e) + "\n" for e in events))


def dry_checks(cmd_prefix: list[str], name: str, rd: pathlib.Path, fname: str, checker: str = "lean") -> dict:
    script = ("echo '## version'; claude --version; "
              "echo '## lean'; s=$(date +%s.%N); " + checker + " /work/" + fname + "; rc=$?; e=$(date +%s.%N); "
              "echo \"## lean_rc $rc $s $e\"; echo '## isolation'; " + ISOLATION_CMD + "; echo '## end'")
    log = rd / "dryrun.log"
    rc, timed_out, secs = run_container(cmd_prefix + ["bash", "-c", script], name, log, rd / "dryrun.stderr", 900)
    text = log.read_text(errors="replace")
    sec = {}
    cur = None
    for line in text.splitlines():
        if line.startswith("## "):
            cur = line[3:].split()[0]
            if cur == "lean_rc":
                code, s, e = line.split()[2:]
                sec["lean_rc"] = int(code)
                sec["lean_seconds"] = round(float(e) - float(s), 2)
            continue
        if cur:
            sec.setdefault(cur, []).append(line)
    hits = sec.get("isolation", [])
    return {"container_rc": rc, "timed_out": timed_out, "seconds": round(secs, 1),
            "claude_version": " ".join(sec.get("version", [])),
            "lean_rc": sec.get("lean_rc"), "lean_seconds": sec.get("lean_seconds"),
            "lean_output": "\n".join(sec.get("lean", []))[-1500:],
            "isolation_ok": rc == 0 and "## end" in text and not hits,
            "isolation_hits": hits}


# The eval images add one commit "SWE-bench" on top of base_commit that changes only file modes.
SWE_STATE_CMD = ("cd /testbed && git status --porcelain; echo \"## head $(git rev-parse HEAD) $(git rev-parse HEAD^) "
                 "$(git diff --raw --abbrev=40 HEAD^ HEAD | awk '$3 != $4 {x = 1} END {exit x}' && echo modeonly)\"")


def at_base(head_line: str, base: str) -> bool:
    f = head_line.split()
    # The official images carry one "SWE-bench" setup commit on top of base_commit (file modes, sometimes a
    # build fix such as pyproject.toml). The evaluator applies patches on the same image, so accept HEAD^ == base.
    return bool(f) and (f[0] == base or (len(f) >= 2 and f[1] == base))


def swe_state(name: str) -> tuple[list[str], str]:
    """Return (git status --porcelain lines, "HEAD HEAD^ [modeonly]") of /testbed in a running container."""
    r = subprocess.run(["docker", "exec", name, "bash", "-c", SWE_STATE_CMD], capture_output=True, text=True,
                       timeout=300)
    lines = r.stdout.splitlines()
    head = next((x[len("## head "):] for x in lines if x.startswith("## head ")), "")
    return [x for x in lines if not x.startswith("## head")], head


SWE_NET_PY = """import urllib.request as u
for name, opener in (("direct", u.build_opener(u.ProxyHandler({}))), ("proxy", u.build_opener())):
    try:
        opener.open("https://pypi.org/simple/", timeout=15)
        print(name, "REACHABLE")
    except Exception as e:
        print(name, "blocked", type(e).__name__, str(e)[:80])
"""


def dry_checks_swe(cmd_prefix: list[str], name: str, rd: pathlib.Path, task: dict) -> dict:
    script = ("echo '## version'; claude --version 2>&1; echo \"## claude_rc $?\"; "
              "echo '## python'; python --version 2>&1; which python; "
              "echo '## git'; " + SWE_STATE_CMD + "; "
              "echo '## network'; timeout 60 python - <<'PY' 2>&1\n" + SWE_NET_PY + "PY\n"
              "echo '## user'; id; echo '## end'")
    log = rd / "dryrun.log"
    rc, timed_out, secs = run_container(cmd_prefix + ["bash", "-c", script], name, log, rd / "dryrun.stderr", 900)
    text = log.read_text(errors="replace")
    sec, cur = {}, None
    for line in text.splitlines():
        if line.startswith("## "):
            cur = line[3:].split()[0]
            if cur in ("claude_rc", "head"):
                sec[cur] = line[len(f"## {cur} "):].strip()
            continue
        if cur:
            sec.setdefault(cur, []).append(line)
    status = [x for x in sec.get("git", []) if x.strip()]
    return {"container_rc": rc, "timed_out": timed_out, "seconds": round(secs, 1),
            "claude_version": " ".join(sec.get("version", [])), "claude_rc": sec.get("claude_rc"),
            "python": " ".join(sec.get("python", [])), "git_status": status, "head": sec.get("head"),
            "git_clean_at_base": not status and at_base(sec.get("head") or "", task["base_commit"]),
            "network_blocked": "REACHABLE" not in " ".join(sec.get("network", [])),
            "network_output": " ".join(sec.get("network", []))[-300:],
            "user": " ".join(sec.get("user", [])), "isolation_ok": rc == 0 and "## end" in text}


SWE_TEST_PATCH_CMD = ("cd /testbed && git apply - && git add -A && "
                      "git -c user.name=cotml -c user.email=cotml@localhost commit -qm test_patch")


def swe_start(prefix: list[str], name: str, task: dict) -> None:
    """Start a detached task container; check /testbed is clean at base; for "debug", commit the test patch.

    The container is added to RUNNING; the caller kills it.
    """
    r = subprocess.run(prefix[:2] + ["-d"] + prefix[2:] + ["sleep", "infinity"], capture_output=True, text=True,
                       timeout=600)
    if r.returncode != 0:
        raise RuntimeError(f"docker run -d failed: {r.stderr[-500:]}")
    RUNNING.add(name)
    status, head = swe_state(name)
    if status or not at_base(head, task["base_commit"]):
        raise RuntimeError(f"/testbed not clean at base_commit: head={head} status={status[:5]}")
    if task["framing"] == "debug":   # the failing tests exist; the model patch is diffed against this commit
        r = subprocess.run(["docker", "exec", "-i", name, "bash", "-c", SWE_TEST_PATCH_CMD],
                           input=task["test_patch"].encode(), capture_output=True, timeout=300)
        status, _ = swe_state(name)
        if r.returncode != 0 or status:
            raise RuntimeError(f"test_patch failed: {r.stderr[-500:]!r} status={status[:5]}")


def swe_collect(name: str, rd: pathlib.Path) -> None:
    """Save git_status.txt and model_patch.diff (diff against HEAD; new files included by `git add -N`)."""
    g = subprocess.run(["docker", "exec", name, "bash", "-c",
                        "cd /testbed && git status --porcelain --untracked-files=all"],
                       capture_output=True, text=True, timeout=300)
    (rd / "git_status.txt").write_text(g.stdout)
    d = subprocess.run(["docker", "exec", name, "bash", "-c",
                        "cd /testbed && git add -A -N && git -c core.fileMode=false diff --binary HEAD"],
                       capture_output=True, timeout=600)
    if d.returncode != 0:
        raise RuntimeError(f"git diff failed: {d.stderr[-500:]!r}")
    (rd / "model_patch.diff").write_bytes(d.stdout)


def run_swe(prefix: list[str], agent: list[str], name: str, rd: pathlib.Path, task: dict, args):
    """Run the agent by docker exec in a detached task container; save its diff before removal.

    Return (rc, timed_out, seconds).
    """
    try:
        swe_start(prefix, name, task)
        # Time out inside the container so that the container (and the diff) survives; outer kill is a backstop.
        limit = int(args.timeout_min * 60)
        rc, timed_out, secs = run_container(["docker", "exec", name, "timeout", "-k", "20", str(limit)] + agent,
                                            name, rd / "agent.jsonl", rd / "agent.stderr", limit + 300)
        timed_out = timed_out or rc in (124, 137)
        if timed_out and subprocess.run(["docker", "inspect", name], capture_output=True).returncode != 0:
            raise RuntimeError("agent container gone after timeout; no diff")
        swe_collect(name, rd)
    finally:
        subprocess.run(["docker", "kill", name], capture_output=True)
        RUNNING.discard(name)
    return rc, timed_out, secs


def patch_files(patch: str) -> list[str]:
    return sorted(set(re.findall(r"^diff --git a/(\S+) b/", patch, re.M)))


GIVEUP_RE = re.compile(r"giveup|give up", re.I)


def run_enforced(prefix: list[str], base: list[str], prompt: str, name: str, rd: pathlib.Path,
                 sub: pathlib.Path, args):
    """Run the agent; resume it with the enforce message while it gives up after too few lean compiles.

    All invocations run by docker exec in one detached container, so --resume finds the session
    under the same HOME. agent.jsonl gets each invocation's stream. Return (rc, timed_out, seconds, info).
    """
    t0 = time.monotonic()
    deadline = t0 + args.timeout_min * 60
    out, err = rd / "agent.jsonl", rd / "agent.stderr"
    out.write_bytes(b"")
    err.write_bytes(b"")
    n_min, msg = args.enforce_min_checks, pathlib.Path(args.enforce_message).read_text().strip()
    info = {"min_checks": n_min, "max_rounds": args.enforce_rounds, "rounds": 0, "checks_at_rounds": [],
            "decisions": [], "reason": None}
    r = subprocess.run(prefix[:2] + ["-d"] + prefix[2:] + ["sleep", "infinity"], capture_output=True, text=True,
                       timeout=600)
    if r.returncode != 0:
        raise RuntimeError(f"docker run -d failed: {r.stderr[-500:]}")
    RUNNING.add(name)
    cmd = base + ["--max-turns", str(args.max_turns), "--max-budget-usd", str(args.max_budget_usd), prompt]
    rc, timed_out = 0, False
    try:
        while True:
            rc, timed_out, _ = run_container(["docker", "exec", name] + cmd, name, out, err,
                                             max(1.0, deadline - time.monotonic()), mode="ab")
            s = parse_stream(out)
            res = s["result"] or {}
            checks = sum(1 for c in s["bash_cmds"] if LEAN_RE.search(c))
            info["checks_at_rounds"].append(checks)
            turns_left = args.max_turns - (res.get("num_turns") or 0)
            budget_left = args.max_budget_usd - (res.get("total_cost_usd") or 0)
            text = sub.read_text(errors="replace") if sub.exists() else "sorry"
            if timed_out:
                reason = "timeout"
            elif s["n_results"] < len(info["checks_at_rounds"]):
                reason = "no result event"
            elif res.get("subtype") != "success" or res.get("is_error"):
                reason = f"result {res.get('subtype')}"
            elif not SORRY_RE.search(strip_comments(text)):
                reason = "no sorry in work file"
            elif not GIVEUP_RE.search(res.get("result") or ""):
                reason = "no GIVEUP in final text"
            elif checks >= n_min:
                reason = f"checks {checks} >= {n_min}"
            elif info["rounds"] >= args.enforce_rounds:
                reason = "rounds exhausted"
            elif turns_left <= 2:
                reason = "turns exhausted"
            elif budget_left <= 0:
                reason = "budget exhausted"
            else:
                reason = None
            info["decisions"].append({"checks": checks, "num_turns": res.get("num_turns"),
                                      "total_cost_usd": res.get("total_cost_usd"),
                                      "session_id": res.get("session_id"), "stop": reason})
            if reason:
                info["reason"] = reason
                break
            info["rounds"] += 1
            text = msg.replace("{checks}", str(checks)).replace("{min}", str(n_min))
            # --max-turns counts this invocation only; --max-budget-usd counts the whole resumed session.
            cmd = base + ["--resume", res["session_id"], "--max-turns", str(turns_left),
                          "--max-budget-usd", str(args.max_budget_usd), text]
    finally:
        subprocess.run(["docker", "kill", name], capture_output=True)
        RUNNING.discard(name)
    (rd / "enforce.json").write_text(json.dumps(info, indent=1) + "\n")
    return rc, timed_out, time.monotonic() - t0, info


RETRIES = 3


def run_one(job: dict, args, batch: str, out: pathlib.Path) -> dict | None:
    """Retry a run that produced no tokens because of an API/proxy error; keep failed attempts aside."""
    rd: pathlib.Path = job["dir"]
    for attempt in range(1, RETRIES + 1):
        r = _run_once(job, args, batch, out)
        if r is None or r["terminal_reason"] != "api_error" or (r["output_tokens"] or 0) > 0 or attempt == RETRIES:
            return r
        aside = out / f"{rd.name}.apierr{attempt}"
        if aside.exists():
            shutil.rmtree(aside)
        rd.rename(aside)
        print(f"  retry {attempt}/{RETRIES - 1}: {rd.name} api_error with 0 tokens", flush=True)
        time.sleep(30)
    return None


def _run_once(job: dict, args, batch: str, out: pathlib.Path) -> dict | None:
    rd: pathlib.Path = job["dir"]
    if (rd / "result.json").exists():
        return None
    if rd.exists():   # interrupted earlier run: start clean
        assert rd.resolve().parent == out.resolve(), rd
        shutil.rmtree(rd)
    work = rd / "work"
    work.mkdir(parents=True)
    src: pathlib.Path = job["src"]
    fname = src.name
    swe = job["bench"] == "swe"
    task = json.loads(src.read_text()) if swe else None
    if swe:   # the repo is in the image; task.json stays on the host
        pass
    elif job["bench"] == "verus":   # stub + description.md; task.json stays on the host
        for f in src.parent.iterdir():
            if f.is_file() and f.name != "task.json":
                shutil.copy(f, work / f.name)
    else:
        shutil.copy(src, work / fname)

    cond_text = job["cond_file"].read_text() if job["cond_file"].exists() else ""
    cond_path = None
    if cond_text.strip():
        cond_path = rd / "condition.md"
        cond_path.write_text(cond_text)
    if swe:
        rule = ""
        if task["framing"] == "debug":
            rule = "\n- These tests currently fail and must pass:" + "".join(
                f"\n  - `{t}`" for t in task["FAIL_TO_PASS"]) + "\n  The tests exist in the repo; run them."
        prompt = (PROMPT_SWE.read_text().replace("{FAILING_TESTS_RULE}", rule)
                  .replace("{ISSUE}", task["problem_statement"].strip()).strip())
    else:
        prompt = (PROMPT_VERUS if job["bench"] == "verus" else PROMPT).read_text().replace("{FILE}", fname).strip()
    (rd / "prompt.txt").write_text(prompt + "\n")

    name = container_name(batch)
    prefix = docker_args(name, args, None if swe else work, cond_path, task["image"] if swe else None)
    agent = ["claude", "-p", "--bare", "--model", MODEL, "--effort", job["effort"],
             "--output-format", "stream-json", "--verbose",
             "--dangerously-skip-permissions", "--no-session-persistence", "--strict-mcp-config",
             "--disallowedTools", "WebFetch,WebSearch"]
    enforce = args.enforce_min_checks > 0
    if enforce:   # --resume needs the session on disk
        agent.remove("--no-session-persistence")
    if cond_path:
        agent += ["--append-system-prompt-file", COND_MOUNT]
    base = agent[:]   # resumed invocations reuse these options
    # Keep a single-value option last: --disallowedTools is variadic and would consume the prompt.
    agent += ["--max-turns", str(args.max_turns), "--max-budget-usd", str(args.max_budget_usd), prompt]
    (rd / "cmd.json").write_text(json.dumps({"docker": prefix, "agent": agent}, indent=1) + "\n")

    started = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    checks, enforce_info = None, None
    if args.dry_run and swe:
        checks = dry_checks_swe(prefix, name, rd, task)
        fake_stream(rd / "agent.jsonl", fname)
        (rd / "agent.stderr").write_text("")
        (rd / "model_patch.diff").write_text("")
        rc, timed_out, secs = 0, False, 0.0
    elif args.dry_run:
        checks = dry_checks(prefix, name, rd, fname, "verus" if job["bench"] == "verus" else "lean")
        fake_stream(rd / "agent.jsonl", fname)
        (rd / "agent.stderr").write_text("")
        rc, timed_out, secs = 0, False, 0.0
    elif swe:
        rc, timed_out, secs = run_swe(prefix, agent, name, rd, task, args)
    elif enforce:
        rc, timed_out, secs, enforce_info = run_enforced(prefix, base, prompt, name, rd, work / fname, args)
    else:
        rc, timed_out, secs = run_container(prefix + agent, name, rd / "agent.jsonl",
                                            rd / "agent.stderr", args.timeout_min * 60)

    s = parse_stream(rd / "agent.jsonl")
    res = s["result"]
    sub = rd / "model_patch.diff" if swe else work / fname
    v = run_verify(src, sub)
    (rd / "verify.json").write_text(json.dumps(v) + "\n")

    if res is not None:
        usage, usage_source = res.get("usage") or {}, "result"
        num_turns = res.get("num_turns")
    else:   # killed before the result event: sum the per-message usage
        usage, usage_source = {}, "assistant_sum"
        for u in s["usage_by_msg"].values():
            for k in ("input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"):
                usage[k] = usage.get(k, 0) + (u.get(k) or 0)
        num_turns = len(s["usage_by_msg"])

    orig = src.read_text()
    sub_text = sub.read_text(errors="replace") if sub.exists() else ""
    touched_tests = None
    if swe:   # "proof" = the patch
        body = sub_text
        touched_tests = [f for f in patch_files(sub_text) if TEST_PATH_RE.search(f)]
        changed = bool(touched_tests)
    elif job["bench"] == "verus":   # "proof" = the three editable regions
        try:
            body = "".join(verify_verus.split(sub_text)[1].values()).strip()
            changed = v.get("stage") == "spec"
        except ValueError:
            body, changed = None, True
    else:
        body, changed = proof_text(orig, sub_text, src.stem) if sub_text else (None, True)
    search_uses = sum(1 for c in s["bash_cmds"] if SEARCH_RE.search(c))
    search_uses += sum(1 for t in s["edit_texts"] if SEARCH_RE.search(strip_comments(t)))
    final_text = (res or {}).get("result") or ""

    r = {
        "problem": src.parent.name if swe else src.stem, "bench": job["bench"], "condition": job["condition"],
        "effort": job["effort"], "model": MODEL, "batch": batch, "dry_run": bool(args.dry_run),
        "outcome": classify(v, timed_out, res, args.max_turns),
        "verify_pass": bool(v.get("pass")), "verify_stage": v.get("stage"),
        "verify_detail": str(v.get("detail", ""))[-1500:],
        "num_turns": num_turns,
        "input_tokens": usage.get("input_tokens"), "output_tokens": usage.get("output_tokens"),
        "thinking_tokens": ((usage.get("output_tokens_details") or {}).get("thinking_tokens")),
        "cache_read_tokens": usage.get("cache_read_input_tokens"),
        "cache_creation_tokens": usage.get("cache_creation_input_tokens"),
        "usage_source": usage_source,
        "total_cost_usd": (res or {}).get("total_cost_usd"),
        "duration_s": round(secs, 1), "agent_duration_ms": (res or {}).get("duration_ms"),
        "lean_compile_count": sum(1 for c in s["bash_cmds"]
                                  if {"verus": VERUS_RE, "swe": TEST_RE}.get(job["bench"], LEAN_RE).search(c)),
        "search_tactic_uses": search_uses,
        "search_tactic_in_final": bool(SEARCH_RE.search(strip_comments(sub_text))),
        "tool_calls": s["tool_counts"],
        "proof_chars": len(body) if body is not None else None,
        "proof_lines": sum(1 for x in body.splitlines() if x.strip()) if body is not None else None,
        "statement_prefix_changed": changed,
        "stop_reason": "timeout" if timed_out else (res or {}).get("stop_reason"),
        "result_subtype": (res or {}).get("subtype"),
        "terminal_reason": (res or {}).get("terminal_reason"),
        "is_error": (res or {}).get("is_error"),
        "api_error_status": (res or {}).get("api_error_status"),
        "permission_denials": len((res or {}).get("permission_denials") or []),
        "agent_said_give_up": "give up" in final_text.lower(),
        "final_text": final_text[-2000:],
        "timed_out": timed_out, "docker_rc": rc,
        "limits": {"max_turns": args.max_turns, "max_budget_usd": args.max_budget_usd,
                   "timeout_min": args.timeout_min},
        "network": args.network, "proxy": bool(args.proxy),
        "claude_version": (s["init"] or {}).get("claude_code_version"),
        "model_usage": (res or {}).get("modelUsage"),
        "started_at": started,
    }
    if swe:
        r["framing"] = task["framing"]
        r["patch_files"] = patch_files(sub_text)
        r["touched_test_files"] = touched_tests
        gs = rd / "git_status.txt"
        r["untracked_files"] = [x[3:] for x in gs.read_text().splitlines() if x.startswith("??")] \
            if gs.exists() else []
    if checks is not None:
        r["dry_checks"] = checks
    if enforce_info is not None:
        r["enforce_rounds"] = enforce_info["rounds"]
        r["enforce_checks_at_rounds"] = enforce_info["checks_at_rounds"]
    (rd / "result.json").write_text(json.dumps(r, indent=1) + "\n")
    return r


# ---------------------------------------------------------------- main

def read_list(spec: str) -> list[str]:
    p = pathlib.Path(spec)
    if p.is_file():
        items = [line.split("#")[0].strip() for line in p.read_text().splitlines()]
    else:
        items = [x.strip() for x in spec.split(",")]
    return [x.removesuffix(".lean") for x in items if x]


def main() -> int:
    global MODEL
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bench", required=True, choices=sorted(BENCH_DIRS))
    ap.add_argument("--problems", required=True, help="file with one name per line, or comma list")
    ap.add_argument("--condition", required=True, help="comma list; maps to conditions/NAME.md")
    ap.add_argument("--model", default=MODEL, help="model id, e.g. claude-haiku-5-5")
    ap.add_argument("--effort", required=True, help="comma list of " + "|".join(EFFORTS))
    ap.add_argument("--max-turns", type=int, default=60)
    ap.add_argument("--max-budget-usd", type=float, default=3.0)
    ap.add_argument("--timeout-min", type=float, default=30.0)
    ap.add_argument("--parallel", type=int, default=1)
    ap.add_argument("--out", required=True, help="runs/<batch_name>/")
    ap.add_argument("--network", default="cotml-egress")
    ap.add_argument("--proxy", default="http://cotml-proxy:8888", help="sets HTTPS_PROXY and HTTP_PROXY in the agent container")
    ap.add_argument("--dry-run", action="store_true", help="do everything except the claude call")
    ap.add_argument("--enforce-min-checks", type=int, default=0,
                    help="resume a run that gives up after fewer lean compiles than N (0 = off)")
    ap.add_argument("--enforce-rounds", type=int, default=2, help="maximum resumes per run")
    ap.add_argument("--enforce-message", default=str(ROOT / "harness/enforce_giveup.md"),
                    help="resume message file; {checks} and {min} are filled in")
    args = ap.parse_args()
    MODEL = args.model
    if args.enforce_min_checks > 0 and not pathlib.Path(args.enforce_message).is_file():
        ap.error(f"--enforce-message: {args.enforce_message} not found")

    out = pathlib.Path(args.out).resolve()
    if out.parent != RUNS.resolve():
        ap.error(f"--out must be a directory directly under {RUNS}")
    batch = out.name

    problems = read_list(args.problems)
    conditions = read_list(args.condition)
    efforts = read_list(args.effort)
    for e in efforts:
        if e not in EFFORTS:
            ap.error(f"bad effort: {e}")
    for c in conditions:
        f = COND_DIR / f"{c}.md"
        # Guard: a missing file would silently run a non-bare condition as bare.
        if c != "bare" and not (f.exists() and f.read_text().strip()):
            ap.error(f"condition {c}: {f} is missing or empty")
    srcs = {}
    for p in problems:
        if args.bench == "swe":
            meta = BENCH_DIRS["swe"] / p / "task.json"
            if not meta.is_file():
                ap.error(f"problem not found: {meta}")
            srcs[p] = meta
            continue
        if args.bench == "verus":
            meta = BENCH_DIRS["verus"] / p / "task.json"
            if not meta.is_file():
                ap.error(f"problem not found: {meta}")
            srcs[p] = meta.parent / json.loads(meta.read_text())["entry"]
            continue
        src = BENCH_DIRS[args.bench] / f"{p}.lean"
        if not src.is_file():
            ap.error(f"problem not found: {src}")
        if not SORRY_RE.search(src.read_text()):
            ap.error(f"no sorry in {src}")
        srcs[p] = src
    if not args.dry_run and not os.environ.get("ANTHROPIC_API_KEY"):
        ap.error("ANTHROPIC_API_KEY is not set (--bare reads only this)")
    if args.bench == "swe":
        if args.enforce_min_checks > 0:
            ap.error("--enforce-min-checks is not supported for bench swe")
        if not CLAUDE_BIN.is_file():
            ap.error(f"{CLAUDE_BIN} not found")
        images = [json.loads(m.read_text())["image"] for m in srcs.values()]
    else:
        images = [VERUS_IMAGE if args.bench == "verus" else IMAGE]
    for image in images:
        if subprocess.run(["docker", "image", "inspect", image], capture_output=True).returncode != 0:
            ap.error(f"docker image {image} not found")

    if args.bench == "swe":   # no Lean in the task images; --dry-run checks git state and network
        hits = []
    else:
        hits = isolation_check(args)
    if hits:
        print("isolation check FAILED; .lean files visible in container:", *hits, sep="\n  ", file=sys.stderr)
        return 2
    print("isolation check: " + ("skipped (swe)" if args.bench == "swe" else "ok (no .lean files outside /work)"),
          flush=True)

    out.mkdir(parents=True, exist_ok=True)
    with open(out / "invocations.jsonl", "a") as f:
        f.write(json.dumps({"time": datetime.datetime.now().isoformat(timespec="seconds"),
                            "argv": sys.argv[1:], "model": MODEL}) + "\n")

    jobs = [{"bench": args.bench, "src": srcs[p], "condition": c, "effort": e,
             "cond_file": COND_DIR / f"{c}.md", "dir": out / f"{p}__{c}__{e}"}
            for p in problems for c in conditions for e in efforts]
    todo = [j for j in jobs if not (j["dir"] / "result.json").exists()]
    print(f"{len(jobs)} runs, {len(jobs) - len(todo)} done, {len(todo)} to run, parallel {args.parallel}", flush=True)

    # Threads suffice: each worker waits on docker subprocesses.
    ex = cf.ThreadPoolExecutor(max_workers=max(1, args.parallel))
    futs = {ex.submit(run_one, j, args, batch, out): j for j in todo}
    done = 0
    try:
        for fut in cf.as_completed(futs):
            j = futs[fut]
            done += 1
            tag = j["dir"].name
            try:
                r = fut.result()
            except Exception as e:   # keep the batch going; the run stays without result.json
                print(f"[{done}/{len(todo)}] {tag}: EXCEPTION {e!r}", flush=True)
                continue
            if r is None:
                continue
            with open(out / "results.jsonl", "a") as f:
                f.write(json.dumps(r) + "\n")
            print(f"[{done}/{len(todo)}] {tag}: {r['outcome']} ({r['verify_stage']}) "
                  f"turns={r['num_turns']} out_tok={r['output_tokens']} cost={r['total_cost_usd']} "
                  f"{r['duration_s']}s", flush=True)
    except KeyboardInterrupt:
        print("interrupted: killing containers", file=sys.stderr)
        ex.shutdown(wait=False, cancel_futures=True)
        for name in list(RUNNING):
            subprocess.run(["docker", "kill", name], capture_output=True)
        return 130
    ex.shutdown()
    return 0


if __name__ == "__main__":
    sys.exit(main())
