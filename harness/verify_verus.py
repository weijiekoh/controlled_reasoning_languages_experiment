"""Verify a Verus submission for an AlgoVeri task.

Usage: python3 -I verify_verus.py <task_dir> <submission.rs>
Prints one JSON object: {"pass": bool, "stage": str, "detail": str, "seconds": float}.

<task_dir> holds task.json and the original stub (task.json "entry"). The stub has
three editable regions, delimited by marker comments:
  // <helpers> ... // </helpers>   helper specs and exec helpers
  // <proofs>  ... // </proofs>    lemmas
  // <code>    ... // </code>      body of the function under spec
All other text (preamble, spec header, main) is fixed.

Stages, in order:
  missing      submission file absent
  structure    markers missing, duplicated or out of order; region does not lex;
               unbalanced delimiters; region ends in a dangling attribute
  spec         fixed text differs from the stub (tokens, comments and whitespace ignored)
  trust        trust escape in an editable region: assume/admit, unsafe, extern,
               unlisted attribute (external_body, external, truncate, cfg, ...), glob
               import outside vstd, item or import name that shadows a fixed name
  termination  loop without `decreases`, recursive exec helper without `decreases`
  verify       verus reports errors or does not finish (spliced file: stub fixed
               text + submitted regions)
  recursion    the function under spec is referenced from submitted code (its header
               has no `decreases`, so Verus 0.2025.01.13 would not check termination)
  verify_error infrastructure failure
  ok
Every verus process runs in the cotml-verus image with no network.
"""
import json
import pathlib
import re
import subprocess
import sys
import tempfile
import time
import uuid

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMAGE = "cotml-verus"
VERUS_TIMEOUT = 300
REGIONS = ("helpers", "proofs", "code")
PROBE_SUFFIX = "__cotml_probe"

# ---------------------------------------------------------------- policy

# Attributes allowed in editable regions (outer or inner). Path = tokens before '(' or '='.
# Source: rust_verify/src/attributes.rs at verus da1c777; only attributes that do not add trust.
SAFE_ATTRS = {
    "trigger", "auto", "all_triggers", "derive", "allow", "warn", "inline", "must_use", "doc",
    "verusfmt::skip", "via_fn", "is_variant",
    "verifier::loop_isolation", "verifier::spinoff_prover", "verifier::rlimit",
    "verifier::nonlinear", "verifier::integer_ring", "verifier::bit_vector",
    "verifier::opaque", "verifier::inline", "verifier::memoize",
    "verifier::accept_recursive_types", "verifier::reject_recursive_types",
    "verifier::reject_recursive_types_in_ground_variants", "verifier::type_invariant",
    "verifier::ext_equal", "verifier::auto_ext_equal", "verifier::publish",
    "verifier::opaque_outside_module", "verifier::prophetic", "verifier::custom_req_err",
    "verifier::custom_err", "verifier::decreases_by", "verifier::recommends_by",
}
# Known trust escapes, for clear messages. Anything not in SAFE_ATTRS is rejected anyway.
TRUST_ATTRS = {
    "verifier::external_body": "body not verified",
    "verifier::external": "item not verified",
    "verifier::external_fn_specification": "trusted spec for external function",
    "verifier::external_type_specification": "trusted spec for external type",
    "verifier::external_trait_specification": "trusted spec for external trait",
    "verifier::truncate": "unchecked truncating cast",
    "verifier::exec_allows_no_decreases_clause": "disables exec termination check",
    "verifier::verify": "verification override",
    "verifier::when_used_as_spec": "exec/spec substitution",
    "verifier::broadcast_forall": "internal broadcast attribute",
    "verifier::size_of": "global size assumption",
    "verifier": "old-style #[verifier(...)] attribute",
    "cfg": "conditional compilation can remove items",
    "cfg_attr": "conditional attribute",
    "path": "external module file",
}
# Identifiers banned anywhere in editable regions (substring match for assume/admit:
# covers assume, admit, assume_specification, Tracked::assume_new, ...).
BANNED_SUBSTR = ("assume", "admit")
BANNED_IDENTS = {
    "unsafe": "unsafe code", "extern": "foreign item", "global": "global layout assumption",
    "macro_rules": "macro can shadow macros used by the spec",
    "include": "file inclusion", "include_str": "file inclusion", "include_bytes": "file inclusion",
    "asm": "inline assembly", "global_asm": "inline assembly", "naked_asm": "inline assembly",
    "external_body": "trust escape", "external_fn_specification": "trust escape",
    "external_type_specification": "trust escape", "external_trait_specification": "trust escape",
    "exec_allows_no_decreases_clause": "trust escape",
}
KEYWORDS = set("""as break const continue crate else enum extern false fn for if impl in let loop match
mod move mut pub ref return self Self static struct super trait true type unsafe use where while async
await dyn abstract become box do final macro override priv typeof unsized virtual yield try union
spec proof exec open closed tracked ghost requires ensures recommends decreases invariant
invariant_except_break ensures forall exists choose broadcast uninterp via when opens_invariants
no_unwind returns default_ensures""".split())
ITEM_KW = {"fn", "struct", "enum", "union", "trait", "type", "const", "static", "mod"}

# ---------------------------------------------------------------- lexer


class LexError(Exception):
    pass


IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
NUM_RE = re.compile(r"[0-9][0-9A-Za-z_]*")


def lex(src: str) -> list[str]:
    """Rust token texts with comments and whitespace removed. Punctuation is one char per token."""
    toks, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c.isspace():
            i += 1
        elif src.startswith("//", i):
            j = src.find("\n", i)
            i = n if j < 0 else j + 1
        elif src.startswith("/*", i):
            depth, i = 1, i + 2
            while depth:
                if i >= n:
                    raise LexError("unterminated block comment")
                if src.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif src.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif (m := re.compile(r'(b?r)(#*)"').match(src, i)):
            close = '"' + m.group(2)
            j = src.find(close, m.end())
            if j < 0:
                raise LexError("unterminated raw string")
            toks.append(src[i:j + len(close)])
            i = j + len(close)
        elif c == '"' or src.startswith('b"', i):
            j = i + (2 if c == "b" else 1)
            while True:
                if j >= n:
                    raise LexError("unterminated string")
                if src[j] == "\\":
                    j += 2
                elif src[j] == '"':
                    break
                else:
                    j += 1
            toks.append(src[i:j + 1])
            i = j + 1
        elif c == "'" or src.startswith("b'", i):
            j = i + (2 if c == "b" else 1)
            if j < n and src[j] == "\\":
                k = src.find("'", j + 2)
                if k < 0:
                    raise LexError("unterminated char literal")
                toks.append(src[i:k + 1])
                i = k + 1
            elif j + 1 < n and src[j + 1] == "'":
                toks.append(src[i:j + 2])
                i = j + 2
            elif (m := IDENT_RE.match(src, j)):     # lifetime or label
                toks.append("'" + m.group())
                i = m.end()
            else:
                raise LexError("bad quote")
        elif (m := re.compile(r"r#[A-Za-z_][A-Za-z0-9_]*").match(src, i)):
            toks.append(m.group()[2:])
            i = m.end()
        elif (m := IDENT_RE.match(src, i)) or (m := NUM_RE.match(src, i)):
            toks.append(m.group())
            i = m.end()
        else:
            toks.append(c)
            i += 1
    return toks


def is_ident(t: str) -> bool:
    return bool(IDENT_RE.fullmatch(t))


# ---------------------------------------------------------------- regions

def marker_re(name: str, close: bool) -> re.Pattern:
    return re.compile(r"//[ \t]*<" + ("/" if close else "") + name + r">[^\n]*(\n|$)")


def split(text: str) -> tuple[list[str], dict[str, str]]:
    """Return fixed segments [F0..F3] and editable regions {helpers, proofs, code}.

    F0 ends after the <helpers> marker line; each region runs from after its open
    marker line to the start of its close marker. Raises ValueError on bad markers."""
    pos = []
    for name in REGIONS:
        for close in (False, True):
            ms = list(marker_re(name, close).finditer(text))
            tag = f"<{'/' if close else ''}{name}>"
            if len(ms) != 1:
                raise ValueError(f"marker {tag} found {len(ms)} times (need exactly 1)")
            pos.append(ms[0])
    if any(a.start() >= b.start() for a, b in zip(pos, pos[1:])):
        raise ValueError("markers out of order")
    fixed, regions = [], {}
    prev = 0
    for k, name in enumerate(REGIONS):
        o, c = pos[2 * k], pos[2 * k + 1]
        fixed.append(text[prev:o.end()])
        regions[name] = text[o.end():c.start()]
        prev = c.start()
    fixed.append(text[prev:])
    return fixed, regions


def main_fn_name(spec_segment: str) -> str:
    toks = lex(spec_segment)
    names = [toks[i + 1] for i, t in enumerate(toks[:-1]) if t == "fn" and is_ident(toks[i + 1])]
    if len(names) < 1:
        raise ValueError("no fn in spec segment")
    return names[-1]


# ---------------------------------------------------------------- static checks

def match_close(toks: list[str], i: int) -> int:
    """Index of the delimiter closing toks[i]."""
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = []
    for j in range(i, len(toks)):
        t = toks[j]
        if t in pairs:
            stack.append(pairs[t])
        elif t in (")", "]", "}"):
            if not stack or stack.pop() != t:
                return -1
            if not stack:
                return j
    return -1


def check_structure(name: str, toks: list[str]) -> str | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = []
    for t in toks:
        if t in pairs:
            stack.append(pairs[t])
        elif t in (")", "]", "}"):
            if not stack or stack.pop() != t:
                return f"{name}: unbalanced '{t}' (regions must not close enclosing scopes)"
    if stack:
        return f"{name}: unclosed delimiter"
    if name == "code":
        if not toks or toks[0] != "{" or match_close(toks, 0) != len(toks) - 1:
            return "code: region must be exactly one block `{ ... }` (the function body)"
    elif toks and toks[-1] not in ("}", ";"):
        return f"{name}: region must be empty or end with '}}' or ';' (got '{toks[-1]}')"
    return None


def attributes(toks: list[str]):
    """Yield (path, inner, text) for each #[...] / #![...]."""
    for i, t in enumerate(toks):
        if t != "#":
            continue
        j = i + 1
        inner = j < len(toks) and toks[j] == "!"
        if inner:
            j += 1
        if j >= len(toks) or toks[j] != "[":
            continue
        k = match_close(toks, j)
        body = toks[j + 1:k] if k > 0 else toks[j + 1:]
        path = body[:1]   # ident(::ident)*
        while len(body) >= len(path) + 3 and body[len(path):len(path) + 2] == [":", ":"]:
            path += body[len(path):len(path) + 3]
        yield "".join(path), inner, "#" + ("!" if inner else "") + "[" + "".join(body) + "]"


def defined_names(toks: list[str]) -> set[str]:
    """Item names defined in toks and leaf names brought in by `use`."""
    out = set()
    for i, t in enumerate(toks[:-1]):
        if t in ITEM_KW and is_ident(toks[i + 1]) and toks[i + 1] not in KEYWORDS:
            out.add(toks[i + 1])
    i = 0
    while i < len(toks):
        if toks[i] == "use":
            j = i
            while j < len(toks) and toks[j] != ";":
                j += 1
            seg = toks[i + 1:j]
            for k, t in enumerate(seg):
                if not is_ident(t) or t in ("self", "super", "crate", "as"):
                    continue
                nxt = seg[k + 1] if k + 1 < len(seg) else None
                prev = seg[k - 1] if k > 0 else None
                if nxt == ":" or nxt == "as":
                    continue          # path segment or renamed import
                if prev == "as" or nxt in (None, ",", "}"):
                    out.add(t)
            i = j
        i += 1
    return out


def glob_imports(toks: list[str]) -> list[str]:
    out, i = [], 0
    while i < len(toks):
        if toks[i] == "use":
            j = i
            while j < len(toks) and toks[j] != ";":
                j += 1
            if "*" in toks[i:j]:
                out.append("".join(toks[i + 1:j]))
            i = j
        i += 1
    return out


def check_trust(regions_toks: dict[str, list[str]], fixed_idents: set[str]) -> str | None:
    for name, toks in regions_toks.items():
        for t in toks:
            if is_ident(t):
                low = t.lower()
                for s in BANNED_SUBSTR:
                    if s in low:
                        return f"{name}: banned identifier `{t}` ({s})"
                if t in BANNED_IDENTS:
                    return f"{name}: banned identifier `{t}` ({BANNED_IDENTS[t]})"
        for path, inner, text in attributes(toks):
            if path in SAFE_ATTRS:
                continue
            why = TRUST_ATTRS.get(path, "attribute not in allowlist")
            if path.startswith("verus::"):
                why = "internal verus attribute"
            return f"{name}: attribute {text} rejected: {why}"
        for g in glob_imports(toks):
            if not (g.startswith("vstd::") or g in ("super::*", "crate::*")):
                return f"{name}: glob import `use {g}` (only vstd::..., super::*, crate::* allowed)"
        clash = sorted(defined_names(toks) & fixed_idents)
        if clash:
            return (f"{name}: defines or imports {', '.join('`'+c+'`' for c in clash)}, which the fixed "
                    "text uses; rename it")
    return None


def header_end(toks: list[str], i: int) -> int:
    """Index of the first '{' or ';' at paren/bracket depth 0 at or after i."""
    depth = 0
    for j in range(i, len(toks)):
        t = toks[j]
        if t in ("(", "["):
            depth += 1
        elif t in (")", "]"):
            depth -= 1
        elif depth == 0 and t in ("{", ";"):
            return j
    return -1


def exec_fns(toks: list[str]):
    """Yield (name, header_tokens, body_tokens) for exec fns with bodies."""
    for i, t in enumerate(toks[:-1]):
        if t != "fn" or not is_ident(toks[i + 1]):
            continue
        k, mods = i - 1, set()
        while k >= 0 and toks[k] not in (";", "{", "}", "]"):
            mods.add(toks[k])
            k -= 1
        if mods & {"spec", "proof"}:
            continue
        h = header_end(toks, i + 2)
        if h < 0 or toks[h] == ";":
            continue
        e = match_close(toks, h)
        yield toks[i + 1], toks[i + 2:h], toks[h:e + 1]


def check_termination(regions_toks: dict[str, list[str]]) -> str | None:
    for name, toks in regions_toks.items():
        for i, t in enumerate(toks):
            if t in ("while", "loop"):
                h = header_end(toks, i + 1)
                if h < 0 or toks[h] != "{" or "decreases" not in toks[i + 1:h]:
                    return f"{name}: `{t}` without a `decreases` clause"
    fns = {}
    for name, toks in regions_toks.items():
        for fname, head, body in exec_fns(toks):
            prev = fns.get(fname)
            fns[fname] = (prev[0] and "decreases" in head if prev else "decreases" in head,
                          (prev[1] if prev else []) + body)
    # Any mention counts as a call (covers `h(..)`, `Self::h(..)`, `x.h(..)`, `let f = h;`).
    calls = {f: {t for t in b if t in fns} for f, (_, b) in fns.items()}
    for f, (has_dec, _) in fns.items():   # f is recursive if f reaches f
        seen, todo = set(), list(calls[f])
        while todo:
            g = todo.pop()
            if g in seen:
                continue
            seen.add(g)
            todo += calls.get(g, ())
        if f in seen and not has_dec:
            return f"exec fn `{f}` is (possibly) recursive and has no `decreases` clause"
    return None


# ---------------------------------------------------------------- verus

def run_verus(tmp: str, timeout: int) -> tuple[int, str, float]:
    """Verify Main.rs and type-check Probe.rs in one no-network container."""
    name = "cotml-verify-" + uuid.uuid4().hex[:10]
    script = (f"cd /tmp && timeout {timeout} verus /v/Main.rs 2>&1; echo \"@@main_rc $?\"; "
              "timeout 120 verus --no-verify /v/Probe.rs 2>&1; echo \"@@probe_rc $?\"")
    args = ["docker", "run", "--rm", "--name", name, "--network", "none", "--user", "1000:1000",
            "--memory", "8g", "--cpus", "4", "--read-only", "--tmpfs", "/tmp:exec,mode=1777",
            "-e", "HOME=/tmp", "-v", f"{tmp}:/v:ro", IMAGE, "bash", "-c", script]
    t0 = time.monotonic()
    try:
        r = subprocess.run(args, capture_output=True, text=True, timeout=timeout + 200)
    except subprocess.TimeoutExpired:
        subprocess.run(["docker", "kill", name], capture_output=True)
        return 124, "container timeout", time.monotonic() - t0
    return r.returncode, r.stdout + r.stderr, time.monotonic() - t0


RESULT_RE = re.compile(r"verification results:: (\d+) verified, (\d+) errors")


def verify(task_dir: pathlib.Path, submission: pathlib.Path, timeout: int = VERUS_TIMEOUT) -> dict:
    t0 = time.monotonic()

    def out(ok, stage, detail=""):
        return {"pass": ok, "stage": stage, "detail": detail[-1500:], "seconds": round(time.monotonic() - t0, 1)}

    meta = json.loads((task_dir / "task.json").read_text())
    orig = (task_dir / meta["entry"]).read_text()
    if not submission.is_file():
        return out(False, "missing", f"{submission.name} not found")
    sub = submission.read_text(errors="replace")

    o_fixed, _ = split(orig)
    try:
        s_fixed, s_reg = split(sub)
        r_toks = {k: lex(v) for k, v in s_reg.items()}
        s_fixed_toks = [lex(f) for f in s_fixed]
    except (ValueError, LexError) as e:
        return out(False, "structure", str(e))
    for k, toks in r_toks.items():
        err = check_structure(k, toks)
        if err:
            return out(False, "structure", err)

    o_fixed_toks = [lex(f) for f in o_fixed]
    for k, (a, b) in enumerate(zip(o_fixed_toks, s_fixed_toks)):
        if a != b:
            j = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
            return out(False, "spec", f"fixed segment {k} changed near: "
                       f"expected `{' '.join(a[max(0, j-8):j+8])}` got `{' '.join(b[max(0, j-8):j+8])}`")

    # Splice: original fixed text + submitted regions. Re-lex the whole file to catch
    # boundary effects (e.g. a region that changes how the next fixed segment lexes).
    parts = [o_fixed[0], s_reg["helpers"], o_fixed[1], s_reg["proofs"], o_fixed[2], s_reg["code"], o_fixed[3]]
    spliced = "".join(parts)
    expect = (o_fixed_toks[0] + r_toks["helpers"] + o_fixed_toks[1] + r_toks["proofs"]
              + o_fixed_toks[2] + r_toks["code"] + o_fixed_toks[3])
    try:
        if lex(spliced) != expect:
            return out(False, "structure", "regions change how the fixed text lexes")
    except LexError as e:
        return out(False, "structure", str(e))

    fixed_idents = {t for f in o_fixed_toks for t in f if is_ident(t) and t not in KEYWORDS}
    err = check_trust(r_toks, fixed_idents)
    if err:
        return out(False, "trust", err)
    err = check_termination(r_toks)
    if err:
        return out(False, "termination", err)

    main_name = meta.get("main_fn") or main_fn_name(o_fixed[2])
    probe_fixed2, nsub = re.subn(r"\bfn\s+" + re.escape(main_name) + r"\b",
                                 "fn " + main_name + PROBE_SUFFIX, o_fixed[2], count=1)
    if nsub != 1:
        return out(False, "verify_error", f"cannot find fn {main_name} in spec segment")
    probe = "".join(parts[:4] + [probe_fixed2] + parts[5:])

    with tempfile.TemporaryDirectory(prefix="verus_", dir=ROOT / "runs") as tmp:
        pathlib.Path(tmp, "Main.rs").write_text(spliced)
        pathlib.Path(tmp, "Probe.rs").write_text(probe)
        pathlib.Path(tmp).chmod(0o755)
        for f in ("Main.rs", "Probe.rs"):
            pathlib.Path(tmp, f).chmod(0o644)
        rc, log, secs = run_verus(tmp, timeout)
    m_rc = re.search(r"@@main_rc (\d+)", log)
    if m_rc is None:
        return out(False, "verify_error", f"docker rc={rc}: {log}")
    main_log, probe_log = log[:m_rc.start()], log[m_rc.end():]
    res = RESULT_RE.findall(main_log)
    if m_rc.group(1) == "124":
        return out(False, "verify", f"verus timeout after {timeout}s")
    if m_rc.group(1) != "0" or not res or res[-1][1] != "0" or res[-1][0] == "0":
        return out(False, "verify", main_log)
    p_rc = re.search(r"@@probe_rc (\d+)", probe_log)
    if p_rc is None or p_rc.group(1) != "0":
        return out(False, "recursion",
                   f"submitted code refers to `{main_name}`; its header has no `decreases`, so "
                   f"recursion would not be checked for termination. Put recursion in a helper "
                   f"with `decreases`. Probe output: {probe_log[-600:]}")
    r = out(True, "ok", f"{res[-1][0]} verified, 0 errors")
    r["verus_seconds"] = round(secs, 1)
    return r


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    try:
        v = verify(pathlib.Path(sys.argv[1]).resolve(), pathlib.Path(sys.argv[2]).resolve())
    except Exception as e:   # report, do not crash the harness
        v = {"pass": False, "stage": "verify_error", "detail": f"{type(e).__name__}: {e}"}
    print(json.dumps(v))
