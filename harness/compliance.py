"""Measure how much of the agent's visible text follows a controlled reasoning language.

Usage: python3 harness/compliance.py runs/<batch> [runs/<batch> ...]
Per run: counts non-empty lines in assistant `text` blocks (code fences excluded)
and the share that start with a construct tag. Prints a per-condition table and
writes compliance.jsonl in each batch dir.

Thinking blocks are empty in the transcripts (display omitted), so this measures
visible text only.
"""
import collections
import json
import pathlib
import re
import sys

CONSTRUCTS = ["DEF", "GOAL", "SUBGOAL", "FACT", "HYP", "REFUTER", "CHECK", "RESULT", "INFER", "ASSUME", "RETRACT", "GROUND", "CASES", "INSTANCE", "GENERALIZE", "INVARIANT", "OBJECTION", "REPLY", "PLAN", "BRANCH", "BUDGET", "PRUNE", "STATE", "DROP", "DONE", "GIVEUP"]
TAG_RE = re.compile(r"^\s*[-*]?\s*(?:`)?(" + "|".join(CONSTRUCTS) + r")\b")


def text_lines(agent_jsonl: pathlib.Path) -> list[str]:
    lines: list[str] = []
    for raw in agent_jsonl.read_text(errors="replace").splitlines():
        try:
            d = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if d.get("type") != "assistant":
            continue
        for b in d["message"].get("content", []):
            if b.get("type") != "text":
                continue
            in_fence = False
            for line in b["text"].splitlines():
                if line.strip().startswith("```"):
                    in_fence = not in_fence
                    continue
                if not in_fence and line.strip():
                    lines.append(line)
    return lines


def score(run_dir: pathlib.Path) -> dict | None:
    rj, aj = run_dir / "result.json", run_dir / "agent.jsonl"
    if not (rj.exists() and aj.exists()):
        return None
    r = json.loads(rj.read_text())
    lines = text_lines(aj)
    tags = collections.Counter()
    for line in lines:
        m = TAG_RE.match(line)
        if m:
            tags[m.group(1)] += 1
    n_tag = sum(tags.values())
    return {
        "problem": r["problem"], "bench": r["bench"], "condition": r["condition"], "effort": r["effort"],
        "outcome": r["outcome"], "text_lines": len(lines), "tagged_lines": n_tag,
        "compliance": (n_tag / len(lines)) if lines else None, "tags": dict(tags),
    }


def main() -> None:
    rows_all = []
    for batch in map(pathlib.Path, sys.argv[1:]):
        rows = [s for d in sorted(batch.iterdir()) if d.is_dir() and (s := score(d))]
        (batch / "compliance.jsonl").write_text("".join(json.dumps(x) + "\n" for x in rows))
        rows_all += rows
    groups = collections.defaultdict(list)
    for x in rows_all:
        groups[(x["bench"], x["condition"], x["effort"])].append(x)
    print(f"{'bench':8} {'cond':7} {'effort':7} {'n':>3} {'lines/run':>9} {'compliance':>10}  top tags")
    for key, xs in sorted(groups.items()):
        scored = [x for x in xs if x["compliance"] is not None]
        mean_c = sum(x["compliance"] for x in scored) / len(scored) if scored else float("nan")
        mean_l = sum(x["text_lines"] for x in xs) / len(xs)
        tags = collections.Counter()
        for x in xs:
            tags.update(x["tags"])
        top = ", ".join(f"{k}:{v}" for k, v in tags.most_common(5))
        print(f"{key[0]:8} {key[1]:7} {key[2]:7} {len(xs):3} {mean_l:9.1f} {mean_c:10.1%}  {top}")


if __name__ == "__main__":
    main()
