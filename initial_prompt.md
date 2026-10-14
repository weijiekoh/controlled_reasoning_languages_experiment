# Can Controlled Reasoning Languages Improve Coding Agent Performance?

Can we come up with a controlled reasoning language that improves coding-agent
benchmark performance and/or reduces inference-token consumption, without
changing model weights?

## Constraints

I have 24 hours to complete an MVP for the Frontiers 2026 hackerthon
(https://www.paradigm.xyz/frontiers-2026). I want to produce, at the absolute
minimum:

- Coding benchmark results from a bare coding agent, without the controlled
  reasoning language definition inserted into the agent's context.
- A controlled reasoning language definition.
- Coding benchmark results from a coding agent that is instructed to use the
  controlled reasoning language definition.
- Before-and-after graphs of the Pareto frontier, where the x-axis is task
  completion, and the y-axis is token consumption.

I'd like at least some way to ensure that the agent can't game the benchmarks,
and that the benchmarks can be automatically verified. For example, if one
benchmark is to produce a correct Lean proof of a complex mathematical theorem,
this proof can be easily verified by Lean (as long as it is valid).

If there is more time, I'd like to iterate on the following, ranked by importance:

- Increase the complexity of the controlled reasoning language, and test
  whether doing so improves agent performance. e.g. introduce more language
  constructs and/or meta-rules.
- More benchmarks beyond the minimum set.

## Presentation

I will produce, by hand, a 5-minute presentation.

## Out-of-scope items

- Any fine-tuning. This is a context/prompt-engineering experiment.

## Open questions

- Which model should we use? Ideally, I'd run the model via my Claude
  subscription, since I don't want to pay per token via the Claude API.
  - And if we use Claude Code, is the `--bare` flag enough to prevent my
    personal user-context (e.g. `~/.claude/CLAUDE.md `) from being read? And
    does Claude have a per-account memory, and if so, is there an option to
    exclude it?
- Which benchmark should we use? How long does each evaluation cycle take?
    - e.g. are SWE-Bench Verified or BigCodeBench-Hard suitable?

## Miscellanous

Document your progress using Makrdown files  in `progress.md`. Include
timestamps. Use ASD-STE100 Simplified Technical English and be terse. Don't use
sentence structures or phases that are unpleasant for humans to read (see [22
Claude-prose Patterns](https://www.linkandth.ink/p/catalog-of-claude-cliches).

## Results

See `analysis/RESULTS.md` (write-up), `analysis/summary_all.png` (one figure), `progress.md` (timestamped log).

## Layout

- `harness/`: runner (`run.py`), verifiers (`verify.py` Lean, `verify_verus.py`, `verify_swe.py`), analysis (`analyze.py`, `compliance.py`, `summary_plot.py`), samplers, Docker images, egress proxy, tests.
- `conditions/`: the reasoning-language system prompts (`bare`, `cod`, `caveman`, `sponge`, `jellyfish`).
- `problems/`: problem lists per batch.
- `data/`: task files the runs used (`putnam_subst`, `fateh`, `fatex`, `combi`, `cam`, `verus`, `swe`), plus statement-compile logs (`*_check.tsv`).
- `runs/`: one directory per run with `result.json`, `verify.json`, `cmd.json`, `prompt.txt`, the agent transcript `agent.jsonl`, and the final `work/` files. SWE-bench evaluation logs are not committed.

## Setup

Not in the repository (see `.gitignore`):

- `.env` with `ANTHROPIC_API_KEY=...`. Load with `set -a; . ./.env; set +a`.
- Lean toolchain v4.33.1 via elan, then `cd lean_env && lake exe cache get` (Mathlib). Override the toolchain path with `COTML_TC`.
- `harness/safeverify`: `lake build` inside it.
- `harness/docker/claude`: the Claude Code binary (copy from `which claude`), then `harness/docker/build.sh`. Verus image: `harness/docker-verus/`. Egress proxy: `harness/egress/up.sh`.
- SWE-bench: `python3 -m venv data/.venv-swe && data/.venv-swe/bin/pip install swebench`, the dataset `SWE-bench/SWE-bench_Verified` as `data/swebench_verified.jsonl`, and the eval images (`harness/sample_swe.py --pull-mode ipv4`).
- Benchmark sources, cloned into `data/`: [PutnamBench](https://github.com/trishullab/PutnamBench) (Apache-2.0), [miniF2F-lean4](https://github.com/yangky11/miniF2F-lean4) (MIT), [FATE-H](https://github.com/frenzymath/FATE-H) and [FATE-X](https://github.com/frenzymath/FATE-X) (MIT), [CombiBench](https://github.com/MoonshotAI/CombiBench) (MIT), [CAM-Bench](https://github.com/optpku/CAM-Bench) (CC0), [AlgoVeri](https://github.com/haoyuzhao123/algoveri) (Apache-2.0), [SafeVerify](https://github.com/GasStationManager/SafeVerify) (Apache-2.0, ported copy in `harness/safeverify`). The derived task files in `data/` are redistributed under those licenses.
