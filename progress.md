# Progress

## 2026-10-13 16:37 PDT: Scope set

- Model: `claude-sonnet-5-5` through Claude Code `--bare` with an API key. Budget: US$300.
- Benchmarks: Lean 4 only. Candidates: miniF2F-test (244), PutnamBench (672).
- Metrics: pass rate (x-axis). Plot 1 y-axis: output tokens per run. Plot 2 y-axis: cost per run.
- Conditions: C0 bare, C1 Chain of Draft control, C2 controlled reasoning language. Sweep effort low, medium, high.
- Current phase: harness and baseline. Language design waits.

## 2026-10-13 16:45 PDT: Data cloned

- `data/PutnamBench` (commit a635813). Lean `v4.33.1`, Mathlib `v4.33.1`. 672 problems in `lean4/src`.
- `data/miniF2F-lean4` (commit 5746b7d). Lean `v4.24.0`. 244 test problems in `MiniF2F/Test`.
- PutnamBench answer problems have `abbrev ..._solution := sorry` with the answer in a comment. Plan: substitute the answer, so the agent proves only. This blocks trivial answers.

## 2026-10-13 17:10 PDT: Lean environment, sandbox, verifier

- `lean_env/`: Lean `v4.33.1`, Mathlib `v4.33.1`, build cache downloaded.
- All 244 miniF2F-test statements compile in `lean_env` (`data/minif2f_check.tsv`). About 6 CPU-seconds each.
- `harness/putnam_substitute.py` puts the reference answer into each PutnamBench `_solution` and marks it `noncomputable`. All 672 statements compile (`data/putnam_subst/`).
- SafeVerify ported to Lean `v4.33.1` (`harness/safeverify/`). `CollectAxioms.collect` is private in `v4.33.1`; replaced by the public `collectAxioms`. Mathlib dependency removed.
- Docker image `cotml-sandbox`: Debian, `claude` 2.1.296, ripgrep. Lean and Mathlib are bind-mounted read-only. One compile takes 3 s with no network.
- `harness/verify.py`: source ban list, import check, compile with no network, SafeVerify in a fresh container.
- Verifier tests on `aime_1983_p2` (`harness/tests/`): `sorry`, `axiom`, weaker statement, `native_decide` and `#eval` are all rejected. The correct proof is also rejected: SafeVerify stops while it replays `Target.olean`. Cause not yet known.
- Open gap: the agent container has network access for the API, so it can reach other sites through Bash. The verifier still rejects any invalid proof.

## 2026-10-13 17:20 PDT: Decisions

- Agent must not read Mathlib or Lean core source. Mount only compiled `.olean` directories in the agent container.
- Pilot limits proposed: $3 / 60 turns / 30 min, 10 miniF2F + 10 PutnamBench, medium effort. Set main-run cap from the pilot (about the 95th percentile of solved-run cost).
- Record each run outcome as solved, gave up, or hit cap.

## 2026-10-13 17:20 PDT: Subagents started

- Four subagents: verifier fix (Fable), runner + prompt (Opus), egress allowlist (Opus), pilot sampler (Opus).
- Search tactics (`exact?`, `apply?`, `rw?`, `simp?`, `hint`) stay allowed. The runner counts their use per run. Revisit after the pilot if use is frequent.

## 2026-10-13 17:23 PDT: Problem sets

- `harness/sample.py`: stratified, seeded, nested samples (Webster divisor method).
- `problems/pilot_*.txt` (10 each) and `problems/main_*.txt` (60 each), seed 20261013. Pilot sets are subsets of main sets.
- Every miniF2F and PutnamBench file has exactly one `sorry`. `putnam_1997_a1` has no Lean file upstream.

## 2026-10-13 17:27 PDT: Runner

- `harness/run.py`, `harness/prompt.md`, `harness/summarize.py`, `conditions/bare.md`, `conditions/cod.md`. Dry run passes (`runs/dryrun1/`). Resume and watchdog tested.
- `--bare` gives the agent only Bash, Edit, Read. Container has no `.lean` file outside `/work`.
- To confirm in the pilot: cap `subtype` names; whether `output_tokens` includes thinking tokens.

## 2026-10-13 17:29 PDT: Egress allowlist

- `harness/egress/`: Squid on internal network `cotml-egress`, proxy `cotml-proxy`. Only `CONNECT api.anthropic.com:443` allowed. 13/13 checks pass (`test.sh`).
- `run.py` defaults: `--network cotml-egress --proxy http://cotml-proxy:8888`, plus `NO_PROXY` and `CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1`.
- Residual risks: sandbox can reach host IPs (no host service listens on them); data can leave through the Anthropic API; sandboxes share the network.

## 2026-10-13 17:30 PDT: Live API check

- `.env` holds `ANTHROPIC_API_KEY` (mode 600, gitignored). Run commands load it with `set -a; . ./.env; set +a`.
- One `claude -p --bare` call through `cotml-proxy` returned `OK`, cost $0.004. Usage fields include `output_tokens_details.thinking_tokens`.
- Pilot plan approved: $3 / 60 turns / 30 min, medium effort, 10 miniF2F + 10 PutnamBench, condition `bare`. Waits on verifier fix.

## 2026-10-13 17:33 PDT: Verifier fixed, pilot started

- Root cause: SafeVerify imported Mathlib four times (28 GB RSS); the 8 GB container killed it (exit 137) before any check ran. Fix in `harness/safeverify/Main.lean`: import once (6 GB, 2 s).
- `harness/tests/run_tests.sh`: 11 cases pass (miniF2F and PutnamBench; `sorry`, axiom, weaker statement, `native_decide`, `#eval`, changed `_solution`, dropped `_solution` all rejected; two real proofs and an `exact?` leftover accepted).
- `verify.py`: memory 12 GB; target cache keyed by path hash. One verify call: about 6 s.
- Side effect: a stray Lean v4.35.0 toolchain was downloaded to `~/.elan`; harmless.
- Pilot: `runs/pilot1/`, bare, medium, $3 / 60 turns / 30 min, 10 + 10 problems, parallel 5.

## 2026-10-13 17:55 PDT: Pilot result, low-effort probe

- `runs/pilot1` (bare, medium, $3/60 turns/30 min): miniF2F 10/10, mean $0.027, 4.5 turns, mean 1,907 output tokens. PutnamBench 9/10, mean $0.135, 9.8 turns, mean 9,312 output tokens. Total about $1.60. No cap reached.
- One failure: `putnam_1997_a6`. Agent duplicated the binder `(S : Set ℝ)`; file compiles; SafeVerify rejects the changed theorem type; agent claimed success.
- Search tactics: 0% of miniF2F runs; 33% of solved Putnam runs used one, 11% left one in the final file.
- Fixed `proof_text` in `run.py` (trailing-space mismatch after `by`); `harness/recompute_proof.py` repairs old results.
- Ceiling: medium effort solves nearly all. Budget is not a constraint (about $0.08 per run).
- Probe started: `runs/probe_low`, same 20 problems, effort low.

## 2026-10-13 18:03 PDT: Language v0, hard subset

- `conditions/sponge.md`: v0 from the user's sketch: DEF, GOAL, FACT, HYP, INFER, PLAN, CHECK, RESULT; 7 rules. Versions are named after sea creatures by intelligence (`conditions/README.md`).
- miniF2F at low effort: 10/10. Putnam low effort: 4/4 so far. Low effort does not reduce the pass rate.
- `problems/hard_putnam.txt`: 139 problems, year >= 2000, number >= 4. `problems/probe_hard_putnam.txt`: 20 of them, seed 20261013, pilot problems excluded.
- Budget caps: derive pass-within-budget from uncapped runs (solved and cost <= B). No capped batches needed.

## 2026-10-13 18:08 PDT: Proxy DNS failure

- Five Putnam low-effort runs failed with `ERR_PROXY_TUNNEL` (Squid `TCP_TUNNEL/503`) from 01:03 UTC. Cause: Docker embedded DNS (127.0.0.11) in the proxy container stopped answering after about 40 minutes. The allowlist was not the cause.
- Fix: `squid.conf` now uses `dns_nameservers 8.8.8.8 8.8.4.4` directly. Proxy restarted; 13/13 egress tests pass.
- `run.py`: a run that ends in `api_error` with 0 output tokens is retried up to 3 times; failed attempts kept as `<run>.apierr<n>`.
- Errored runs moved to `runs/probe_low_errored/`; the five Putnam runs resumed.

## 2026-10-13 18:09 PDT: Hard-subset probe started

- `runs/probe_hard`: 20 problems from `problems/probe_hard_putnam.txt`, bare, low, $3 / 60 turns / 30 min, parallel 5. Runs alongside the last Putnam low-effort runs.

## 2026-10-13 18:15 PDT: Probes

- Putnam low effort: 10/10 (after proxy fix). miniF2F low: 10/10. Effort level does not change pass rate or cost on these sets.
- `harness/compliance.py`: share of visible assistant lines that start with a construct. Bare runs: 0%, 4-8 visible lines per run.
- Hard probe in progress: 10/11 solved so far. First failure: `putnam_2019_a4` (gave up, file does not compile).

## 2026-10-13 18:26 PDT: FATE-H

- Harder-eval survey done (FATE-H/X, CombiBench, FormalQualBench, SorryDB, others). Chosen: FATE-H (100 graduate algebra problems, `frenzymath/FATE-H`, tag v4.28.0).
- `data/fateh/fateh_NNN.lean`: 96/100 compile on Mathlib v4.33.1 (`data/fateh_check.tsv`); 4 use renamed Mathlib names.
- `run.py` bench `fateh`. `problems/fateh_ok.txt` (96), `problems/probe_fateh.txt` (20, seed 20261013).
- Turn distribution (54 solved runs): miniF2F median 3; Putnam median 12, p90 19. A 12-turn cap would put the hard Putnam subset near 47%.
- Probe started: `runs/probe_fateh`, bare, low, parallel 5.

## 2026-10-13 18:40 PDT: Hard Putnam probe result

- `runs/probe_hard` (20 problems, bare, low): 18/20 solved, mean $0.28, median 12 turns, 17% of solved runs used a search tactic. Failures: `putnam_2019_a4` (gave up, 5 turns), `putnam_2022_a5` (gave up, 2 turns). Most expensive: `putnam_2025_a5`, 29 turns, 72k output tokens, $1.08.
- FATE-H probe: 15/15 solved so far.

## 2026-10-13 18:45 PDT: Haiku probe

- FATE-H probe (bare, low): 19/19 solved so far, mean $0.16, median 12 turns. FATE-H is not hard for a Sonnet 5.5 agent.
- Decision: stay with `bare` until a setting with a higher failure rate exists. Language runs must start early enough to leave time for analysis.
- `run.py --model` added. Probe: Haiku 5.5, bare, low, 20 hard Putnam + 20 FATE-H, `runs/probe_haiku`.

## 2026-10-13 18:54 PDT: Haiku probe result, main runs started

- Haiku 5.5 bare low on hard Putnam: 9/18 so far. Every failure is a 2-turn give-up with no compile attempt. Solved runs cost $0.01-0.03.
- Decision: main model Haiku 5.5. Problems: `problems/main_hard_putnam.txt` (60 = 20 probed + 40 new, seed 20261014) + FATE-H 20. Conditions bare, cod, sponge. Effort low.
- `runs/main_haiku.sh` launched: cod+sponge on the 40 probed problems, then bare/cod/sponge on the 40 new. Output `runs/main_haiku/`.

## 2026-10-13 19:00 PDT: Timestamp correction, Haiku result

- Entries from 17:20 to 18:54 above were first written with estimated times up to 5 h too late. Corrected from the `started_at` fields in `result.json`.
- Haiku 5.5 bare low, hard Putnam 20: 10/20 solved (50%). All 10 failures are 2-turn give-ups with no compile. Solved runs: $0.01-0.06, 17k-83k output tokens.
- `harness/analyze.py`: Pareto plots, budget and turn-cap curves, McNemar and sign tests, `analysis/summary.md`. Tested on current data.
- Sonnet FATE-H final: 19/20. `fateh_067` rejected with verifier `timeout` (host overloaded); re-verifying.

## 2026-10-13 19:02 PDT: caveman condition

- `conditions/caveman.md`: copied verbatim from https://github.com/JuliusBrussee/caveman (744 words). Output-style control with wide real-world use.
- Queued on the same Haiku problem sets (`runs/main_haiku_caveman.sh`, parallel 4). Added to `analyze.py` (slot 4, yellow).

## 2026-10-13 19:06 PDT: Interim

- `sponge` compliance in visible text: 62% of lines tagged (FACT, PLAN, INFER, RESULT, GOAL). The language changes the form of a give-up, not the decision: `CHECK` lines are not executed, `RESULT Not achievable` follows with no compile.
- All Haiku failures are "untouched" (file still has the original `sorry`). `analyze.py` now reports untouched vs attempted-fail.
- Candidate next rung (`jellyfish`): CHECK must be a tool run; RESULT quotes tool output; a give-up needs at least N executed CHECKs.

## 2026-10-13 19:11 PDT: Turn-cap detection

- Claude Code reports `subtype: success`, `terminal_reason: completed` at the 60-turn cap, and the agent writes a wrap-up. `run.py` and `analyze.py` now classify `num_turns >= max_turns` as `hit_cap`. First case: `fateh_033` (Haiku, bare), 60 turns, proof nearly complete.
- Haiku FATE-H bare so far: 11/13 solved. FATE-H is not a hard set for Haiku either.

## 2026-10-13 19:16 PDT: Probed-set batches done

- cod and sponge on the 20 probed hard Putnam problems: done (40 runs). Chain continues with bare/cod/sponge on 40 new problems.
- Pass/fail is a property of the problem: the same 9-10 problems fail under every condition, almost all as 2-turn give-ups. cod solved two problems that bare and sponge quit on (`2010_a5`, `2021_b5`).
- Run-to-run variance in tokens (same problem, same condition) is about 2x, the same size as between-condition differences. Proposed: 2 extra repeats per problem on the probed set.
- `fateh_067` (Sonnet): compiles, but SafeVerify kernel replay exceeds 600 s. `verify.py` SafeVerify timeout raised to 1800 s; re-check running.

## 2026-10-13 19:16 PDT: Repeat 1 complete on the probed set

- Haiku 5.5, hard Putnam 20, low: bare 55%, cod 65%, sponge 55%, caveman 45%. No pair significant (McNemar p >= 0.5). Token ratio vs bare on both-solved: cod 0.93, sponge 1.11, caveman 1.01.
- Repeats 2 and 3 launched (`runs/rep2_haiku`, `runs/rep3_haiku`; 80 runs). `analyze.py` pairs by (problem, repeat).

## 2026-10-13 19:25 PDT: Scope change

- Dropped miniF2F, FATE-H and random Putnam (near ceiling). FATE-H cod/sponge/caveman batches stopped at 13/40 and 7/20.
- Kept: hard Putnam (60 problems; repeats on the 20 probed). New-40 batch started under bare/cod/sponge/caveman (`runs/main_haiku_new40.sh`, parallel 8).
- Next sets: FATE-X and CombiBench; survey of other hard formally verifiable evals, Lean and non-Lean.

## 2026-10-13 19:28 PDT: FATE-X

- `data/fatex`: 98/100 compile on v4.33.1 (`fatex_009` Mathlib rename, `fatex_041` needs noncomputable). 39 files define helpers before the theorem; all have one `sorry` in the theorem.
- `problems/probe_fatex.txt` (20). Probe started: bare, low, Haiku then Sonnet (`runs/probe_fatex_haiku`, `runs/probe_fatex_sonnet`).
- Note: `probe_fateh.txt` was sampled from unsorted check-order; not reproducible from the recipe. FATE-H is dropped, so no action.

## 2026-10-13 19:30 PDT: CombiBench

- `data/combi`: 99 files (45 with official answers substituted from `metadata.csv`, cross-checked against `with_solution/`); 93 compile on v4.33.1. Excluded: `imo_2019_p5` (two theorems). A stray theorem removed from `imo_2010_p5`.
- `problems/probe_combi.txt` (20). Probe started: bare, low, Haiku then Sonnet.

## 2026-10-13 19:36 PDT: CombiBench and FATE-X probes (Haiku, bare, low)

- CombiBench: 8/20 (40%). In the target band. Sonnet half running.
- FATE-X: 3/18 so far (about 17%). Too hard for Haiku; Sonnet half pending.
- Eval survey done (subagent). Candidates in band: CAM-Bench (1,000 statements, same toolchain, <1 h), FormalTCS FT2FP (Claude Code pass@8: Sonnet-5 24%, Haiku-4.5 8%; 2-4 h), AlgoVeri-Verus (non-Lean, fixed specs). Awaiting choice.

## 2026-10-13 19:39 PDT: CAM-Bench and AlgoVeri-Verus setup started

- Two subagents: CAM-Bench (Lean, same toolchain) and AlgoVeri Verus track (new image `cotml-verus`, `verify_verus.py`).
- CombiBench defect finding: Sonnet gives correct counterexamples for mis-formalized statements (e.g., `brualdi_ch12_62`, single-vertex graph). Plan: flag problems where Sonnet claims a counterexample and exclude them.

## 2026-10-13 19:52 PDT: jellyfish (v1)

- Budget: $18.13 spent, 359 runs; burn $5.7/h at 20 containers. Sonnet is 80% of spend. Wall time, not dollars, is the constraint.
- `conditions/jellyfish.md`: domain-general core (26 constructs, 10 rules) + Lean dictionary. Ideas: refuter-bound checks, provenance, grounding, exhaustive cases, assumption retraction, branch budgets, objection before done, evidence-based termination.
- Launched on hard Putnam 60, Haiku (`runs/jellyfish_haiku.sh`, parallel 4). `compliance.py` and `analyze.py` know the new constructs.

## 2026-10-13 19:53 PDT: SafeVerify false reject fixed

- Cause: hygienic universe-parameter names of auto-generated `noConfusion`/`noConfusionType` embed the module name (`Target` vs `Submission`). SafeVerify compared level params syntactically. Fix in `harness/safeverify/SafeVerify/Util.lean`: canonical renaming of hygienic level params only. Tests 13/13 (two new: `combi_good`, `combi_ctor_renamed`).
- Affected past runs: only `combi_imo_2010_p5` (Sonnet); the problem is excluded anyway (truncated-subtraction loophole, exploited by the agent).

## 2026-10-13 19:53 PDT: CAM-Bench

- `data/cam`: 627 single-`sorry` files of 778 (150 multi-theorem files excluded; 1 banned token); 625 compile on v4.33.1. Books: Convex Optimization (+ Additional Exercises), Numerical Optimization, one Chinese optimization text.
- `problems/probe_cam.txt` (20). Probe started: bare, low, Haiku then Sonnet.

## 2026-10-13 20:03 PDT: Verus ready, CombiBench defects, jellyfish observation

- AlgoVeri-Verus: image `cotml-verus`, 77 tasks in `data/verus`, `harness/verify_verus.py` (24/24 cheat tests). Verus 0.2025.01.13 does not check termination; AlgoVeri's pipeline is exploitable by `loop {}`; our verifier adds termination, attribute allowlist, spec identity, shadowing checks. `run.py` diff pending (`harness/tests/verus/run_verus.diff`).
- CombiBench: 5/19 problems flagged by Sonnet (4 counterexamples, 1 loophole): `problems/combi_defective_sonnet.txt`.
- jellyfish: grammar followed, binding rules not. On `2011_a5`: REFUTER lines written, 0 compiles, GIVEUP (rule 9 ignored). `claude -p --resume` works in bare mode; a runner-side rule check (resume with a reminder on premature GIVEUP) is being built behind `--enforce-min-checks`.

## 2026-10-13 20:12 PDT: Enforcement loop, Verus probe

- `run.py --enforce-min-checks N --enforce-rounds K`: on a premature GIVEUP the runner resumes the session with `harness/enforce_giveup.md`. Live test on `2011_a5` (jellyfish): 2 compiles, reminder, exactly 1 more compile, GIVEUP again. Enforcement yields minimal compliance, not effort. Cost accounting: a resumed call's `total_cost_usd` is cumulative; taken from the last event.
- Verus runner integration applied (`harness/tests/verus/run_verus.diff`). Dry run OK on 20 tasks. Probe started: bare, low, Haiku then Sonnet, parallel 3.

## 2026-10-13 20:17 PDT: Main batches nearly complete; first plots

- Hard Putnam, Haiku, 60 problems, repeats pooled (n=79-80 per condition): bare 46%, cod 48%, sponge 41%, caveman 41%, jellyfish 53% (n=19). No pair significant (McNemar p >= 0.13). Token ratio on both-solved: cod 0.97, sponge 1.20, caveman 1.01, jellyfish 1.08.
- Other benches (bare): CombiBench Haiku 40% / Sonnet 60%; FATE-X 20% / 50%; CAM-Bench 85% / 82%; Verus Haiku 3/7 so far (all attempted, no untouched give-ups).
- `analysis/putnam/`: pareto_tokens.png, pareto_cost.png, budget_curves.png, turn_curves.png, summary.md, results.csv. `analyze.py --bench --min-n` added.

## 2026-10-13 20:24 PDT: Four-condition result on hard Putnam (60 problems, 2 repeats on 20)

- Haiku 5.5, low: bare 46%, cod 49%, sponge 41%, caveman 41% (n=80 each). No pair significant (McNemar p 0.22-0.69). Token ratio on both-solved vs bare: cod 0.97, sponge 1.20, caveman 1.01.
- Per-problem outcomes are nearly deterministic across repeats and conditions: the same ~10 of 20 probed problems fail under every condition in every repeat; discordance is 1-6 problems of 80.
- Compliance (visible text): sponge 69%, jellyfish 56%, others 0%. jellyfish (n=31 so far): 58%, discordant 2/1 vs bare.
- Repeat 3 and jellyfish new-40 still running. Verus probe: Haiku 6/12.

## 2026-10-13 20:28 PDT: Probe finals

- FATE-X: Sonnet 10/20 (50%), Haiku 4/20 (20%). CAM-Bench: 85% both models (dropped). Verus Haiku 10/17 so far, failures are attempted (not give-ups).
- Theories for the null result written up (capability bottleneck; hidden thinking; grammar as format not control flow; terse formats suppress exploration; low power; compiler is already the controlled language; trained-in procedure; model size; prompt length; no domain knowledge). Proposed tests: Sonnet + sponge/jellyfish on FATE-X; thinking share; language in user turn; hard enforcement.

## 2026-10-13 20:32 PDT: Verus probe (Haiku) final

- AlgoVeri-Verus, Haiku bare low: 12/20 (60%). Failures: 1 spec change (`#![auto]` trigger inside ensures; correct reject), rest verification failures after 2-24 turns. Few early give-ups. Sonnet half running.
- Thinking share of output tokens: 74-78% in every condition; terse conditions highest. The languages act on the visible quarter only.

## 2026-10-13 20:38 PDT: Verus trigger policy

- Two `spec` rejects (Haiku LIS, Sonnet dijkstra) were caused by inserted trigger annotations (`#![auto]`, `#[trigger]`). Policy: triggers are allowed edits to fixed regions (no semantic change); helper definitions inside fixed regions remain rejects. Verifier update delegated; the two runs will be re-verified and reconciled.

## 2026-10-13 20:44 PDT: jellyfish final

- jellyfish on hard Putnam 60 (Haiku): 38% vs bare 45% paired (5/1 discordant, p=0.22); 55% on the probed 20, lower on the new 40. Same signature as sponge/caveman: fewer turns, more untouched give-ups. Token ratio 1.10.
- Monitors expiring at 30 min were mistaken for hung batches; all runners alive. Rep 3 at 24/80; Verus Sonnet 9/20 (6 solved).

## 2026-10-13 20:58 PDT: Verus probe complete

- AlgoVeri-Verus, bare, low: Haiku 12/20 (60%), Sonnet 16/20 (80%). Failures are attempted verification failures, not early give-ups; two `spec` rejects are trigger annotations in fixed code (kept as rejects). Plots in `analysis/verus/`.
- Repeat 3 at 51/80. Spend $38.94.

## 2026-10-13 23:17 PDT: Session restart; all batches complete

- The Claude Code session ended around 21:00 and resumed 23:16. All runners finished on their own: repeat 3 80/80, jellyfish 60/60, Verus Sonnet 20/20.
- Final hard Putnam, Haiku 5.5, low, 60 problems, 3 repeats on 20 (n=100 per condition): bare 47%, cod 49%, sponge 44%, caveman 44%, jellyfish 38% (n=60). McNemar p vs bare: 0.69, 0.45, 0.51, 0.22. Token ratio on both-solved: cod 0.97, sponge 1.23, caveman 1.16, jellyfish 1.10.
- Per-problem outcomes are near-deterministic: on the probed 20, bare has mixed outcomes across 3 repeats on 1 problem; 9 problems fail 0/3 under every condition.
- Visible compliance: sponge 68%, jellyfish 64%, others 0%.
- `analysis/putnam/` regenerated (460 runs).

## 2026-10-13 23:18 PDT: Results write-up

- `analysis/RESULTS.md`: question, conditions, benchmark difficulty table, main result (n=100 per condition), why the languages did not act, harness findings, cost, proper tests. 750 runs, $39.15.
- Plot labels staggered; `analysis/putnam/` regenerated.

## 2026-10-13 23:29 PDT: Verus jellyfish; SWE session planned

- Verus jellyfish (Haiku) running: 5/11 so far vs bare 12/20.
- Unsupervised 8-hour SWE session (23:30-07:30) approved with these decisions: SWE-bench Verified; both framings (issue-only, debugging with failing test names), 24 tasks each; Haiku bare/cod/jellyfish + Sonnet bare; spend cap $150; I adjust framing/model on my own if the probe lands outside 20-80% and log it here.
- Plan: setup 23:30-01:00 (images, adapter, official evaluation harness as verifier, dry run, 6+6 probe); main runs 01:00-06:30 (about 190 runs, parallel 6); analysis 06:30-07:30 (`analysis/swe/`, RESULTS.md update).
- Adapter build delegated to a subagent.

## 2026-10-13 23:44 PDT: Verus jellyfish done; SWE adapter ready

- Verus, Haiku: jellyfish 12/20 = bare 12/20; discordant 1/1; token ratio 0.77 on both-solved (p=0.55, n=11). Visible compliance 36%. Added as section 4b in RESULTS.md.
- SWE-bench Verified adapter works end to end: official eval images and harness; gold patch passes, empty fails; one real Haiku run solved django-11179 (5 turns, $0.001). Dataset from `SWE-bench/SWE-bench_Verified` (has eval fields). Docker Hub pull quota hit; pulls continue over IPv4 at about 3 min per image (6/48 at 23:43).
- Decisions: debug framing applies the gold test patch before the agent starts (so the named tests exist); test-file edits are flagged, not failed. Subagent implementing.

## 2026-10-13 23:48 PDT: SWE session launched

- Debug framing: gold test patch applied and committed before the agent starts; model patch diffed against that commit. Gold-patch check passes under both framings.
- Image pull detached (IPv4 registry API, about 3 min per image); order follows the issue list. Session script `runs/swe_session.sh` waits per list: issue probe + Haiku bare/cod/jellyfish, then debug probe + same, then Sonnet bare on both, then analysis. Log: `runs/swe_session.log`.
- Band rule after each probe: if the framing's bare pass rate is outside 20-80%, I adjust and log.

## 2026-10-14 00:00 PDT: SWE session restart

- Image pulls finished for the issue list at 23:56 (faster than estimated). Issue probe: 5/5 django tasks solved in 3-8 turns, about $0.002 each.
- The `astropy-14309` image carries a "SWE-bench" setup commit that edits `pyproject.toml`; the clean-state check only accepted mode-only commits. Relaxed to accept HEAD^ == base_commit. My `pkill` pattern also hit the running issue step; stray containers cleaned and the session relaunched (resumes).

## 2026-10-14 00:07 PDT: Band rule applied: harder SWE set added

- Issue probe 6/6 and the first 26 main runs all solved in 3-9 turns, under $0.004 each: above the 80% band and consistent with memorized fixes (SWE-bench Verified is in training data).
- Main plan continues unchanged (cheap). Added `problems/swe_hard.txt`: 48 non-django tasks (`harness/sample_swe_hard.py`, seed 20261015, proportional by repo), issue framing. `runs/swe_hard_session.sh` waits for the main session, pulls images, runs Haiku bare/cod/jellyfish + Sonnet bare, then analysis. Log: `runs/swe_hard_session.log`.

## 2026-10-14 01:02 PDT: SWE issue framing complete

- Issue list, Haiku, 24 tasks x 3: 72/72 runs done. Interim: bare 91%, cod 96%, jellyfish 87% (n=23 at last check); jellyfish +19% output tokens on commonly solved tasks (sign test p=0.012). Set is saturated; the hard set is queued.
- `scikit-learn-14710`: the hist-gradient-boosting test module runs 15-25 min; the jellyfish agent hit the 25-min wall cap, its patch passed (solved, tokens undercounted). Keep in mind for the 6 sklearn tasks in the hard set.
- Debug framing step started.

## 2026-10-14 01:03 PDT: Debug probe

- Debug framing probe (Haiku bare, 6 tasks): 6/6 solved. Above band; the hard non-django set already queued is the adjustment. Debug main step (72 runs) running.

## 2026-10-14 01:28 PDT: Main SWE session complete

- SWE-bench Verified, 48 tasks (24 issue + 24 debug), low effort. Haiku: bare 94%, cod 96%, jellyfish 92%; Sonnet bare 98%. Discordant vs bare: cod 0/1, jellyfish 2/1 (p=1.0). Tokens on commonly solved: cod 1.03 (p=0.77), jellyfish 1.14 (p=0.001, n=43). Cost per Haiku run $0.002; Sonnet $0.021.
- Set is saturated (memorized fixes). Hard non-django set pending image pulls.

## 2026-10-14 01:30 PDT: Hard SWE session unblocked

- The hard session's wait loop matched its own launcher shell (the heredoc that wrote the script contained the pattern). Killed the launcher; the detached script continued and started pulling the 48 hard-set images at 01:30.

## 2026-10-14 02:50 PDT: Hard SWE set, Haiku complete

- Non-django 48 tasks, Haiku low: bare 69%, cod 67%, jellyfish 67%. Discordant vs bare: cod 2/1, jellyfish 1/0. Token ratio on both-solved: cod 1.03 (p=0.47), jellyfish 1.24 (p=0.002, n=32). Pooled over all 96 SWE tasks: 81% / 81% / 79%; jellyfish 1.19 (p<0.001, n=75).
- Sonnet bare on the hard set running; analysis follows automatically.

## 2026-10-14 03:07 PDT: SWE session complete

- All SWE runs done at 03:06 (384 runs). Haiku over 96 tasks: bare 81%, cod 81%, jellyfish 79%; Sonnet bare 85%. Hard non-django set: 69/67/67/73. jellyfish +19% tokens on commonly solved (p<0.001, n=75); cod neutral. Visible jellyfish compliance 22%.
- `analysis/swe/` written by the session script; RESULTS.md section 4c added. Totals: 1,155 runs, $42.67.
- Remaining: final plot check, presentation support. No runs pending.

## 2026-10-14 03:07 PDT: Deliverables final

- `analysis/summary_all.png`: one cross-domain figure (pass rate with CI; token ratio vs bare on commonly solved tasks) for Lean, Verus, SWE.
- Per-domain: `analysis/putnam/`, `analysis/verus/`, `analysis/swe/` (pareto_tokens, pareto_cost, budget_curves, turn_curves, summary.md, results.csv).
- Write-up: `analysis/RESULTS.md`. Conditions: `conditions/`. Harness: `harness/`. Runs: `runs/`. No processes running.

## 2026-10-14 15:17 PDT: Repository prepared for GitHub

- `.gitignore`: `.env`, Lake build dirs, the Claude binary, the SWE venv and dataset, the nine benchmark clones, `runs/targets`, `runs/**/swe_eval`.
- Hard-coded home paths removed from `harness/run.py`, `harness/verify.py`, `harness/check_statements.sh`, `harness/docker/Dockerfile` (now build args; `harness/docker/build.sh`). Toolchain path override: `COTML_TC`.
- All run artifacts and `data/*_check.tsv` rewritten: `/home/<user>` replaced by `/home/user` (2,113 files). One SWE transcript (`runs/swe_sonnet/django__django-14315__bare__low/agent.jsonl`) contained the API key, printed by the agent's `env` dump; redacted.
- Stale files deleted: `harness/run.py.orig`, `harness/tests/verus/run_verus.diff`.
- Lean verifier tests 13/13 after the path change. README: results pointer, layout, setup, data licenses.
- Staged, not committed: 11,148 files, 150 MB.
