# Results: controlled reasoning languages for a Lean/Verus coding agent

Date: 2026-10-13/14. Agent: Claude Code 2.1.296 in `--bare` mode, Docker sandbox, egress allowlisted to `api.anthropic.com`. Models: Claude Haiku 5.5 (main), Claude Sonnet 5.5 (reference). Effort `low` unless stated. Caps: 60 turns, $3, 30 min. Verification: Lean 4.33.1 + Mathlib compile, then SafeVerify kernel replay (same statement, three standard axioms); Verus 0.2025.01.13 with spec identity, trust and termination checks.

## 1. Question

Does a controlled reasoning language, injected as a system-prompt appendix, raise a coding agent's pass rate or cut its output tokens on formally verified tasks?

## 2. Conditions

| Condition | Appendix | Words |
|---|---|---|
| `bare` | none | 0 |
| `cod` | Chain of Draft (Xu et al. 2025): "keep a minimum draft for each thinking step, 5 words at most" | 20 |
| `caveman` | JuliusBrussee/caveman, verbatim: terse output voice | 744 |
| `sponge` | v0 language: DEF, GOAL, FACT, HYP, INFER, PLAN, CHECK, RESULT + 7 rules | 170 |
| `jellyfish` | v1: 26 domain-general constructs (REFUTER, CHECK binding, GROUND, CASES EXHAUSTIVE, ASSUME/RETRACT, BRANCH/BUDGET, OBJECTION/REPLY, STATE, evidence-based DONE/GIVEUP) + Lean dictionary | 594 |

## 3. Benchmark difficulty (bare, low effort)

| Benchmark | n | Haiku 5.5 | Sonnet 5.5 | Note |
|---|---|---|---|---|
| miniF2F-test | 10 | — | 100% | saturated |
| PutnamBench, random | 10–30 | — | 90–93% | saturated |
| FATE-H (graduate algebra) | 20 | 80% | 95% | saturated; published 3% for provers in 2025 |
| CAM-Bench (applied math) | 20 | 85% | 85% | saturated |
| **PutnamBench hard (A4–B6, 2000+)** | 20 / 100 | **47%** | 90% | main set |
| CombiBench | 20 | 40% | 60% | 5/19 statements false or exploitable (Sonnet gave counterexamples) |
| FATE-X (beyond PhD) | 20 | 20% | 50% | Sonnet's hard set |
| AlgoVeri-Verus (verified programs) | 20 | 60% | 80% | second domain; failures are attempted, not give-ups |

Published pass rates for provers do not predict agent results: FATE-H went from 3% (pass@64, 2025) to 95% for a Sonnet agent with a compiler loop.

## 4. Main result: hard PutnamBench, Haiku 5.5, 60 problems, 3 repeats on 20 (n = 100 per condition)

| Condition | Pass | 95% CI | Median output tokens | Mean turns | Untouched give-ups | Discordant vs bare (bare only / cond only) | McNemar p | Token ratio on both-solved | Visible compliance |
|---|---|---|---|---|---|---|---|---|---|
| bare | 47% | 38–57 | 12.5k | 8.6 | 52 | — | — | — | 0% |
| cod | 49% | 39–59 | 13.4k | 8.5 | 51 | 2 / 4 | 0.69 | 0.97 | 0% |
| sponge | 44% | 35–54 | 6.8k | 6.3 | 56 | 5 / 2 | 0.45 | 1.23 | 68% |
| caveman | 44% | 35–54 | 9.8k | 7.5 | 56 | 6 / 3 | 0.51 | 1.16 | 0% |
| jellyfish (n=60) | 38% | 27–51 | 6.2k | 6.5 | 37 | 5 / 1 | 0.22 | 1.10 | 64% |

Plots: `analysis/putnam/pareto_tokens.png`, `pareto_cost.png`, `budget_curves.png`, `turn_curves.png`.

Findings:

1. **No condition changes the pass rate.** All within 9 points of bare; no McNemar test below p = 0.22. Discordance is 3–9 problems of 100.
2. **No condition saves tokens on problems both conditions solve.** cod 0.97×; the languages cost 10–23% more.
3. **Outcomes are determined by the problem, not the prompt.** On the probed 20 across 3 repeats, 9 problems fail 0/3 under every condition and 9 succeed 3/3 under every condition. Bare has a mixed outcome on 1 of 20.
4. **Terse conditions quit sooner.** sponge, caveman, jellyfish: fewer turns (6.3–7.5 vs 8.6) and more untouched give-ups (56 vs 52). Lower mean cost comes from quitting, not from efficiency.
5. **Every failure is the same event:** the agent reads the problem, reasons on paper, and declares the formalization too large, with zero compiles. Sonnet solves these same problems.
6. **The model is the lever:** Haiku 47% vs Sonnet 90% on identical problems and harness.

## 4b. Second domain: AlgoVeri-Verus, Haiku 5.5, 20 tasks

| Condition | Pass | Median output tokens | Mean turns | Discordant (bare only / cond only) | Token ratio on both-solved | Sign-test p | Visible compliance |
|---|---|---|---|---|---|---|---|
| bare | 60% | 21.0k | 19.1 | — | — | — | 0% |
| jellyfish | 60% | 11.7k | 16.7 | 1 / 1 | 0.77 | 0.55 | 36% |

Same pass rate; 23% fewer output tokens on the 11 commonly solved tasks (not significant at n = 11). Verus failures are attempted verification failures after 3–40 turns, not early give-ups, so the budget and refuter constructs were exercised. The direction differs from Lean (sponge +23%, jellyfish +10%) and is the only token saving seen for a language. n = 20 single-repeat; treat as a lead, not a result.

## 4c. Third domain: SWE-bench Verified (hidden tests), 96 tasks

Setup: official per-task images and official evaluation harness (hidden FAIL_TO_PASS and PASS_TO_PASS tests). 48 tasks sampled across repositories (24 issue-only, 24 debugging: gold test patch applied and failing test names shown) plus 48 non-django tasks (issue-only) added after the first probe saturated. Haiku 5.5 low effort, 50 turns, $2, 25 min; Sonnet 5.5 bare as reference. Runs took 10-60 s and $0.002 (Haiku) to $0.02 (Sonnet).

| Set | Haiku bare | Haiku cod | Haiku jellyfish | Sonnet bare |
|---|---|---|---|---|
| Main 48 (22 django) | 94% | 96% | 92% | 98% |
| Hard 48 (non-django) | 69% | 67% | 67% | 73% |
| All 96 | 81% | 81% | 79% | 85% |

Paired against bare over 96 tasks: cod discordant 2/2, token ratio 1.03 (p = 0.42); jellyfish discordant 3/1 (p = 0.63), token ratio 1.19 on 75 commonly solved tasks (p < 0.001). Visible compliance with jellyfish: 22% of lines (64% on Lean): on SWE the agent acts instead of narrating.

Reading: the same pattern as Lean and Verus. The pass rate is set by the task, the conditions do not move it, and the full language costs 15-25% more output tokens on identical solved tasks. SWE-bench Verified is contaminated for these models (about a quarter of bare solves are one-test fixes under 1.5k tokens), so absolute rates are inflated; the paired comparison is unaffected.

Harness notes: the official images carry a "SWE-bench" setup commit above base_commit; evaluation runs with network; sklearn test modules can take 15-25 min and hit the wall cap; the Docker Hub pull quota (100/h) needed an IPv4 fallback.

## 5. Why the languages did not act

- **Hidden channel.** 74–78% of output tokens are thinking, in every condition; the terse conditions have the highest share. The appendix shapes the visible quarter only.
- **Grammar as format, not control flow.** Compliance is 64–68% of visible lines, yet `CHECK` lines are written without tool runs and `RESULT` lines are opinions. Example (`putnam_2005_b5`, jellyfish): `STATE: BUDGET 2 checks spent 0` followed by `GIVEUP`. The plan it wrote was the one bare Haiku later executed to solve the problem.
- **Enforcement yields minimal compliance.** With the runner resuming the session on a premature GIVEUP (`--enforce-min-checks 3`), Haiku ran exactly one more compile to reach the minimum and gave up again.
- **The compiler is already a controlled language.** Lean returns exact goals and errors every step; epistemic bookkeeping in prose is redundant with it. Solved runs drop the language once the compile loop starts.
- **Power.** ±10-point CIs at n = 100 with near-deterministic outcomes: a true ±3-point effect is undetectable with tonight's budget. Run-to-run token variance is 2× on the same problem.

## 6. Harness findings worth reporting

- **Verifier matters.** Lean `lake build` alone accepts changed statements and extra axioms. SafeVerify caught: a duplicated binder (Sonnet, `putnam_1997_a6`), an altered `_solution`, `native_decide`, a false-statement exploit via truncated subtraction (Sonnet, `imo_2010_p5`).
- **Benchmarks carry defects.** Sonnet produced correct counterexamples for 4 of 19 CombiBench statements. AlgoVeri's own Verus pipeline accepts `loop {}` as a proof (no termination check in that Verus release).
- **Two verifier bugs fixed tonight:** SafeVerify OOM at 8 GB (imported Mathlib four times), and a false reject on auto-generated `noConfusion` whose universe name embeds the module name.
- **Haiku checks for loopholes** ("There is no formalization loophole I can exploit") before giving up.

## 7. Cost

1,155 runs (460 hard Putnam, 60 Verus, 384 SWE, 251 probes): $43 total. Haiku solved runs cost $0.01–0.05; Sonnet $0.1–1.4. Dollars were never the constraint; wall time (24 cores, 5–10 min per hard run) was.

## 8. What would test the hypothesis properly

1. Sonnet with sponge/jellyfish on FATE-X and CombiBench (where capability suffices and pass is ~50%).
2. Thinking off (`between_tools`) so all reasoning is visible and subject to the language.
3. Language in the user turn, and at medium/high effort.
4. Hard enforcement: no GIVEUP accepted until the turn cap.
5. A domain with no oracle (planning, debugging with hidden tests), where epistemic bookkeeping is not redundant.
6. n ≈ 400 problems for ±5-point resolution.
