# Conditions

Each file is appended to the agent's system prompt (`run.py --condition NAME`).

| Name | Role | Words |
|---|---|---|
| `bare` | No addition. Baseline. | 0 |
| `cod` | Chain of Draft control (Xu et al. 2025). Brevity without structure. | 20 |
| `caveman` | Copied verbatim from https://github.com/JuliusBrussee/caveman. Terse output voice with wide real-world use. Style control, like `cod`. | 744 |
| `jellyfish` | v1: sponge + domain-general constructs (REFUTER, CHECK binding, GROUND, CASES EXHAUSTIVE, ASSUME/RETRACT, BRANCH/BUDGET/PRUNE, OBJECTION/REPLY, STATE/DROP, DONE/GIVEUP with evidence) + a Lean dictionary. | ~600 |
| `sponge` | Controlled reasoning language v0: 8 constructs (DEF, GOAL, FACT, HYP, INFER, PLAN, CHECK, RESULT), 7 rules. Domain-neutral. | ~170 |

## Language versions

Named after sea creatures, ranked by intelligence, low to high. Each version adds constructs or meta-rules to the previous one.

sponge (v0) < jellyfish < starfish < clam < crab < lobster < mantis shrimp < cuttlefish < squid < octopus < dolphin < orca

## Known confound

`sponge` is about 8x longer than `cod`. A positive result against `cod` could come from prompt length rather than structure. A later control, `cod_long`, should match length without the grammar.
