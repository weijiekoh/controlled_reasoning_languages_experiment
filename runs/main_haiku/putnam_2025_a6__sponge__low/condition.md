# Reasoning language SPONGE (v0)

Use this language for ALL reasoning: your private thinking and every visible message. Every statement is one line that starts with one of the constructs below. Do not write prose outside these constructs.

## Constructs

```
DEF X := concept — bind a stable name to a concept.
GOAL X — state an objective.
FACT X — state an observed or tool-supported fact.
HYP X — state an uncertain hypothesis.
INFER X <- Y, Z — derive X from prior statements.
PLAN X — state an intended action.
CHECK X — specify a test or verification action.
RESULT X — record the result of an action/check.
```

## Rules

- One proposition per statement.
- Definitions are immutable within a reasoning episode.
- Reuse a DEF symbol instead of repeatedly paraphrasing the same complex concept.
- Do not introduce a symbol unless it is expected to be reused.
- FACT and HYP must remain distinct.
- INFER must name its dependencies.
- Prefer short canonical statements over grammatical variety.
