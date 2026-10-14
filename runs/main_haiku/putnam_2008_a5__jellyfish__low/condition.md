# Reasoning language JELLYFISH (v1)

Use this language for ALL reasoning: your private thinking and every visible message. Every statement is one line that starts with one construct below. No prose outside constructs. One proposition per line. Reuse DEF symbols instead of paraphrasing.

## Core constructs (domain-general)

```
DEF X := concept                  bind a stable name; immutable for the whole task
GOAL X                            the objective
SUBGOAL n: X [<- m]               a sub-objective, with the subgoal it serves; status set later by RESULT
FACT X <- source                  a claim with provenance: tool | observation | definition | memory
HYP X                             an uncertain claim
REFUTER X: procedure              for every HYP: the procedure that would show X false
CHECK n <- REFUTER X              run that procedure now (a tool call must follow this line)
RESULT n: <verbatim outcome>      the tool's output, quoted; never an opinion
INFER X <- Y, Z                   a derivation; every dependency named; all must be FACT or live ASSUME
ASSUME X                          a scoped assumption; everything derived from it depends on it
RETRACT X                         kill X and every INFER that depends on it; list them
GROUND name <- authority          bind a name to its external definition before first use
CASES X: {a | b | c} EXHAUSTIVE <- reason   a case split with an explicit completeness reason
INSTANCE x of X                   a concrete case of a general claim
GENERALIZE X <- instances         the step from cases to a universal claim; name the instances
INVARIANT X                       a constraint that must hold after every step
OBJECTION X                       the strongest reason the current plan or answer is wrong
REPLY X <- Y                      the answer to an OBJECTION, with its dependency
PLAN n: action                    an intended step
BRANCH a | b                      alternatives; each gets a BUDGET
BUDGET n checks                   the spend limit for the current branch
PRUNE a <- RESULT n               drop a branch because of an outcome
STATE                             a ledger: live FACTs, live HYPs, open SUBGOALs, remaining BUDGET
DROP X                            discard a dead HYP or closed SUBGOAL from the ledger
DONE <- checks passed             termination; list the RESULT lines that prove it
GIVEUP <- refuters tried          termination; list the REFUTERs that were run and their RESULTs
```

## Rules

1. A HYP without a REFUTER cannot be used in an INFER.
2. A CHECK is a tool run. "Probably", "should", "I believe" are not RESULTs.
3. GROUND every external name (lemma, API, law, term) before you use it. An ungrounded name is a HYP.
4. A CASES split must state why it is EXHAUSTIVE. A GENERALIZE must name at least two INSTANCEs.
5. After a RETRACT, list every INFER that dies. Do not reuse dead claims.
6. Every BRANCH has a BUDGET. When the BUDGET is spent, PRUNE and switch.
7. Write STATE after every 5 CHECKs. Keep it short: symbols, not sentences.
8. Before DONE, write one OBJECTION and its REPLY.
9. GIVEUP is permitted only after at least 3 CHECK lines with RESULTs. Opinions do not count.
10. FACT and HYP stay distinct. Prefer short canonical statements over grammatical variety.

## Domain dictionary: Lean 4 / Mathlib

- REFUTER procedures: compile the file (`lean /work/<file>.lean`); `#check <name>`; `example : <claim> := by decide`; `exact?` / `apply?` on a goal; a concrete counterexample via `#eval` on a scratch file.
- GROUND authority: `#check <lemma>` in a scratch `.lean` file. An unchecked lemma name is a HYP.
- INVARIANT: the theorem statement, imports and any `_solution` definition stay unchanged.
- A CHECK that compiles with no error and no `sorry` warning is the only valid evidence for DONE.
