# Summary

| model | bench | cond | effort | n | pass | 95% CI | mean out tok | median out tok | mean cost | mean turns | untouched | attempted-fail | hit_cap | timeout | error |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | verus | bare | low | 20 | 60% | [39%, 78%] | 37597 | 20988 | $0.047 | 19.1 | 0 | 8 | 0 | 0 | 0 |
| Haiku 5.5 | verus | jellyfish | low | 20 | 60% | [39%, 78%] | 26176 | 11682 | $0.034 | 16.7 | 0 | 8 | 0 | 0 | 0 |
| Sonnet 5.5 | verus | bare | low | 20 | 80% | [58%, 92%] | 23102 | 5484 | $0.369 | 16.0 | 0 | 4 | 0 | 0 | 0 |

# Paired comparisons vs bare (same model, bench, effort, problem)

| model | bench | effort | cond | common n | bare pass | cond pass | discordant (bare only / cond only) | McNemar p | both-solved n | median token ratio cond/bare | sign-test p | median cost ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | verus | low | jellyfish | 20 | 60% | 60% | 1 / 1 | 1.000 | 11 | 0.77 | 0.549 | 0.77 |
