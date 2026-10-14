# Summary

| model | bench | cond | effort | n | pass | 95% CI | mean out tok | median out tok | mean cost | mean turns | untouched | attempted-fail | hit_cap | timeout | error |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | swe | bare | low | 96 | 81% | [72%, 88%] | 2494 | 2008 | $0.002 | 6.9 | 1 | 17 | 0 | 0 | 0 |
| Haiku 5.5 | swe | cod | low | 96 | 81% | [72%, 88%] | 2462 | 1902 | $0.002 | 7.1 | 2 | 16 | 0 | 0 | 0 |
| Haiku 5.5 | swe | jellyfish | low | 96 | 79% | [70%, 86%] | 2688 | 2230 | $0.003 | 7.1 | 1 | 19 | 0 | 0 | 0 |
| Sonnet 5.5 | swe | bare | low | 96 | 85% | [77%, 91%] | 1100 | 841 | $0.022 | 5.6 | 0 | 14 | 0 | 0 | 0 |

# Paired comparisons vs bare (same model, bench, effort, problem)

| model | bench | effort | cond | common n | bare pass | cond pass | discordant (bare only / cond only) | McNemar p | both-solved n | median token ratio cond/bare | sign-test p | median cost ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | swe | low | cod | 96 | 81% | 81% | 2 / 2 | 1.000 | 76 | 1.03 | 0.422 | 1.00 |
| Haiku 5.5 | swe | low | jellyfish | 96 | 81% | 79% | 3 / 1 | 0.625 | 75 | 1.19 | 0.000 | 1.16 |
