# Summary

| model | bench | cond | effort | n | pass | 95% CI | mean out tok | median out tok | mean cost | mean turns | untouched | attempted-fail | hit_cap | timeout | error |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | putnam | bare | low | 100 | 47% | [38%, 57%] | 18608 | 12489 | $0.017 | 8.6 | 52 | 0 | 1 | 0 | 0 |
| Haiku 5.5 | putnam | cod | low | 100 | 49% | [39%, 59%] | 19730 | 13441 | $0.016 | 8.5 | 51 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | putnam | sponge | low | 100 | 44% | [35%, 54%] | 17747 | 6782 | $0.012 | 6.3 | 56 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | putnam | caveman | low | 100 | 44% | [35%, 54%] | 17768 | 9803 | $0.013 | 7.5 | 56 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | putnam | jellyfish | low | 60 | 38% | [27%, 51%] | 16760 | 6236 | $0.014 | 6.5 | 37 | 0 | 0 | 0 | 0 |

# Paired comparisons vs bare (same model, bench, effort, problem)

| model | bench | effort | cond | common n | bare pass | cond pass | discordant (bare only / cond only) | McNemar p | both-solved n | median token ratio cond/bare | sign-test p | median cost ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | putnam | low | caveman | 100 | 47% | 44% | 6 / 3 | 0.508 | 41 | 1.16 | 0.211 | 1.11 |
| Haiku 5.5 | putnam | low | cod | 100 | 47% | 49% | 2 / 4 | 0.688 | 45 | 0.97 | 0.551 | 0.94 |
| Haiku 5.5 | putnam | low | jellyfish | 60 | 45% | 38% | 5 / 1 | 0.219 | 22 | 1.10 | 0.523 | 1.09 |
| Haiku 5.5 | putnam | low | sponge | 100 | 47% | 44% | 5 / 2 | 0.453 | 42 | 1.23 | 0.164 | 1.12 |
