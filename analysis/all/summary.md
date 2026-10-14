# Summary

| model | bench | cond | effort | n | pass | 95% CI | mean out tok | median out tok | mean cost | mean turns | untouched | attempted-fail | hit_cap | timeout | error |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | cam | bare | low | 20 | 85% | [64%, 95%] | 14410 | 5756 | $0.012 | 9.9 | 3 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | combi | bare | low | 20 | 40% | [22%, 61%] | 5441 | 3166 | $0.003 | 3.5 | 12 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | fateh | bare | low | 20 | 80% | [58%, 92%] | 29150 | 19676 | $0.029 | 19.4 | 1 | 1 | 2 | 0 | 0 |
| Haiku 5.5 | fatex | bare | low | 20 | 20% | [8%, 42%] | 8495 | 3970 | $0.006 | 6.8 | 16 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | putnam | bare | low | 100 | 47% | [38%, 57%] | 18608 | 12489 | $0.017 | 8.6 | 52 | 0 | 1 | 0 | 0 |
| Haiku 5.5 | putnam | cod | low | 100 | 49% | [39%, 59%] | 19730 | 13441 | $0.016 | 8.5 | 51 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | putnam | sponge | low | 100 | 44% | [35%, 54%] | 17747 | 6782 | $0.012 | 6.3 | 56 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | putnam | caveman | low | 100 | 44% | [35%, 54%] | 17768 | 9803 | $0.013 | 7.5 | 56 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | putnam | jellyfish | low | 60 | 38% | [27%, 51%] | 16760 | 6236 | $0.014 | 6.5 | 37 | 0 | 0 | 0 | 0 |
| Haiku 5.5 | verus | bare | low | 20 | 60% | [39%, 78%] | 37597 | 20988 | $0.047 | 19.1 | 0 | 8 | 0 | 0 | 0 |
| Sonnet 5.5 | cam | bare | low | 20 | 85% | [64%, 95%] | 4664 | 2874 | $0.069 | 7.0 | 3 | 0 | 0 | 0 | 0 |
| Sonnet 5.5 | combi | bare | low | 20 | 60% | [39%, 78%] | 15942 | 2956 | $0.211 | 7.6 | 7 | 1 | 0 | 0 | 0 |
| Sonnet 5.5 | fateh | bare | low | 20 | 95% | [76%, 99%] | 10111 | 6392 | $0.158 | 12.0 | 0 | 1 | 0 | 0 | 0 |
| Sonnet 5.5 | fatex | bare | low | 20 | 50% | [30%, 70%] | 16725 | 6784 | $0.268 | 15.4 | 8 | 2 | 0 | 0 | 0 |
| Sonnet 5.5 | minif2f | bare | low | 10 | 100% | [72%, 100%] | 1808 | 741 | $0.027 | 4.4 | 0 | 0 | 0 | 0 | 0 |
| Sonnet 5.5 | minif2f | bare | medium | 10 | 100% | [72%, 100%] | 1907 | 822 | $0.027 | 4.5 | 0 | 0 | 0 | 0 | 0 |
| Sonnet 5.5 | putnam | bare | low | 30 | 93% | [79%, 98%] | 16020 | 8949 | $0.234 | 11.6 | 2 | 0 | 0 | 0 | 0 |
| Sonnet 5.5 | putnam | bare | medium | 10 | 90% | [60%, 98%] | 9312 | 9032 | $0.135 | 9.8 | 0 | 1 | 0 | 0 | 0 |
| Sonnet 5.5 | verus | bare | low | 20 | 80% | [58%, 92%] | 23102 | 5484 | $0.369 | 16.0 | 0 | 4 | 0 | 0 | 0 |

# Paired comparisons vs bare (same model, bench, effort, problem)

| model | bench | effort | cond | common n | bare pass | cond pass | discordant (bare only / cond only) | McNemar p | both-solved n | median token ratio cond/bare | sign-test p | median cost ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Haiku 5.5 | putnam | low | caveman | 100 | 47% | 44% | 6 / 3 | 0.508 | 41 | 1.16 | 0.211 | 1.11 |
| Haiku 5.5 | putnam | low | cod | 100 | 47% | 49% | 2 / 4 | 0.688 | 45 | 0.97 | 0.551 | 0.94 |
| Haiku 5.5 | putnam | low | jellyfish | 60 | 45% | 38% | 5 / 1 | 0.219 | 22 | 1.10 | 0.523 | 1.09 |
| Haiku 5.5 | putnam | low | sponge | 100 | 47% | 44% | 5 / 2 | 0.453 | 42 | 1.23 | 0.164 | 1.12 |
