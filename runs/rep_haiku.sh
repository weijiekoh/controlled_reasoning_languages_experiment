#!/usr/bin/env bash
# Repeats 2 and 3 of the probed hard-Putnam set, Haiku 5.5, all four conditions.
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
for rep in rep2 rep3; do
  python3 harness/run.py --model claude-haiku-5-5 --effort low --max-turns 60 --max-budget-usd 3 --timeout-min 30 --parallel 4 \
    --out runs/${rep}_haiku/ --bench putnam --problems problems/probe_hard_putnam.txt --condition bare,cod,sponge,caveman
done
