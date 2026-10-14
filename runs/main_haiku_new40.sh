#!/usr/bin/env bash
# 40 new hard-Putnam problems, Haiku 5.5, all four conditions.
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
python3 harness/run.py --model claude-haiku-5-5 --effort low --max-turns 60 --max-budget-usd 3 --timeout-min 30 --parallel 8 \
  --out runs/main_haiku/ --bench putnam --problems problems/main_hard_putnam_new40.txt --condition bare,cod,sponge,caveman
