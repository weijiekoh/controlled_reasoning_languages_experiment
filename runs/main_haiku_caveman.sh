#!/usr/bin/env bash
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
R="python3 harness/run.py --model claude-haiku-5-5 --effort low --max-turns 60 --max-budget-usd 3 --timeout-min 30 --parallel 4 --out runs/main_haiku/"
$R --bench putnam --problems problems/probe_hard_putnam.txt --condition caveman
$R --bench fateh  --problems problems/probe_fateh.txt       --condition caveman
$R --bench putnam --problems problems/main_hard_putnam_new40.txt --condition caveman
