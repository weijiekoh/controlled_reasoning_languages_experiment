#!/usr/bin/env bash
# jellyfish on hard Putnam 60, Haiku 5.5: probed 20 first (fast signal), then the 40 new.
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
R="python3 harness/run.py --model claude-haiku-5-5 --effort low --max-turns 60 --max-budget-usd 3 --timeout-min 30 --parallel 4 --out runs/main_haiku/ --bench putnam --condition jellyfish"
$R --problems problems/probe_hard_putnam.txt
$R --problems problems/main_hard_putnam_new40.txt
