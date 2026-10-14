#!/usr/bin/env bash
# FATE-X probe: 20 problems, bare, low effort, Haiku then Sonnet.
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
R="python3 harness/run.py --effort low --max-turns 60 --max-budget-usd 3 --timeout-min 30 --parallel 4 --bench fatex --problems problems/probe_fatex.txt --condition bare"
$R --model claude-haiku-5-5  --out runs/probe_fatex_haiku/
$R --model claude-sonnet-5-5 --out runs/probe_fatex_sonnet/
