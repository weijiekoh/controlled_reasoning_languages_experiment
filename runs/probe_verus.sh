#!/usr/bin/env bash
# Verus probe: 20 problems, bare, low effort, Haiku then Sonnet.
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
R="python3 harness/run.py --effort low --max-turns 60 --max-budget-usd 3 --timeout-min 30 --parallel 3 --bench verus --problems problems/probe_verus.txt --condition bare"
$R --model claude-haiku-5-5  --out runs/probe_verus_haiku/
$R --model claude-sonnet-5-5 --out runs/probe_verus_sonnet/
