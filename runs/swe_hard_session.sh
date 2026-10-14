#!/usr/bin/env bash
# Harder SWE set (non-django, 48 tasks, issue framing). Waits for the main session, pulls images, runs, analyzes.
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
H="python3 harness/run.py --bench swe --model claude-haiku-5-5 --effort low --max-turns 50 --max-budget-usd 2 --timeout-min 25 --parallel 6"
S="python3 harness/run.py --bench swe --model claude-sonnet-5-5 --effort low --max-turns 50 --max-budget-usd 4 --timeout-min 25 --parallel 6"
LOG="/tmp/claude-1000/-home-di-cot-metalang/7b73d1d3-5f9f-48a1-8412-6ca1028180d0/scratchpad/pull_hard.log"
# Pull once the debug-list pull is done (registry quota is per address per hour).
while [ "$(pgrep -c -f 'sample_swe.py --pull-mode')" -gt 0 ]; do sleep 60; done
echo "=== $(date '+%H:%M') pulling hard-set images (docker mode first, ipv4 fallback)"
python3 harness/sample_swe_hard.py --pull-mode docker --pull-parallel 3 >> "$LOG" 2>&1
python3 harness/sample_swe_hard.py --pull-mode ipv4 --pull-parallel 3 >> "$LOG" 2>&1
missing() { local have; have=$(docker images --format '{{.Repository}}' | grep sweb.eval | sed 's/.*x86_64\.//; s/_1776_/__/'); local m=0; for p in $(cat problems/swe_hard.txt); do echo "$have" | grep -qx "$p" || m=$((m+1)); done; echo $m; }
until [ "$(missing)" -eq 0 ]; do echo "$(date '+%H:%M') hard images missing: $(missing)"; python3 harness/sample_swe_hard.py --pull-mode ipv4 --pull-parallel 2 >> "$LOG" 2>&1; sleep 300; done
# Do not overlap with the main session's agent runs.
while [ "$(pgrep -c -f 'runs/swe_session.sh')" -gt 0 ]; do sleep 60; done
echo "=== $(date '+%H:%M') hard set: Haiku bare,cod,jellyfish"
$H --out runs/swe_haiku/ --condition bare,cod,jellyfish --problems problems/swe_hard.txt
echo "=== $(date '+%H:%M') hard set: Sonnet bare"
$S --out runs/swe_sonnet/ --condition bare --problems problems/swe_hard.txt
echo "=== $(date '+%H:%M') analysis"
python3 harness/analyze.py --out analysis/swe --bench swe runs/swe_haiku runs/swe_sonnet
python3 harness/compliance.py runs/swe_haiku runs/swe_sonnet
echo "=== $(date '+%H:%M') hard session complete"
