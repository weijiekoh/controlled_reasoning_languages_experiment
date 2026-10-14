#!/usr/bin/env bash
# SWE-bench Verified, 48 instances (problems/swe_issue.txt: issue framing; problems/swe_debug.txt: debug framing).
# Each step resumes: runs with result.json are skipped. Needs the eval images (harness/sample_swe.py --pull-mode ipv4,
# running detached) and the egress proxy (harness/egress/up.sh). Steps wait for the images of their own list.
set -a; . /home/user/cot_metalang/.env; set +a
cd /home/user/cot_metalang
H="python3 harness/run.py --bench swe --model claude-haiku-5-5 --effort low --max-turns 50 --max-budget-usd 2 --timeout-min 25 --parallel 6"
S="python3 harness/run.py --bench swe --model claude-sonnet-5-5 --effort low --max-turns 50 --max-budget-usd 4 --timeout-min 25 --parallel 6"
LOG="/tmp/claude-1000/-home-di-cot-metalang/7b73d1d3-5f9f-48a1-8412-6ca1028180d0/scratchpad/pull.log"

have_images() {  # $1 = problem list file; prints missing count
  local have; have=$(docker images --format '{{.Repository}}' | grep sweb.eval | sed 's/.*x86_64\.//; s/_1776_/__/')
  local miss=0; for p in $(grep -v '^#' "$1"); do echo "$have" | grep -qx "$p" || miss=$((miss+1)); done; echo $miss
}
wait_images() {  # $1 = problem list file
  while [ "$(have_images "$1")" -gt 0 ]; do
    echo "$(date '+%H:%M') waiting: $(have_images "$1") images missing for $1 (pull alive: $(pgrep -c -f 'sample_swe.py --pull-mode'))"
    if [ "$(pgrep -c -f 'sample_swe.py --pull-mode')" -eq 0 ]; then nohup setsid python3 harness/sample_swe.py --pull-mode ipv4 >> "$LOG" 2>&1 & fi
    sleep 120
  done
}
probe() {  # $1 = list, $2 = label
  local six; six=$(grep -v '^#' "$1" | head -6 | paste -sd,)
  echo "=== $(date '+%H:%M') probe $2 (Haiku bare, 6 tasks)"
  $H --out runs/swe_haiku/ --condition bare --problems "$six"
  echo "=== $(date '+%H:%M') probe $2 done:"; python3 harness/summarize.py runs/swe_haiku 2>/dev/null | tail -3
}

# Issue framing: images arrive first.
wait_images problems/swe_issue.txt
probe problems/swe_issue.txt issue
$H --out runs/swe_haiku/ --condition bare,cod,jellyfish --problems problems/swe_issue.txt
# Debug framing.
wait_images problems/swe_debug.txt
probe problems/swe_debug.txt debug
$H --out runs/swe_haiku/ --condition bare,cod,jellyfish --problems problems/swe_debug.txt
# Sonnet reference line.
$S --out runs/swe_sonnet/ --condition bare --problems problems/swe_issue.txt
$S --out runs/swe_sonnet/ --condition bare --problems problems/swe_debug.txt
# Analysis.
echo "=== $(date '+%H:%M') analysis"
python3 harness/analyze.py --out analysis/swe --bench swe runs/swe_haiku runs/swe_sonnet
python3 harness/compliance.py runs/swe_haiku runs/swe_sonnet
echo "=== $(date '+%H:%M') session complete"
