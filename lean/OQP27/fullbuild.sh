#!/usr/bin/env bash
# Clean rebuild of every OQP27 file in dependency order (OQP27/BUILD_ORDER.txt); stops at the first failure.
# Run from lean/.  Logs: OQP27/logs/fullbuild/<File>.log, summary OQP27/logs/fullbuild/SUMMARY.log
# Optional argument: a file name from BUILD_ORDER.txt to resume from (the summary is then appended to, not reset).
set -u
out=.lake/build/lib/lean/OQP27
from="${1:-}"
mkdir -p OQP27/logs/fullbuild "$out"
[ -z "$from" ] && : > OQP27/logs/fullbuild/SUMMARY.log
t0=$(date +%s)
skipping=0; [ -n "$from" ] && skipping=1
while read -r f; do
  f="$(printf '%s' "$f" | tr -d '\r')"; [ -z "$f" ] && continue
  if [ $skipping -eq 1 ]; then
    if [ "$f" == "$from" ]; then skipping=0; else continue; fi
  fi
  if [[ "$f" == *Axioms ]]; then
    bash OQP27/leanrun.sh "OQP27/$f.lean" > "OQP27/logs/fullbuild/$f.log" 2>&1
  else
    bash OQP27/leanrun.sh "OQP27/$f.lean" -o "$out/$f.olean" -i "$out/$f.ilean" > "OQP27/logs/fullbuild/$f.log" 2>&1
  fi
  code=$?
  el=$(grep -o "elapsed s: [0-9]*" "OQP27/logs/fullbuild/$f.log" | tail -1)
  echo "$f exit=$code $el" >> OQP27/logs/fullbuild/SUMMARY.log
  if [ $code -ne 0 ]; then echo "FAILED at $f" >> OQP27/logs/fullbuild/SUMMARY.log; exit 1; fi
done < OQP27/BUILD_ORDER.txt
echo "ALL OK; total $(( $(date +%s) - t0 )) s" >> OQP27/logs/fullbuild/SUMMARY.log
