#!/usr/bin/env bash
# Memory-aware, concurrency-limited Lean runner for the OQP27 formalisation.
# Usage (from lean/):  bash OQP27/leanrun.sh OQP27/File.lean [-o out.olean -i out.ilean]
# At most N Lean processes run at once (N = first number in OQP27/.slots, default 3; lock slots in OQP27/.locks),
# and a slot is taken only when at least 5 GB of physical memory is free.  Prints waiting and elapsed time.
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
lockdir="OQP27/.locks"; mkdir -p "$lockdir"
start=$(date +%s); slot=""; free=0
while [ -z "$slot" ]; do
  free=$(powershell -NoProfile -Command "[int]((Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory/1024)" 2>/dev/null | tr -dc '0-9')
  free=${free:-0}
  nslots=$(tr -dc '0-9' < OQP27/.slots 2>/dev/null); nslots=${nslots:-3}
  if [ "$free" -ge 5000 ]; then
    for s in $(seq 1 "$nslots"); do
      if mkdir "$lockdir/slot$s" 2>/dev/null; then slot=$s; break; fi
    done
  fi
  [ -z "$slot" ] && sleep 20
done
trap 'rmdir "$lockdir/slot$slot" 2>/dev/null' EXIT
echo "waited $(( $(date +%s) - start ))s; free MB at start: $free; slot $slot"
t0=$(date +%s)
lake env lean "$@"
code=$?
echo "exit code: $code; elapsed s: $(( $(date +%s) - t0 ))"
exit $code
