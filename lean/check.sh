#!/usr/bin/env bash
# Check the whole formalisation from scratch, one file at a time, in dependency order.
#
# Run from this folder (lean/), after fetching the prebuilt Mathlib of the pinned revision:
#     lake exe cache get
#     bash check.sh
# Each file is elaborated and kernel-checked by `lake env lean`; its .olean goes to .lake/build so that later files can
# import it.  Logs go to logs_check/.  The whole run takes about two hours on a laptop; the certificate files CertD18,
# CertD19 and CertD20 need up to about 8 GB of memory, and CertLP takes about 45 minutes.
# Optional argument: a file of OQP27/BUILD_ORDER.txt to resume from.
set -uo pipefail
out=.lake/build/lib/lean
from="${1:-}"
mkdir -p "$out/OQP27" "$out/CGLMPRigidity" logs_check
t_all=$(date +%s)

check_file() {  # $1 = module path without .lean, e.g. OQP27/Main
  local f="$1" log="logs_check/${1//\//_}.log" t0 code
  t0=$(date +%s)
  if [[ "$f" == *Axioms ]]; then
    lake env lean "$f.lean" > "$log" 2>&1
  else
    lake env lean -o "$out/$f.olean" -i "$out/$f.ilean" "$f.lean" > "$log" 2>&1
  fi
  code=$?
  printf '%-34s exit=%d %6ds\n' "$f" "$code" "$(( $(date +%s) - t0 ))"
  if [ $code -ne 0 ]; then echo "FAILED: $f (see $log)"; exit 1; fi
}

if [ -z "$from" ]; then
  for f in CGLMPRigidity/Rigidity CGLMPRigidity/Links CGLMPRigidity/Model; do check_file "$f"; done
fi
skipping=0; [ -n "$from" ] && skipping=1
while read -r f; do
  f="$(printf '%s' "$f" | tr -d '\r')"; [ -z "$f" ] && continue
  if [ $skipping -eq 1 ]; then
    if [ "$f" == "$from" ]; then skipping=0; else continue; fi
  fi
  check_file "OQP27/$f"
done < OQP27/BUILD_ORDER.txt
echo "all files checked in $(( $(date +%s) - t_all )) s"

echo "== forbidden tokens in code (comments and strings skipped):"
python3 scan_forbidden.py OQP27 CGLMPRigidity 2>/dev/null || python scan_forbidden.py OQP27 CGLMPRigidity || exit 1

echo "== axioms used by the main theorems (logs_check/OQP27_MainAxioms.log):"
[ -s logs_check/OQP27_MainAxioms.log ] || { echo "MISSING: logs_check/OQP27_MainAxioms.log"; exit 1; }
grep "depends on axioms" logs_check/OQP27_MainAxioms.log
n=$(cat logs_check/OQP27_*Axioms.log | grep -c "depends on axioms")
bad=$(cat logs_check/OQP27_*Axioms.log | grep "depends on axioms" | sed -e 's/^.*depends on axioms: \[//' -e 's/\].*$//' \
      | tr ',' '\n' | tr -d ' \r' | grep -v -x -E 'propext|Classical[.]choice|Quot[.]sound' | sort -u)
if [ -n "$bad" ]; then echo "UNEXPECTED AXIOMS: $bad"; exit 1; fi
if [ "$n" -lt 250 ]; then echo "TOO FEW AUDITED THEOREMS: $n (expected 265)"; exit 1; fi
echo "OK: all $n audited theorems (files *Axioms.lean) use only propext, Classical.choice, Quot.sound"
