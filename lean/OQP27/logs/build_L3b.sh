#!/usr/bin/env bash
# Build the module L3b files in dependency order (run from lean/); logs go to OQP27/logs/<File>.log.
# Without arguments, builds all files of module L3b.  StripRIChain also needs the oleans of module L3a
# (StripTheorem2, StripSkeleton) and of module L1 (Skeleton).
set -u
mkdir -p .lake/build/lib/lean/OQP27 OQP27/logs
FILES="$*"
if [ -z "$FILES" ]; then
  FILES="StripJensen StripPencil StripSlice StripBounds StripBMV StripRIContour StripRIPencil StripRISums StripRISmooth StripRIEnds StripRIBoundary StripRIAssembly StripRIMain StripRIChain StripAxiomsL3b"
fi
for f in $FILES; do
  bash OQP27/leanrun.sh OQP27/$f.lean -o .lake/build/lib/lean/OQP27/$f.olean -i .lake/build/lib/lean/OQP27/$f.ilean \
    > OQP27/logs/$f.log 2>&1
  echo "$f: $(tail -1 OQP27/logs/$f.log)"
done
