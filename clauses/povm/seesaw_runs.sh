#!/bin/bash
# independent see-saw cross-check (SDP best responses) for small (d, D)
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")/runs"
for dD in "3 2" "3 3" "3 4" "3 6" "4 2" "4 3" "4 4" "4 5" "4 8" "5 3" "5 5" "5 6"; do
  set -- $dD
  python ../seesaw_check.py search $1 $2 6 $((77*$1+$2)) > seesaw_d$1_D$2.log 2>&1
  grep "SEESAW BEST" seesaw_d$1_D$2.log >> seesaw_summary.log
done
python ../seesaw_check.py gaps best_d*_sweep.npz > gaps_all.log 2>&1
echo "SEESAW DONE" >> seesaw_summary.log
