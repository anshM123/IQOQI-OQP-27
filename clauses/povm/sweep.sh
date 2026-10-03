#!/bin/bash
# global POVM sweep: d = 3..8, D = 2..2d ; per-(d,D) logs in runs/
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")/runs"
for d in 3 4 5 6 7 8; do
  if [ $d -le 5 ]; then NS=150; else NS=90; fi
  for D in $(seq 2 $((2*d))); do
    python ../povm_search.py $d $D $NS $((1000*d+D)) sweep > sweep_d${d}_D${D}.log 2>&1
    grep "# BEST" sweep_d${d}_D${D}.log >> sweep_summary.log
  done
done
echo "SWEEP DONE" >> sweep_summary.log
