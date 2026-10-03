#!/bin/bash
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")"
for d in 6 7 8; do
  python analyze_dual.py $d 1,3 adj > sdp_logs/analyze_adj_d$d.log 2>&1
done
