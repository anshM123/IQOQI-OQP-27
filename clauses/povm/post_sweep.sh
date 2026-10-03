#!/bin/bash
# runs after the sweep: re-verify d=4 (log), numerical cross-checks d=5,6, see-saw cross-check
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")"
until grep -q "SWEEP DONE" runs/sweep_summary.log 2>/dev/null; do sleep 20; done
cd certs
python ../verify_povm.py 4 > verify_d4.log 2>&1
PYTHONPATH=.. python ../cert_numcheck.py 5 4 > numcheck_d5.log 2>&1
PYTHONPATH=.. python ../cert_numcheck.py 6 3 > numcheck_d6.log 2>&1
cd ..
./seesaw_runs.sh
echo "POST DONE" >> runs/seesaw_summary.log
