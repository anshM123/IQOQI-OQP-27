#!/bin/bash
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")/certs"
for d in 3 4 5 6 7; do python ../verify_povm.py iv $d > verify_iv_d$d.log 2>&1; done
cd ../prebuild9
PYTHONPATH=.. python ../exact_povm.py 9 > build_d9.log 2>&1
if [ ! -f ../certs/exact_povm_d9.pkl ] && grep -q "kernel dims" build_d9.log; then
  mv build_d9.log ../certs/build_d9.log; mv exact_povm_d9.pkl ../certs/exact_povm_d9.pkl
fi
echo SLOT2 DONE > ../certs/slot2_done.flag
