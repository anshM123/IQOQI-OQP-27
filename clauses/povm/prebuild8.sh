#!/bin/bash
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")/prebuild8"
PYTHONPATH=.. python ../exact_povm.py 8 > build_d8.log 2>&1
if [ ! -f ../certs/exact_povm_d8.pkl ] && grep -q "kernel dims" build_d8.log; then
  mv build_d8.log ../certs/build_d8.log; mv exact_povm_d8.pkl ../certs/exact_povm_d8.pkl
fi
