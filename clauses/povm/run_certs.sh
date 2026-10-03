#!/bin/bash
# exact POVM certificates: build exact data, construct certificate, verify independently
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")/certs"
for d in "$@"; do
  PYTHONPATH=.. python ../exact_povm.py $d > build_d$d.log 2>&1
  PYTHONPATH=.. python ../cert_povm.py $d > cert_d$d.log 2>&1
  python ../verify_povm.py $d > verify_d$d.log 2>&1
done
