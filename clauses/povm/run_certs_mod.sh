#!/bin/bash
# exact POVM certificates with multi-modular projection: build exact data, certificate, independent verification.
# usage: ./run_certs_mod.sh d1 d2 ...   (runs strictly sequentially; one python process at a time)
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 SOLVER=dixon
cd "$(dirname "$0")/certs" || exit 1
for d in "$@"; do
  if [ ! -f exact_povm_d$d.pkl ]; then PYTHONPATH=.. python ../exact_povm.py $d > build_d$d.log 2>&1; fi
  if [ ! -f cert_povm_d$d.pkl ]; then PYTHONPATH=.. python ../cert_povm.py mod $d > cert_d$d.log 2>&1; fi
  python ../verify_povm.py $d > verify_d$d.log 2>&1
done
