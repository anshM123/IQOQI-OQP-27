#!/bin/bash
# d = 8 certificate with the p-adic (Dixon) exact projection, then independent verification (exact LDL and interval)
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 SOLVER=dixon
cd "$(dirname "$0")/certs" || exit 1
PYTHONPATH=.. python ../cert_povm.py mod 8 > cert_d8.log 2>&1
if [ -f cert_povm_d8.pkl ]; then
  python ../verify_povm.py iv 8 > verify_iv_d8.log 2>&1
  python ../verify_povm.py 8 > verify_d8.log 2>&1
fi
