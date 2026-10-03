#!/bin/bash
# d=8 certificate in parallel with the running d=7 one; verify each as soon as its certificate exists
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd "$(dirname "$0")/certs" || exit 1
( PYTHONPATH=.. python ../cert_povm.py mod 8 > cert_d8.log 2>&1 ) &
until grep -qE "CERTIFICATE|Traceback|Error|assert" cert_d7.log 2>/dev/null; do sleep 20; done
[ -f cert_povm_d7.pkl ] && python ../verify_povm.py 7 > verify_d7.log 2>&1
until grep -qE "CERTIFICATE|Traceback|Error|assert" cert_d8.log 2>/dev/null; do sleep 20; done
[ -f cert_povm_d8.pkl ] && python ../verify_povm.py 8 > verify_d8.log 2>&1
