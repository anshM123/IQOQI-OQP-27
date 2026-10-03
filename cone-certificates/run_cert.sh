#!/bin/bash
# usage: run_cert.sh worker_index n_workers [d0 d1]
# runs verify_cert.py for the d in [d0, d1] (default 201..2000) with d % n_workers == worker_index, skipping every d that already
# has logs/cert_g_d{d}.json; one summary line per d in logs/run_cert_w{worker}.log (tracebacks: logs/cert_g_err_d{d}.txt)
cd "$(dirname "$0")"
w=$1; n=$2; d0=${3:-201}; d1=${4:-2000}
PY=${PY:-python3}
for d in $(seq $d0 $d1); do
  if [ $((d % n)) -ne $w ]; then continue; fi
  if [ -f logs/cert_g_d$d.json ]; then continue; fi
  timeout 7200 "$PY" verify_cert.py $d 2>&1 | tail -1 >> logs/run_cert_w$w.log
done
echo "worker $w done" >> logs/run_cert_w$w.log
