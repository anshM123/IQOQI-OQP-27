#!/bin/bash
# usage: start_cert.sh n_workers [d0 d1]
# starts n_workers background workers (nohup bash run_cert.sh w n d0 d1) and appends their PIDs (MSYS pid and Windows pid) to
# logs/run_cert_pids.txt.  To stop: kill only these recorded PIDs (and their current verify_cert.py child).
cd "$(dirname "$0")"
n=$1; d0=${2:-201}; d1=${3:-2000}
for w in $(seq 0 $((n - 1))); do
  nohup bash run_cert.sh $w $n $d0 $d1 > /dev/null 2>&1 &
  pid=$!
  winpid=$(cat /proc/$pid/winpid 2>/dev/null)
  echo "worker=$w n=$n range=$d0..$d1 pid=$pid winpid=$winpid started=$(date '+%Y-%m-%dT%H:%M:%S')" >> logs/run_cert_pids.txt
done
