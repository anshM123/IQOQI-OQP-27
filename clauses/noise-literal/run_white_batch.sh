#!/bin/bash
# B1 search batch (white state noise, unbalanced PVMs); two sequential streams, logs in logs/
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
if [ "$1" == "A" ]; then
  for D in 2 3 4 5 6 7 8 9; do python white_search.py 3 $D 400 3 1 > logs/white_d3_D$D.log 2>&1; done
  for D in 2 3 4 5 6 7 8; do python white_search.py 4 $D 400 3 1 > logs/white_d4_D$D.log 2>&1; done
else
  for D in 2 3 4 5 6; do python white_search.py 5 $D 400 3 1 > logs/white_d5_D$D.log 2>&1; done
  for D in 2 3 4 5; do python white_search.py 6 $D 400 3 1 > logs/white_d6_D$D.log 2>&1; done
fi
