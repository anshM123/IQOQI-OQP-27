"""kappa_mono.py -- rigorous (ia.py) check that kappa_n = 2 - 4 E_G/(n-1) is strictly increasing for 2 <= n <= N,
and that sqrt2 = kappa_2 <= kappa_n < kappa_oo.  (THEOREM.md, Lemma K, proves this for all n >= 2; this script is an interval cross-check.)"""
import sys
import numpy as np
from verify_X import enclosures
from ia import IA
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
prev = None; ok = True
KINF_LO = 1.4849074908430886
for n in range(2, N + 1):
    S, L, G, kap, tk = enclosures(n)
    lo, hi = float(kap.lo), float(kap.hi)
    if prev is not None and not lo > prev:
        ok = False; print("NOT increasing at", n, lo, prev)
    if not hi < KINF_LO:
        ok = False; print("kappa_n >= kappa_oo ?", n)
    prev = hi
    if n in (2, 3, 4, 5, 10, 12, 50, 100, 200, N):
        print(f"n={n}: kappa_n in [{lo:.15f}, {hi:.15f}]", flush=True)
print(f"kappa strictly increasing and < kappa_oo for 2 <= n <= {N}: {ok}")
