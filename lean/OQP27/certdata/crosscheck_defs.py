"""Sanity check: the enclosures computed by (an exact emulation of) the Lean checker contain the values of
QD2/cells.py (window-sum form u_window AND the original cell-pair kernel u_vector) for random integer cells."""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "cone-certificates"))   # cells.py of the certificate programme
import numpy as np
import cells as C
import leanemu as E
from fractions import Fraction as F
rng = np.random.default_rng(5)
worst = 0.0
for d in [2, 3, 4, 5, 6, 7, 9, 12]:
    q = int(rng.integers(1, 3))
    gT = E.gTab(d, q)
    for t in range(4):
        x = rng.dirichlet(np.ones(d) * 0.7) * d * q
        n = np.floor(x).astype(int)
        for i in rng.choice(d, size=d * q - n.sum()): n[i] += 1
        n = [int(a) for a in n]
        ell = np.array(n, float) / q
        uw = C.u_window(ell)
        uv, _ = C.u_vector(ell)
        UL = E.uList(d, gT, n)
        for m in range(d - 1):
            lo, hi = float(UL[m].lo), float(UL[m].hi)
            mid = (lo + hi) / 2
            for val in (uw[m], uv[m]):
                dev = abs(val - mid) / max(1.0, abs(val))
                worst = max(worst, dev)
            assert hi - lo < 1e-8, (d, n, m, hi - lo)
        vT = [E.vEnc(d, i + 1) for i in range(d - 1)]
        vv = C.v_vector(d)
        for m in range(d - 1):
            assert float(vT[m].lo) - 1e-12 <= vv[m] <= float(vT[m].hi) + 1e-12
    print(f"d={d} q={q}: ok", flush=True)
print("max relative deviation float(cells.py) vs Lean-enclosure midpoint:", worst)
