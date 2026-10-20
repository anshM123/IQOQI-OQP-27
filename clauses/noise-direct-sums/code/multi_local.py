"""v_c of DKZ_{k1} (+) ... (+) DKZ_{kr} (+) L_m (local block of size m >= 1): data for guessing the general law."""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import vc, behaviour, dkz_bases, ime   # noqa: E402
from scipy.linalg import block_diag


def build(blocks, m):
    As, Fs = [], []
    for k in blocks:
        A, F = dkz_bases(k); As.append(A); Fs.append(F)
    A = np.array([block_diag(*([a[x] for a in As] + ([np.eye(m)] if m else []))) for x in range(2)])
    F = np.array([block_diag(*([f[y] for f in Fs] + ([np.eye(m)] if m else []))) for y in range(2)])
    return A, F


kap = lambda k: ime(k) / 2
for blocks, m in (((2, 2), 1), ((3, 2), 1), ((2, 2), 2), ((3, 3), 1), ((4, 2), 1), ((3, 2), 2), ((2, 2, 2), 1)):
    A, F = build(blocks, m)
    d = sum(blocks) + m
    v = vc(behaviour(A, F))
    avg = (sum(k * kap(k) for k in blocks) + m) / d          # naive averaging with kappa_1 = 1
    print(f"blocks {blocks} + L_{m}: d={d}  R = {1/v:.9f}  naive avg {avg:.9f}  kappa_d {kap(d):.6f}", flush=True)
