"""lb_general.py -- Theorem LB with an ARBITRARY strategy T on the extra m-dim block (not only classical blocks).
Mode A only needs the C-block remainder to be local: it is proportional to v_T P_T + (1 - v_T) u with
v_T = v0/(v0 + (1 - v0) m/d), so the law v_c = v0 should hold iff (roughly) v_c(T) >= v_T (and v_c <= v0 always).
Checks with the full LP for random T (Haar bases on the block) of varying nonlocality.  Numerics only."""
import sys, os
import numpy as np
from scipy.linalg import block_diag
from scipy.stats import unitary_group
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import dkz_bases, behaviour, vc, ime

kap = lambda n: ime(n) / 2
rng = np.random.default_rng(11)
for (blocks, m, trials) in (((3,), 2, 6), ((2, 2), 2, 4), ((4,), 2, 4), ((3,), 3, 3)):
    K = sum(blocks); d = K + m
    S = sum(k * kap(k) for k in blocks)
    v0 = (2 * d - K) / (d * S / K + m)
    vT = v0 / (v0 + (1 - v0) * m / d)
    for t in range(trials):
        # T: Alice bases U0, U1, Bob bases V0, V1 on C^m; interpolate between classical (eps=0) and Haar (eps=1)
        eps = [0.15, 0.35, 0.6, 1.0, 0.25, 0.8][t % 6]
        H = [unitary_group.rvs(m, random_state=rng) for _ in range(4)]
        from scipy.linalg import logm, expm
        def toward(Uh):
            L = logm(Uh); return expm(eps * L)
        TA = [np.eye(m), toward(H[0])]; TB = [np.eye(m), toward(H[1])]
        As, Fs = [], []
        for k in blocks:
            A, F = dkz_bases(k); As.append(A); Fs.append(F)
        A = np.array([block_diag(*([a[x] for a in As] + [TA[x]])) for x in range(2)])
        F = np.array([block_diag(*([f[y] for f in Fs] + [TB[y]])) for y in range(2)])
        vcT = vc(behaviour(np.array(TA), np.array(TB)))
        v = vc(behaviour(A, F))
        print(f"blocks {blocks} + T_{m} (eps {eps}): v_c(T) = {vcT:.6f} (threshold v_T = {vT:.6f}) -> "
              f"v_c = {v:.9f}, v0 = {v0:.9f}, diff {v - v0:+.2e}", flush=True)
