"""ds_template.py -- Theorem DS template: for DKZ_k (+) DKZ_m check Z_i >= 0, phi_i >= 0 and CLAIM(phi_i) by LP
(phi_i = all four 1-marginals of a law on compositions of d_i - 1 into 4 parts), and report margins.
usage: python ds_template.py kmax"""
import sys, itertools, numpy as np
from scipy.optimize import linprog

def ime(d):
    j = np.arange(1, d); return 4.0 / (d * (d - 1)) * np.sum((d - j) / np.cos(np.pi * j / (2 * d)))

def G(d):
    n = np.arange(d); return 1.0 / (2 * d * d * np.sin(np.pi * (4 * n + 1) / (4 * d)) ** 2)

def claim_lp(phi):
    """max t s.t. exists law on compositions with all four marginals = phi and every composition weight >= t."""
    S = len(phi) - 1
    comps = [c for c in itertools.product(range(S + 1), repeat=4) if sum(c) == S]
    nC = len(comps)
    A = np.zeros((4 * (S + 1), nC + 1)); b = np.zeros(4 * (S + 1))
    for j, c in enumerate(comps):
        for i in range(4):
            A[i * (S + 1) + c[i], j] = 1.0
    for i in range(4):
        b[i * (S + 1):(i + 1) * (S + 1)] = phi
    # variables w_c = t + s_c, s_c >= 0 : A (t 1 + s) = b
    Aeq = np.hstack([A[:, :nC], A[:, :nC].sum(axis=1, keepdims=True)])
    c = np.zeros(nC + 1); c[-1] = -1.0
    res = linprog(c, A_eq=Aeq, b_eq=b, bounds=[(0, None)] * nC + [(None, None)], method='highs')
    return (res.x[-1] if res.status == 0 else -np.inf), nC

if __name__ == '__main__':
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    kap = {j: ime(j) / 2 for j in range(2, kmax + 1)}
    worst = np.inf
    for k in range(2, kmax + 1):
        for m in range(2, k + 1):
            d = k + m
            v = d / (k * kap[k] + m * kap[m])
            out = []
            for di in (k, m):
                Zi = (v * di / d) * (kap[di] - 1) - (1 - v) * di * di / d ** 2
                g = G(di)
                q = v * di / d * g + (1 - v) * di / d ** 2
                q[0] -= Zi
                qi = q.sum(); phi = q / qi
                mean_err = phi @ np.arange(di) - (di - 1) / 4
                t, nC = claim_lp(phi)
                out.append((di, Zi, phi.min(), mean_err, t * nC))
                worst = min(worst, t * nC)
            print(f"k={k:2d} m={m:2d} d={d:2d} v_ds={v:.7f} v*(d)={2/ime(d):.7f} | " +
                  " | ".join(f"blk{di}: Z={Zi:.4f} min phi={pm:.4f} meanerr={me:.1e} CLAIM min weight*#comps={tw:.4f}"
                             for (di, Zi, pm, me, tw) in out), flush=True)
    print("worst normalised CLAIM margin:", worst)
