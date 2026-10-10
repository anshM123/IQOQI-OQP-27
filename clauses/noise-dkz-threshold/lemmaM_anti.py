"""
lemmaM_anti.py -- "near-antithetic" core for Lemma M (numerics).

Core: for y = 1..L (L = floor((S-1)/2)) put weight w_y on every interior cell (t, S-y-t), t = 1..S-y-1 (sum S-y),
plus eta * Q(x1)Q(x2) on the interior cells with sum <= S-L-1 (eta = 0.01/d^2).  For family y:  F_y = w_y 1_[1,S-y-1] - (S-y-1) w_y delta_{S-y} / 2, so on
the lower half its antisymmetric part is  w_y 1_[1,y] + (S-y-1) w_y delta_y / 2.  The core equation F^a = D
(D(z) = Q(z) - Q(S-z)) is therefore TRIANGULAR:
      w_z = 2 (Dt(z) - sum_{y > z} w_y) / (S - z + 1),    z = L, L-1, ..., 1,    Dt = D - (eta part)^a.
Checks: w > 0 (ratio  sum_{y>z} w_y / Dt(z) < 1), usage m_I < Q, and the completed pairing (edges, antithetic cells,
(0,0)) is a strictly positive coupling with symmetric sum law.
"""
import sys
import numpy as np
from lemmaM_pairing import Q_law


def run(d, eta=None, full_check=True):
    Q, G, kap = Q_law(d)
    S = d - 1
    L = (S - 1) // 2
    D = Q - Q[::-1]
    x = np.arange(d)
    if eta is None:
        eta = 0.01 / d ** 2
    # regulariser only on interior cells NOT covered by the families (sums 2 .. S-L-1)
    Iint = (np.add.outer(x, x) <= S - L - 1) & (np.outer(x, x) > 0)
    Pe = eta * np.outer(Q, Q) * Iint
    m_e = Pe.sum(1)
    R_e = np.array([np.trace(np.fliplr(Pe), offset=(d - 1) - y) for y in range(d)])
    F_e = m_e - R_e / 2
    Dt = D - (F_e - F_e[::-1])
    w = np.zeros(d)
    tail = 0.0
    ratio = 0.0
    for z in range(L, 0, -1):
        ratio = max(ratio, tail / Dt[z]) if Dt[z] > 0 else float("inf")
        w[z] = 2 * (Dt[z] - tail) / (S - z + 1)
        tail += w[z]
    # core matrix
    pi = Pe.copy()
    for y in range(1, L + 1):
        for t in range(1, S - y):
            pi[t, S - y - t] += w[y]
    m_I = pi.sum(1)
    R_I = np.array([np.trace(np.fliplr(pi), offset=(d - 1) - yy) for yy in range(d)])
    F = m_I - R_I / 2
    res = max(abs((F[z] - F[S - z]) - D[z]) for z in range(1, S)) if S > 1 else 0.0
    usage = (m_I[1:S] / Q[1:S]).max() if S > 1 else 0.0
    out = dict(d=d, wmin=w[1:L + 1].min() if L >= 1 else float("nan"), ratio=ratio, res=res, usage=usage)
    if full_check:
        rho = Q - m_I
        A = np.zeros(d); E = np.zeros(d)
        for t in range(1, S):
            A[t] = 0.5 * min(rho[t], rho[S - t])
            E[t] = rho[t] - A[t]
        E[S] = Q[S]
        z0 = Q[0] - E[1:].sum()
        full = pi.copy()
        for t in range(1, d):
            full[t, 0] += E[t]; full[0, t] += E[t]
        for t in range(1, S):
            full[t, S - t] += A[t]
        full[0, 0] += z0
        T = np.add.outer(x, x) <= S
        R = np.array([np.trace(np.fliplr(full), offset=(d - 1) - yy) for yy in range(d)])
        out.update(z=z0, marg=np.abs(full.sum(1) - Q).max(), sym=np.abs(R - R[::-1]).max(),
                   relmin=(full[T] / np.outer(Q, Q)[T]).min(), outside=np.abs(full[~T]).max(),
                   asym=np.abs(full - full.T).max())
    return out


if __name__ == "__main__":
    ds = [int(a) for a in sys.argv[1:]] or [4, 5, 6, 8, 12, 20, 40, 80, 160, 320, 640, 1280]
    for d in ds:
        r = run(d, full_check=(d <= 1500))
        s = (f"d={d:5d}  min w={r['wmin']:.3e}  max tail/Dt={r['ratio']:.4f}  core residual={r['res']:.1e}  "
             f"max usage m_I/Q={r['usage']:.4f}")
        if 'z' in r:
            s += (f"  | z={r['z']:.4f} marg err {r['marg']:.1e} sym err {r['sym']:.1e} "
                  f"min pi/(QQ) on T {r['relmin']:.2e} outside {r['outside']:.0e} asym {r['asym']:.0e}")
        print(s, flush=True)
