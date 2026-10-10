"""
lemmaM_core.py -- explicit candidate construction for Lemma M (CLAIM_d) via the pairing + core lemmas (NOTES.md Sec. 5).
Numerics only.

Core: pi_I = nu (x) nu + eta * (Q (x) Q) on the interior I = {x1, x2 >= 1, x1 + x2 <= S-1}, nu supported on
[1, L], L = floor((S-1)/2).  With F = m_I - R_I/2 the core lemma needs F(y) - F(S-y) = D(y) := Q(y) - Q(S-y),
1 <= y <= S-1, and m_I < Q.  For the nu (x) nu part: F_nu(y) = nu(y) N - (nu*nu)(y)/2 (y <= L), F_nu(y) = -(nu*nu)(y)/2
(y > L), N = sum nu.  So nu solves, for y = 1..L,
     nu(y) N = D(y) - Fa_eta(y) + (nu*nu)(y)/2 - (nu*nu)(S-y)/2,     Fa_eta = antisymmetric part of F_eta,
a fixed point (outer: N; inner: the recursion in y).  Then the edges / antithetic cells / (0,0) are completed as in
the core lemma, and the full pairing pi is checked: pi > 0 on T, marginals Q, sum law symmetric.
"""
import sys
import math
import numpy as np
from lemmaM_pairing import Q_law


def build(d, eta=1e-3, iters=400):
    Q, G, kap = Q_law(d)
    S = d - 1
    L = (S - 1) // 2
    D = Q - Q[::-1]                                   # D(y) = Q(y) - Q(S-y)
    # eta-part: eta * Q(x1)Q(x2) on the interior
    I = np.zeros((d, d), bool)
    for x1 in range(1, d):
        for x2 in range(1, d):
            if x1 + x2 <= S - 1:
                I[x1, x2] = True
    Pe = eta * np.outer(Q, Q) * I
    m_e = Pe.sum(1)
    R_e = np.array([sum(Pe[a, y - a] for a in range(max(0, y - S), min(y, S) + 1) if 0 <= y - a <= S) for y in range(d)])
    F_e = m_e - R_e / 2
    Fa_e = F_e - F_e[::-1]
    target = D - Fa_e
    nu = np.zeros(d)
    nu[1:L + 1] = np.maximum(target[1:L + 1], 0) / 0.2
    for it in range(iters):
        N = nu.sum()
        conv = np.convolve(nu, nu)[:2 * d]
        new = np.zeros(d)
        for y in range(1, L + 1):
            new[y] = (target[y] + conv[y] / 2 - conv[S - y] / 2) / N
        if np.max(np.abs(new - nu)) < 1e-16:
            nu = new
            break
        nu = 0.5 * nu + 0.5 * new
    pi = np.outer(nu, nu) * I + Pe
    # core checks
    m_I = pi.sum(1)
    R_I = np.array([sum(pi[a, y - a] for a in range(0, y + 1) if y - a < d) for y in range(d)])
    F = m_I - R_I / 2
    res_sym = max(abs((F[y] - F[S - y]) - D[y]) for y in range(1, S))
    rho = Q - m_I
    # completion
    A = np.zeros(d); E = np.zeros(d)
    for x in range(1, S):
        A[x] = 0.5 * min(rho[x], rho[S - x])
    for x in range(1, S):
        E[x] = rho[x] - A[x]
    E[S] = Q[S]
    z = Q[0] - E[1:].sum()
    full = pi.copy()
    for x in range(1, d):
        full[x, 0] += E[x]; full[0, x] += E[x]
    for x in range(1, S):
        full[x, S - x] += A[x]
    full[0, 0] += z
    # full checks
    T = np.array([[x1 + x2 <= S for x2 in range(d)] for x1 in range(d)])
    marg = np.abs(full.sum(1) - Q).max()
    R = np.array([sum(full[a, y - a] for a in range(0, y + 1)) for y in range(d)])
    sym = np.abs(R - R[::-1]).max()
    rel = (full[T] / np.outer(Q, Q)[T]).min()
    return dict(d=d, N=nu.sum(), nu_min=nu[1:L + 1].min(), res_core=res_sym, rho_min=(rho[1:S] / Q[1:S]).min(),
                z=z, marg=marg, sym=sym, rel_min=rel, outside=np.abs(full[~T]).max(), symm=np.abs(full - full.T).max())


if __name__ == "__main__":
    ds = [int(a) for a in sys.argv[1:]] or [5, 8, 12, 20, 40, 80, 160, 320, 640]
    for d in ds:
        r = build(d)
        print(f"d={d:5d} N={r['N']:.6f} min nu={r['nu_min']:.3e} core residual={r['res_core']:.1e} "
              f"min (Q-m_I)/Q={r['rho_min']:.4f} z={r['z']:.4f} | marginal err {r['marg']:.1e} sym err {r['sym']:.1e} "
              f"min pi/(Q Q) on T = {r['rel_min']:.3e} (outside T {r['outside']:.0e}, asym {r['symm']:.0e})", flush=True)
