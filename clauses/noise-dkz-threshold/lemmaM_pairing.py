"""
lemmaM_pairing.py -- numerics for Lemma M (CLAIM_d) via the PAIRING reduction.

CLAIM_d: Q_d(n) = G_d(n)/kappa_d + (1 - 1/kappa_d)/d  (n = 0..d-1),  G_d(n) = 1/(2 d^2 sin^2(pi(4n+1)/(4d))),
kappa_d = I_ME(d)/2, is a strictly positive mixture of the laws (1/4) sum_i delta_{pi_i}, pi a composition of S = d-1
into 4 nonnegative parts.

Pairing reduction (proof in NOTES.md): if pi is a coupling of (Q, Q) supported on T = {x1 + x2 <= S}, positive on T,
whose sum law R(y) = sum_{x1+x2=y} pi(x1,x2) is symmetric (R(y) = R(S-y)), then
   P(x1,x2,x3,x4) = pi(x1,x2) pi(x3,x4) / R(x1+x2)    on compositions (x1+x2+x3+x4 = S)
is a coupling of four copies of Q supported on ALL compositions with positive weights; symmetrising gives CLAIM_d.
This script solves the pairing LP  max eps  s.t.  pi >= eps * Q(x1) Q(x2) on T,  marginals Q,  R symmetric.
"""
import sys
import math
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix


def i_me(d):
    """I_ME(d) = 4/(d(d-1)) sum_{j=1}^{d-1} (d-j)/cos(pi j/(2d))  (closed form; checked below via the mean of Q)."""
    j = np.arange(1, d)
    return 4.0 / (d * (d - 1)) * float(np.sum((d - j) / np.cos(np.pi * j / (2 * d))))


def Q_law(d):
    n = np.arange(d)
    G = 1.0 / (2 * d * d * np.sin(np.pi * (4 * n + 1) / (4 * d)) ** 2)
    kap = i_me(d) / 2
    return G / kap + (1 - 1 / kap) / d, G, kap


def pairing_lp(d, sym=True):
    Q, G, kap = Q_law(d)
    S = d - 1
    cells = [(a, b) for a in range(d) for b in range(d) if a + b <= S and (not sym or a <= b)]
    idx = {c: i for i, c in enumerate(cells)}
    nv = len(cells) + 1               # + eps
    rows = []
    rhs = []
    A = lil_matrix((d + (S + 1) // 2 + 1, nv))
    r = 0
    # marginals: sum_b pi(a,b) = Q(a)   (with symmetric storage: pi(a,b) = pi(b,a))
    for a in range(d):
        for b in range(d):
            if a + b <= S:
                c = (min(a, b), max(a, b)) if sym else (a, b)
                A[r, idx[c]] += 1.0
        rhs.append(Q[a]); r += 1
    # symmetry of R: R(y) - R(S-y) = 0 for y < S/2
    for y in range((S + 1) // 2):
        for a in range(y + 1):
            b = y - a
            c = (min(a, b), max(a, b)) if sym else (a, b)
            A[r, idx[c]] += 1.0
        y2 = S - y
        for a in range(y2 + 1):
            b = y2 - a
            c = (min(a, b), max(a, b)) if sym else (a, b)
            A[r, idx[c]] -= 1.0
        rhs.append(0.0); r += 1
    A = csr_matrix(A[:r])
    # pi(c) - eps * Q(a)Q(b) >= 0  -> -pi + eps*QQ <= 0
    Aub = lil_matrix((len(cells), nv))
    for i, (a, b) in enumerate(cells):
        Aub[i, i] = -1.0
        Aub[i, -1] = Q[a] * Q[b]
    c = np.zeros(nv); c[-1] = -1.0
    res = linprog(c, A_ub=csr_matrix(Aub), b_ub=np.zeros(len(cells)), A_eq=A, b_eq=np.array(rhs),
                  bounds=[(0, None)] * len(cells) + [(None, 1.0)], method="highs")
    return res, Q, cells


if __name__ == "__main__":
    ds = [int(a) for a in sys.argv[1:]] if len(sys.argv) > 1 else [3, 4, 5, 6, 7, 8, 10, 15, 20, 30, 50, 80, 120, 200]
    for d in ds:
        res, Q, cells = pairing_lp(d)
        top = Q[(d + 1) // 2:].sum() if d % 2 == 1 else Q[d // 2:].sum()
        print(f"d={d:4d}  status={res.status}  eps*={(-res.fun if res.status == 0 else float('nan')):.6f}  "
              f"mean-(d-1)/4={Q @ np.arange(d) - (d - 1) / 4:+.2e}  Q(top half)={top:.6f}", flush=True)
