"""
ref_dkz_large.py -- referee: certified LOWER bounds on S^UNI(DKZ_d) for large d with a shift-invariant test factor
(Lemma D; any feasible r gives a valid bound, shift invariance only reduces the constraint check), own code.

  maximise (1/4) sum_xy sum_m Q_xy(m) log r_xy(m)
  s.t.   max_b [r00(b) + r10(b - al)] + max_b [r01(b) + r11(b - al)] <= 4   for every al in Z_d
  (equivalent to: (1/4) sum_xy r_xy(b_y - a_x) <= 1 for every deterministic (a0, a1, b0, b1)).
Certification: r rounded to integers N_xy(m) = round(r * 10^12); exact integer maximum Mint of the constraint;
final test factor r' = N * 4 / Mint; bound = (1/4) sum Q log N + log 4 - log Mint (interval arithmetic, Q from
Lemma 0 in intervals).  Compare: T(mu*) (Lemma Z) must exceed every lower bound; Lemma W(iii) monotonicity
along multiples is visible in the output.
usage: python ref_dkz_large.py d1 d2 ...
"""
import sys
import numpy as np
import cvxpy as cp
from mpmath import iv, mpf

iv.dps = 30
DL = {(0, 0): (1, 4), (0, 1): (3, 4), (1, 0): (-1, 4), (1, 1): (1, 4)}
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]


def Qd(d):
    m = np.arange(d)
    return {L: 1 / (2 * d ** 2 * np.sin(np.pi * (m - DL[L][0] / DL[L][1]) / d) ** 2) for L in LINKS}


def Qd_iv(d):
    out = {}
    for L in LINKS:
        n, den = DL[L]
        out[L] = [1 / (2 * iv.mpf(d) ** 2 * iv.sin(iv.pi * (m - iv.mpf(n) / den) / d) ** 2) for m in range(d)]
    return out


def solve(d):
    Q = Qd(d)
    r = {L: cp.Variable(d) for L in LINKS}
    F = cp.Variable(d)
    G = cp.Variable(d)
    cons = [F + G <= 4]
    # r00(b) + r10(b - al) <= F(al)  for all al, b  ->  stack: for each al, vector over b
    idx = np.arange(d)
    for al in range(d):
        sh = (idx - al) % d
        cons.append(r[(0, 0)] + r[(1, 0)][sh] <= F[al])
        cons.append(r[(0, 1)] + r[(1, 1)][sh] <= G[al])
    obj = sum(Q[L] @ cp.log(r[L]) for L in LINKS) / 4
    pr = cp.Problem(cp.Maximize(obj), cons)
    pr.solve(solver=cp.CLARABEL, tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11, max_iter=300)
    return pr.value, {L: np.maximum(r[L].value, 1e-300) for L in LINKS}


def certify(d, r):
    SC = 10 ** 12
    N = {L: [int(round(v * SC)) for v in r[L]] for L in LINKS}
    assert all(v > 0 for L in LINKS for v in N[L])
    best = 0
    for al in range(d):
        f = max(N[(0, 0)][b] + N[(1, 0)][(b - al) % d] for b in range(d))
        g = max(N[(0, 1)][b] + N[(1, 1)][(b - al) % d] for b in range(d))
        best = max(best, f + g)
    Qi = Qd_iv(d)
    L_ = iv.mpf(0)
    for L in LINKS:
        for m in range(d):
            L_ += Qi[L][m] * iv.log(iv.mpf(N[L][m]))
    L_ = L_ / 4 + iv.log(iv.mpf(4)) - iv.log(iv.mpf(best))
    return mpf((L_ / iv.log(iv.mpf(2))).a), best / SC


if __name__ == "__main__":
    T = 0.068780260568
    for d in map(int, sys.argv[1:]):
        val, r = solve(d)
        lo, M = certify(d, r)
        print(f"d={d:4d}: float dual {val / np.log(2):.12f} bits; CERTIFIED S^UNI(DKZ_d) >= {float(lo):.12f} bits "
              f"(exact constraint max before scaling {M:.12f}/4); below T(mu*) = {T}: {float(lo) < T}", flush=True)
