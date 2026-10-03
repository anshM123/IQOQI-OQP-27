"""
zmodel.py -- numerical construction of an explicit local model for the d -> infinity limit of DKZ
(outcomes in Z), used to bound S(DKZ_d) for all d at once (see THEOREM.md).

Limit correlation: link (x,y) difference m = b_y - a_x has law Q_xy(m) = f(m - delta_xy), f(t) = 1/(2 pi^2 t^2),
delta = (00: 1/4, 01: 3/4, 10: -1/4, 11: 1/4).
Z-local model (a0 = 0):  a = a1 - a0, b0, b1 integers;
   P00 = law(b0), P10 = law(b0 - a), P01 = law(b1), P11 = law(b1 - a).
Model = window part pi0(a,b0), pi1(a,b1) for |a| <= A, |b| <= B (common a-marginal), plus a tail for |a| > A:
   mu(a) = t / (a^2 - 1/4)  (sum_{a > A} = t/(A + 1/2) exactly),
   given a: b0 in {0, a} w.p. 1/2 each, b1 in {1, a} w.p. 1/2 each.
Objective (1/4) sum_xy sum_m Q log(Q/P), truncated at |m| <= M2 (numerical only).
usage: python zmodel.py A B M2 [out.npz]
"""
import sys
import numpy as np
import cvxpy as cp

DELTA = {(0, 0): 0.25, (0, 1): 0.75, (1, 0): -0.25, (1, 1): 0.25}
LOG2 = np.log(2)


def Qz(m, dl):
    return 1.0 / (2 * np.pi ** 2 * (m - dl) ** 2)


def tail_link_contrib(m, A, xy):
    """per unit t: contribution of the tail family to P_xy(m) at integer array m (excluding the
    'near' atoms, which are handled separately).  mu(a)=1/(a^2-1/4) for |a|>A."""
    def mu(a):
        a = np.asarray(a, float)
        out = 1.0 / (a ** 2 - 0.25)
        out[np.abs(a) <= A] = 0.0
        return out
    if xy == (0, 0):      # b0 = a -> L00 = a
        return 0.5 * mu(m)
    if xy == (1, 0):      # b0 = 0 -> L10 = -a
        return 0.5 * mu(-m)
    if xy == (0, 1):      # b1 = a -> L01 = a
        return 0.5 * mu(m)
    if xy == (1, 1):      # b1 = 1 -> L11 = 1 - a
        return 0.5 * mu(1 - m)


def near_atoms(xy):
    """value of the link for the 'near' choice: (00: b0=0 -> 0), (10: b0=a -> 0), (01: b1=1 -> 1), (11: b1=a -> 0)"""
    return {(0, 0): 0, (1, 0): 0, (0, 1): 1, (1, 1): 0}[xy]


def build(A, B, M2):
    na, nb = 2 * A + 1, 2 * B + 1
    av = np.arange(-A, A + 1)
    bv = np.arange(-B, B + 1)
    ms = np.arange(-M2, M2 + 1)
    idx = {m: i for i, m in enumerate(ms)}
    # sparse maps from pi (flattened a-major) to link marginals over ms
    import scipy.sparse as sp
    rows_b, rows_bma, cols = [], [], []
    for i, a in enumerate(av):
        for j, b in enumerate(bv):
            cols.append(i * nb + j)
            rows_b.append(idx[b])
            rows_bma.append(idx[b - a])
    n = na * nb
    Mb = sp.csr_matrix((np.ones(n), (rows_b, cols)), shape=(len(ms), n))
    Mbma = sp.csr_matrix((np.ones(n), (rows_bma, cols)), shape=(len(ms), n))
    return av, bv, ms, Mb, Mbma


def solve(A, B, M2, verbose=False):
    av, bv, ms, Mb, Mbma = build(A, B, M2)
    na, nb = len(av), len(bv)
    p0 = cp.Variable(na * nb, nonneg=True)
    p1 = cp.Variable(na * nb, nonneg=True)
    t = cp.Variable(nonneg=True)
    tail_mass_per_t = 2.0 / (A + 0.5)
    # a-marginals
    import scipy.sparse as sp
    Ma = sp.kron(sp.eye(na), np.ones((1, nb)))
    cons = [Ma @ p0 == Ma @ p1, cp.sum(p0) + t * tail_mass_per_t == 1]
    obj = 0
    for xy in DELTA:
        Q = Qz(ms, DELTA[xy])
        lin = Mb @ (p0 if xy[1] == 0 else p1) if xy[0] == 0 else Mbma @ (p0 if xy[1] == 0 else p1)
        tail = tail_link_contrib(ms, A, xy)
        near = np.zeros(len(ms))
        near[np.where(ms == near_atoms(xy))[0][0]] = 0.5 * tail_mass_per_t
        P = lin + t * (tail + near)
        obj = obj + 0.25 * cp.sum(cp.rel_entr(Q, P))
    prob = cp.Problem(cp.Minimize(obj), cons)
    prob.solve(solver="CLARABEL", verbose=verbose)
    return prob.value, p0.value.reshape(na, nb), p1.value.reshape(na, nb), t.value, av, bv


if __name__ == "__main__":
    A, B, M2 = map(int, sys.argv[1:4])
    val, p0, p1, t, av, bv = solve(A, B, M2)
    # crude remainder estimate beyond M2 (numerical only): tails P ~ t pi^2-ratio
    print(f"A={A} B={B} M2={M2}: objective {val / LOG2:.12f} bits  t={t:.6f}  t*pi^2={t*np.pi**2:.6f}  "
          f"window mass {p0.sum():.6f}", flush=True)
    if len(sys.argv) > 4:
        np.savez(sys.argv[4], p0=p0, p1=p1, t=t, A=A, B=B, M2=M2, av=av, bv=bv)
