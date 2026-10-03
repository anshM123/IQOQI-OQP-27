"""
dkz_limit.py -- numerical KL strength (uniform settings) of DKZ_D on Phi_D for large D, via the
link-marginal reduction.

For a shift-invariant correlation q(a,b|x,y) = Q_xy(b-a)/D the strength is
   S = min over local shift-invariant p of (1/4) sum_xy D(Q_xy || P_xy),
and a shift-invariant local model is a law of (a1-a0, b0-a0, b1-a0) =: (a, b0, b1); its link marginals are
   P00 = law(b0), P10 = law(b0 - a), P01 = law(b1), P11 = law(b1 - a).
Dual (test factor) form:  max (1/4) sum Q log r  s.t.  for all a:
   max_b [r00(b) + r10(b-a)] + max_b [r01(b) + r11(b-a)] <= 4.
DKZ:  Q_xy(m) = 1 / (2 D^2 sin^2(pi (m - delta_xy)/D)),  delta = (00: 1/4, 01: 3/4, 10: -1/4, 11: 1/4).
usage: python dkz_limit.py D1 D2 ...
"""
import sys
import numpy as np
import cvxpy as cp

DELTA = {(0, 0): 0.25, (0, 1): 0.75, (1, 0): -0.25, (1, 1): 0.25}
LOG2 = np.log(2)


def dkz_Q(D):
    m = np.arange(D)
    return {k: 1.0 / (2 * D ** 2 * np.sin(np.pi * (m - dl) / D) ** 2) for k, dl in DELTA.items()}


def strength_dual(Q, D, solver="CLARABEL"):
    r = {k: cp.Variable(D, pos=True) for k in Q}
    F = cp.Variable(D)
    G = cp.Variable(D)
    A, B = np.meshgrid(np.arange(D), np.arange(D), indexing="ij")
    A = A.ravel()
    B = B.ravel()
    BmA = (B - A) % D
    cons = [r[(0, 0)][B] + r[(1, 0)][BmA] <= F[A],
            r[(0, 1)][B] + r[(1, 1)][BmA] <= G[A],
            F + G <= 4]
    obj = sum(0.25 * Q[k] @ cp.log(r[k]) for k in Q)
    prob = cp.Problem(cp.Maximize(obj), cons)
    prob.solve(solver=solver)
    return prob.value, {k: r[k].value for k in r}, prob


def strength_primal(Q, D, solver="CLARABEL"):
    """min over pi0(a,b0), pi1(a,b1) >= 0 with equal a-marginals, total mass 1."""
    p0 = cp.Variable((D, D), nonneg=True)
    p1 = cp.Variable((D, D), nonneg=True)
    cons = [cp.sum(p0, axis=1) == cp.sum(p1, axis=1), cp.sum(p0) == 1]
    # link marginals
    a = np.arange(D)
    P00 = cp.sum(p0, axis=0)
    P01 = cp.sum(p1, axis=0)
    # P10(m) = sum_a p0(a, m + a)
    S = np.zeros((D * D, D))
    for aa in range(D):
        for b in range(D):
            S[aa * D + b, (b - aa) % D] = 1.0
    P10 = cp.vec(p0, order="C") @ S
    P11 = cp.vec(p1, order="C") @ S
    obj = 0
    for k, P in (((0, 0), P00), ((0, 1), P01), ((1, 0), P10), ((1, 1), P11)):
        obj = obj + 0.25 * cp.sum(cp.rel_entr(Q[k], P))
    prob = cp.Problem(cp.Minimize(obj), cons)
    prob.solve(solver=solver)
    return prob.value, p0.value, p1.value


if __name__ == "__main__":
    for D in map(int, sys.argv[1:]):
        Q = dkz_Q(D)
        v, r, _ = strength_dual(Q, D)
        line = f"D={D}: dual {v / LOG2:.12f} bits"
        if D <= 40:
            vp, _, _ = strength_primal(Q, D)
            line += f"  primal {vp / LOG2:.12f} bits"
        print(line, flush=True)
