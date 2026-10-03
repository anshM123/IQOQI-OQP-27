"""
ref_solver.py -- referee's own KL (van Dam-Gruenwald-Gill) strength solver for the (2,2,d) scenario, written
independently of P4_kl (no shared code).

  U_q(sigma) = min_{p in L_d} sum_xy sigma_xy D(q_xy || p_xy)

DUAL (used for certified LOWER bounds, Lemma D / Gibbs):  for r >= 0, r > 0 on supp q, with
  M(r) = max_{lambda in Z_d^4} sum_xy sigma_xy r(a_x, b_y | xy),
  U_q(sigma) >= sum sigma q log r - log M(r).
  Solved with cvxpy (Clarabel, exponential cone): max sum w log s  s.t.  E s <= 1, with w = sigma q, s = sigma r.
PRIMAL (certified UPPER bounds): the constraint multipliers y_lambda >= 0 of the dual give a local model
  p = sum y_lambda delta_lambda; rationalised, mixed with 1e-12 of the uniform mixture, normalised exactly.

Certification: r and y are rationalised (Fractions), M(r) is computed exactly over all d^4 strategies, and the
logarithmic sums are evaluated in mpmath interval arithmetic from an interval enclosure of q supplied by the caller.
"""
import itertools
from fractions import Fraction as Fr
import numpy as np
import cvxpy as cp
from mpmath import iv, mpf

iv.dps = 40
LN2 = iv.log(iv.mpf(2))
CELLS_CACHE = {}


def cells(d):
    return [(x, y, a, b) for x in range(2) for y in range(2) for a in range(d) for b in range(d)]


def strategies(d):
    return list(itertools.product(range(d), repeat=4))      # (a0, a1, b0, b1)


def incidence(d):
    if d in CELLS_CACHE:
        return CELLS_CACHE[d]
    C = cells(d)
    idx = {c: i for i, c in enumerate(C)}
    S = strategies(d)
    E = np.zeros((len(S), len(C)))
    for k, lam in enumerate(S):
        for x in range(2):
            for y in range(2):
                E[k, idx[(x, y, lam[x], lam[2 + y])]] = 1.0
    CELLS_CACHE[d] = (C, idx, S, E)
    return CELLS_CACHE[d]


def solve(qf, d, sigma=None, verbose=False):
    """qf: float array over cells(d) order. returns dict with float dual r, multipliers y, value (nats)."""
    C, idx, S, E = incidence(d)
    sig = np.array([0.25] * len(C)) if sigma is None else np.array([sigma[(c[0], c[1])] for c in C])
    w = sig * qf
    supp = w > 1e-300
    s = cp.Variable(int(supp.sum()))
    cons = [E[:, supp] @ s <= 1]
    prob = cp.Problem(cp.Maximize(w[supp] @ cp.log(s)), cons)
    prob.solve(solver=cp.CLARABEL, verbose=verbose, max_iter=500, tol_gap_abs=1e-12, tol_gap_rel=1e-12,
               tol_feas=1e-12)
    sv = np.zeros(len(C))
    sv[supp] = s.value
    r = np.where(supp, sv / sig, 0.0)
    y = np.maximum(cons[0].dual_value, 0)
    val = float(np.sum(w[supp] * np.log(r[supp])))
    return dict(r=r, y=y, val=val, supp=supp, sig=sig)


def certify_lower(qiv, d, r, sigma=None, den=10 ** 10):
    """qiv: dict cell -> iv interval enclosure of q. r: float test factor (0 off support).
    returns (certified lower bound in bits (iv lower endpoint as mpf), exact M before scaling)."""
    C, idx, S, E = incidence(d)
    sg = {(x, y): Fr(1, 4) for x in range(2) for y in range(2)} if sigma is None else sigma
    R = {c: (Fr(float(r[i])).limit_denominator(den) if r[i] > 0 else Fr(0)) for i, c in enumerate(C)}
    for c in C:
        if qiv[c].b > 0:
            assert R[c] > 0, c
    # exact M(R): max over strategies of sum sigma r -- decomposed: for fixed (a0, a1), max over b0 and b1 separately
    best = Fr(0)
    for a0 in range(d):
        for a1 in range(d):
            m0 = max(sg[(0, 0)] * R[(0, 0, a0, b)] + sg[(1, 0)] * R[(1, 0, a1, b)] for b in range(d))
            m1 = max(sg[(0, 1)] * R[(0, 1, a0, b)] + sg[(1, 1)] * R[(1, 1, a1, b)] for b in range(d))
            best = max(best, m0 + m1)
    Mx = best
    L = iv.mpf(0)
    for c in C:
        if R[c] > 0:
            L += iv.mpf(sg[(c[0], c[1])].numerator) / sg[(c[0], c[1])].denominator * qiv[c] * \
                 iv.log(iv.mpf(R[c].numerator) / R[c].denominator)
    L -= iv.log(iv.mpf(Mx.numerator) / Mx.denominator)
    return mpf((L / LN2).a), Mx


def certify_upper(qiv, d, y, sigma=None, den=10 ** 12, eps=Fr(1, 10 ** 12)):
    """explicit rational local model from multipliers y; returns certified upper bound in bits (mpf)."""
    C, idx, S, E = incidence(d)
    sg = {(x, y_): Fr(1, 4) for x in range(2) for y_ in range(2)} if sigma is None else sigma
    yr = [Fr(float(v)).limit_denominator(den) for v in y]
    tot = sum(yr)
    n = len(S)
    wts = [(1 - eps) * v / tot + eps / n for v in yr]
    assert sum(wts) == 1 and all(v > 0 for v in wts)
    p = {c: Fr(0) for c in C}
    for k, lam in enumerate(S):
        wk = wts[k]
        for x in range(2):
            for y_ in range(2):
                p[(x, y_, lam[x], lam[2 + y_])] += wk
    U = iv.mpf(0)
    for c in C:
        qc = qiv[c]
        if qc.b > 0:
            sgc = iv.mpf(sg[(c[0], c[1])].numerator) / sg[(c[0], c[1])].denominator
            pc = iv.mpf(p[c].numerator) / p[c].denominator
            if qc.a > 0:
                U += sgc * qc * (iv.log(qc) - iv.log(pc))
            else:   # q may be 0: use x log x <= 0 bound, enclosure [-1/e .. ] handled conservatively
                U += sgc * qc * (iv.log(iv.mpf(qc.b)) - iv.log(pc))
    return mpf((U / LN2).b)


# -------------------------------------------------------------------------------- quantum correlations
def corr_from_bases(A, B):
    """A[x], B[y]: d x d unitary (columns = basis vectors). Phi_d. q[(x,y,a,b)] (float)."""
    d = A[0].shape[0]
    out = {}
    for x in range(2):
        for y in range(2):
            amp = A[x].conj().T @ B[y].conj() / np.sqrt(d)      # <a_x|<b_y|Phi> = d^-1/2 sum_k conj(A_ka) conj(B_kb)
            q = np.abs(amp) ** 2
            for a in range(d):
                for b in range(d):
                    out[(x, y, a, b)] = q[a, b]
    return out
