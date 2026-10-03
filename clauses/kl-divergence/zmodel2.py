"""
zmodel2.py -- as zmodel.py, but the far tail (|m| > A + B, where only the analytic tail family contributes)
is summed analytically, so the convex program only involves the window.

Model (a0 = 0): window part pi0(a,b0), pi1(a,b1), |a| <= A, |b| <= B, common a-marginal;
tail |a| > A: mu(a) = t/(a^2 - 1/4), b0 in {0, a} (1/2 each), b1 in {1, a} (1/2 each).
For |m| > A + B:  P00(m) = t g(m), P10(m) = t g(-m), P01(m) = t g(m), P11(m) = t g(1-m),  g(a) = 1/(2(a^2-1/4)).
Far-tail objective:  sum_{|m| > K} Q log(Q/(t g)) = C_xy - (sum_{|m|>K} Q) log t   (C_xy, Q-mass by mpmath).
usage: python zmodel2.py A B [out.npz]
"""
import sys
import numpy as np
import cvxpy as cp
import scipy.sparse as sp
import mpmath as mp

DELTA = {(0, 0): 0.25, (0, 1): 0.75, (1, 0): -0.25, (1, 1): 0.25}
NEAR = {(0, 0): 0, (1, 0): 0, (0, 1): 1, (1, 1): 0}
LOG2 = np.log(2)
mp.mp.dps = 30


def Qz(m, dl):
    return 1.0 / (2 * np.pi ** 2 * (np.asarray(m, float) - dl) ** 2)


def mprime(m, xy):
    """argument of g giving the tail far contribution of link xy at value m"""
    return {(0, 0): m, (0, 1): m, (1, 0): -m, (1, 1): 1 - m}[xy]


def far_constants(K, xy):
    """C = sum_{|m|>K} Q log(Q/g(m')),  W = sum_{|m|>K} Q  (mpmath, high precision, nsum)."""
    dl = mp.mpf(DELTA[xy])

    def Q(m):
        return 1 / (2 * mp.pi ** 2 * (m - dl) ** 2)

    def g(a):
        return 1 / (2 * (a * a - mp.mpf(1) / 4))

    def termC(m):
        return Q(m) * mp.log(Q(m) / g(mprime(m, xy)))
    C = mp.nsum(termC, [K + 1, mp.inf]) + mp.nsum(lambda n: termC(-n), [K + 1, mp.inf])
    W = mp.nsum(Q, [K + 1, mp.inf]) + mp.nsum(lambda n: Q(-n), [K + 1, mp.inf])
    return float(C), float(W)


def tail_in_window(ms, A, xy):
    """per unit t: tail contributions to P_xy(m) for m in ms (far part only)"""
    a = np.array([mprime(m, xy) for m in ms], float)
    out = 0.5 / (a ** 2 - 0.25)
    out[np.abs(a) <= A] = 0.0
    return out


def solve(A, B, verbose=False):
    K = A + B
    av = np.arange(-A, A + 1)
    bv = np.arange(-B, B + 1)
    ms = np.arange(-K, K + 1)
    idx = {m: i for i, m in enumerate(ms)}
    na, nb = len(av), len(bv)
    rows_b, rows_bma, cols = [], [], []
    for i, a in enumerate(av):
        for j, b in enumerate(bv):
            cols.append(i * nb + j)
            rows_b.append(idx[b])
            rows_bma.append(idx[b - a])
    n = na * nb
    Mb = sp.csr_matrix((np.ones(n), (rows_b, cols)), shape=(len(ms), n))
    Mbma = sp.csr_matrix((np.ones(n), (rows_bma, cols)), shape=(len(ms), n))
    Ma = sp.kron(sp.eye(na), np.ones((1, nb))).tocsr()
    p0 = cp.Variable(n, nonneg=True)
    p1 = cp.Variable(n, nonneg=True)
    t = cp.Variable(pos=True)
    tm = 4.0 / (2 * A + 1)            # sum_{|a|>A} 1/(a^2-1/4)
    cons = [Ma @ p0 == Ma @ p1, cp.sum(p0) + t * tm == 1]
    obj = 0
    consts = 0.0
    for xy in DELTA:
        Q = Qz(ms, DELTA[xy])
        pv = p0 if xy[1] == 0 else p1
        lin = (Mb if xy[0] == 0 else Mbma) @ pv
        near = np.zeros(len(ms))
        near[idx[NEAR[xy]]] = 0.5 * tm
        P = lin + t * (tail_in_window(ms, A, xy) + near)
        C, W = far_constants(K, xy)
        consts += 0.25 * C
        obj = obj + 0.25 * cp.sum(cp.rel_entr(Q, P)) - 0.25 * W * cp.log(t)
    prob = cp.Problem(cp.Minimize(obj), cons)
    prob.solve(solver="CLARABEL", verbose=verbose)
    return prob.value + consts, p0.value.reshape(na, nb), p1.value.reshape(na, nb), float(t.value), av, bv


if __name__ == "__main__":
    A, B = map(int, sys.argv[1:3])
    val, p0, p1, t, av, bv = solve(A, B)
    print(f"A={A} B={B}: full objective {val / LOG2:.12f} bits  t*pi^2={t*np.pi**2:.6f}  window mass {p0.sum():.6f}",
          flush=True)
    if len(sys.argv) > 3:
        np.savez(sys.argv[3], p0=p0, p1=p1, t=t, A=A, B=B, av=av, bv=bv)
