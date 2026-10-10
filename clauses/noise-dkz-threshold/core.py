"""
core.py -- shared utilities for P3_full_theory (scenario (2,2,d), behaviours p[x,y,a,b]).

Conventions (as in ../BRIEF.md):
  * behaviour p has shape (2,2,d,d), p[x,y,a,b] = p(a,b|x,y), flattened in C order;
  * deterministic strategy lam = (a0,a1,b0,b1);
  * max-ent rank-one strategy: p_xy = |T_xy|^2/d, T_xy = A_x^T B_y (columns of A_x, B_y = basis vectors);
    flatness: T_01 = T_00 T_10^dagger T_11;
  * flat permutation connection: permutations s_xy (as maps a -> b) with s_01 = s_11 o s_10^{-1} o s_00,
    behaviour p_xy(a,b) = [b = s_xy(a)]/d.
"""
import itertools
import numpy as np
from scipy.optimize import linprog

_E = {}


def det_matrix(d):
    """rows = deterministic behaviours (d^4 x 4d^2), row order = itertools.product(range(d), repeat=4)
    over (a0, a1, b0, b1)."""
    if d not in _E:
        S = np.array(list(itertools.product(range(d), repeat=4)))
        m = len(S)
        E = np.zeros((m, 4 * d * d))
        for x in range(2):
            for y in range(2):
                idx = ((x * 2 + y) * d + S[:, x]) * d + S[:, 2 + y]
                E[np.arange(m), idx] = 1.0
        _E[d] = (S, E)
    return _E[d]


def i_me(d):
    j = np.arange(1, d)
    return 4.0 / (d * (d - 1)) * np.sum((d - j) / np.cos(np.pi * j / (2 * d)))


def uniform(d):
    return np.full((2, 2, d, d), 1.0 / d ** 2)


def perm_matrix(s):
    d = len(s)
    P = np.zeros((d, d))
    P[np.arange(d), np.asarray(s)] = 1.0
    return P


def flat_perm_connections(d):
    """all flat permutation connections as behaviours (array n x 4d^2); duplicates removed."""
    perms = list(itertools.permutations(range(d)))
    out = []
    for s00 in perms:
        P00 = perm_matrix(s00)
        for s10 in perms:
            P10 = perm_matrix(s10)
            for s11 in perms:
                P11 = perm_matrix(s11)
                P01 = P00 @ P10.T @ P11
                p = np.stack([P00, P01, P10, P11]).reshape(2, 2, d, d) / d
                out.append(p.reshape(-1))
    out = np.unique(np.round(np.array(out) * d).astype(np.int8), axis=0).astype(float) / d
    return out


def dkz_unitaries(d):
    """DKZ bases A_x, B_y (columns = vectors), p = |A^T B|^2/d."""
    k = np.arange(d)
    w = np.exp(2j * np.pi / d)
    alpha = [0.0, 0.5]
    beta = [0.25, -0.25]
    A = [np.array([w ** (k * (a + alpha[x])) / np.sqrt(d) for a in range(d)]).T for x in range(2)]
    B = [np.array([w ** (-k * (b + beta[y])) / np.sqrt(d) for b in range(d)]).T for y in range(2)]
    return A, B


def maxent_behaviour(A, B):
    d = A[0].shape[0]
    p = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            p[x, y] = np.abs(A[x].T @ B[y]) ** 2 / d
    return p


def dkz(d):
    return maxent_behaviour(*dkz_unitaries(d))


def gauge_lp(p, V, n=None, method="highs"):
    """largest t with n + t (p - n) in conv(V) (rows of V = vertices).  Returns t (np.inf if unbounded)."""
    pf = p.reshape(-1)
    d2 = pf.size
    nf = (np.full(d2, 1.0 / (d2 // 4)) if n is None else n.reshape(-1))
    m = V.shape[0]
    # variables: mu (m), t ; constraints: V^T mu - t (p - n) = n ; sum mu = 1
    Aeq = np.hstack([V.T, -(pf - nf)[:, None]])
    Aeq = np.vstack([Aeq, np.concatenate([np.ones(m), [0.0]])])
    beq = np.concatenate([nf, [1.0]])
    c = np.zeros(m + 1)
    c[-1] = -1.0
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m + [(None, None)], method=method)
    if res.status == 3:
        return np.inf, res
    if res.status != 0:
        raise RuntimeError(res.message)
    return res.x[-1], res


def critical_visibility(p, n=None):
    """v_c = max{v : v p + (1-v) n in L}; n defaults to the uniform behaviour."""
    d = p.shape[2]
    S, E = det_matrix(d)
    t, res = gauge_lp(p, E, n)
    return min(t, np.inf), res


def haar(D, rng):
    Z = (rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def random_maxent(d, rng):
    A = [haar(d, rng) for _ in range(2)]
    B = [haar(d, rng) for _ in range(2)]
    return maxent_behaviour(A, B)
