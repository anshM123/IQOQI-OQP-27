"""core.py -- numerics for the white-noise clause C2 (OQP 27B(ii)), complete von Neumann strategies on Phi_d.

Conventions.
  Alice: two orthonormal bases, columns of unitaries A[0], A[1] (vectors alpha^x_a).
  Bob:   two orthonormal bases of STEERED vectors, columns of unitaries F[0], F[1] (phi^y_b = conj of Bob's basis).
  Behaviour P[x, y, a, b] = |<alpha^x_a | phi^y_b>|^2 / d   (shape (2, 2, d, d)); uniform marginals.
  Noisy behaviour P_v = v P + (1 - v) u, u = 1/d^2.
  Deterministic points lam = (a0, a1, b0, b1).
"""
import itertools
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog


# ----------------------------------------------------------------------------------------------------------------
def ime(d):
    j = np.arange(1, d)
    return 4.0 / (d * (d - 1)) * np.sum((d - j) / np.cos(np.pi * j / (2 * d)))


def vstar(d):
    return 2.0 / ime(d)


def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    ph = np.diag(r) / np.abs(np.diag(r))
    return q * ph[None, :]


def dkz_bases(d):
    """DKZ: alpha^x_a = d^{-1/2} sum_k w^{-k(a + al_x)} |k>, phi^y_b = d^{-1/2} sum_k w^{-k(b + be_y)} |k>,
    al = (0, 1/2), be = (-1/4, 1/4)  (noise-literal/THEOREM.md, Lemma 7 orientation)."""
    k = np.arange(d)[:, None]
    al = [0.0, 0.5]
    be = [-0.25, 0.25]
    A = np.array([np.exp(-2j * np.pi * k * (np.arange(d)[None, :] + al[x]) / d) / np.sqrt(d) for x in range(2)])
    F = np.array([np.exp(-2j * np.pi * k * (np.arange(d)[None, :] + be[y]) / d) / np.sqrt(d) for y in range(2)])
    return A, F


def behaviour(A, F):
    d = A.shape[1]
    P = np.empty((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            P[x, y] = np.abs(A[x].conj().T @ F[y]) ** 2 / d
    return P


def noisy(P, v):
    d = P.shape[-1]
    return v * P + (1 - v) / d ** 2


def cglmp(P):
    """CGLMP expression of main.tex eq. (1.1); A_1, A_2 = Alice x = 0, 1; B_1, B_2 = Bob y = 0, 1."""
    d = P.shape[-1]

    def pr(x, y, k):   # P(A_x = B_y + k)
        a = np.arange(d)
        return sum(P[x, y, a, (a - k) % d].sum() for _ in [0])

    def prB(y, x, k):  # P(B_y = A_x + k)
        a = np.arange(d)
        return P[x, y, a, (a + k) % d].sum()

    tot = 0.0
    for k in range(d // 2):
        c = 1 - 2 * k / (d - 1)
        plus = pr(0, 0, k) + prB(0, 1, k + 1) + pr(1, 1, k) + prB(1, 0, k)
        minus = pr(0, 0, -k - 1) + prB(0, 1, -k) + pr(1, 1, -k - 1) + prB(1, 0, -k - 1)
        tot += c * (plus - minus)
    return tot


# ----------------------------------------------------------------------------------------------------------------
_ET = {}


def strategies(d):
    return np.array(list(itertools.product(range(d), repeat=4)), dtype=np.int64)


def det_T(d):
    """sparse (4 d^2) x d^4 matrix; column lam = indicator vector of deterministic point lam; row ((x*2+y)*d+a)*d+b."""
    if d not in _ET:
        S = strategies(d)
        m = len(S)
        rows, cols = [], []
        for x in range(2):
            for y in range(2):
                rows.append(((x * 2 + y) * d + S[:, x]) * d + S[:, 2 + y])
                cols.append(np.arange(m))
        rows = np.concatenate(rows)
        cols = np.concatenate(cols)
        _ET[d] = sp.csc_matrix((np.ones(len(rows)), (rows, cols)), shape=(4 * d * d, m))
    return _ET[d]


def vc(P, return_dual=False):
    """critical visibility max{v : v P + (1-v) u in L} by LP (HiGHS)."""
    d = P.shape[-1]
    ET = det_T(d)
    u = np.full(4 * d * d, 1.0 / d ** 2)
    p = P.reshape(-1)
    A = sp.hstack([ET, sp.csc_matrix((u - p)[:, None])]).tocsc()
    c = np.zeros(ET.shape[1] + 1)
    c[-1] = -1.0
    res = linprog(c, A_eq=A, b_eq=u, bounds=[(0, None)] * ET.shape[1] + [(0, None)], method='highs')
    if res.status != 0:
        raise RuntimeError(res.message)
    v = -res.fun
    if return_dual:
        y = res.eqlin.marginals.reshape(2, 2, d, d)
        return v, y, res.x[:-1]
    return v


def is_local(Q, tol=1e-9):
    """feasibility of Q in L; returns (bool, weights)."""
    d = Q.shape[-1]
    ET = det_T(d)
    q = Q.reshape(-1)
    res = linprog(np.zeros(ET.shape[1]), A_eq=ET, b_eq=q, bounds=[(0, None)] * ET.shape[1], method='highs')
    return res.status == 0, (res.x if res.status == 0 else None)


def local_max(beta):
    b = beta
    T = (b[0, 0][:, None, :, None] + b[0, 1][:, None, None, :] + b[1, 0][None, :, :, None]
         + b[1, 1][None, :, None, :])
    return float(T.max())


# ----------------------------------------------------------------------------------------------------------------
def random_strategy(d, rng):
    return np.array([haar(d, rng) for _ in range(2)]), np.array([haar(d, rng) for _ in range(2)])


def expm_herm(H):
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * w)[None, :]) @ V.conj().T


def perturb(A, F, eps, rng):
    d = A.shape[1]
    A2 = A.copy()
    F2 = F.copy()
    for x in range(2):
        H = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        H = (H + H.conj().T) / 2
        A2[x] = expm_herm(eps * H) @ A[x]
        H = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        H = (H + H.conj().T) / 2
        F2[x] = expm_herm(eps * H) @ F[x]
    return A2, F2


if __name__ == '__main__':
    for d in range(2, 9):
        A, F = dkz_bases(d)
        P = behaviour(A, F)
        print(d, 'marg', np.abs(P.sum(axis=3) - 1 / d).max(), 'I', cglmp(P), 'IME', ime(d),
              'vc', vc(P), 'v*', vstar(d))
