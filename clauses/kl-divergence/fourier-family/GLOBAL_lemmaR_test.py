"""
GLOBAL_lemmaR_test.py -- NUMERICAL test (not a proof) of the 'fixed Alice-joint' decoupling at DKZ_3.

Lemma R (proved in GLOBAL_NOTES.md Sec. 3): for any law mu of (a0, a1),
   S^UNI(q(A, B0, B1)) <= (1/2) [Phi(A, B0; mu) + Phi(A, B1; mu)],
   Phi(A, B; mu) = min_K (1/2) sum_x D(q_x(A, B) || p_x(mu, K)),  p_x(a, b) = sum_{a_x = a} mu(a0, a1) K(b | a0, a1).
The reduction proves 'DKZ Bob is the best response to DKZ Alice' only if max_B Phi(A*, B; mu) <= S0 for some mu.
This script takes mu = mu* (Alice marginal of the symmetric decomposition of the DKZ KKT model p*), checks
Phi(A*, B*_y; mu*) <= S0, and maximises Phi(A*, B; mu*) over B in U(3) (random starts + Nelder-Mead on exp(iH)).
"""
import itertools
import numpy as np
from scipy.optimize import minimize
from scipy.linalg import expm

d = 3
w = np.exp(2j * np.pi / 3)
alpha = (0.5, 0.0)
beta = (0.25, -0.25)
A = [np.array([[w ** (k * (a + alpha[x])) for a in range(d)] for k in range(d)]) / np.sqrt(3) for x in range(2)]
Bs = [np.array([[w ** (-k * (b + beta[y])) for b in range(d)] for k in range(d)]) / np.sqrt(3) for y in range(2)]
phi = np.eye(3).reshape(-1) / np.sqrt(3)


def q_link(Ax, B):
    out = np.zeros((3, 3))
    for a in range(3):
        for b in range(3):
            out[a, b] = abs(np.kron(Ax[:, a], B[:, b]).conj() @ phi) ** 2
    return out


def levels():
    """CGLMP levels g'_xy(a, b) of THEOREM.md Sec. 3."""
    g = np.zeros((2, 2, 3, 3), dtype=int)
    for a in range(3):
        for b in range(3):
            g[0, 0, a, b] = (a - b) % 3
            g[1, 1, a, b] = (a - b) % 3
            g[1, 0, a, b] = (b - a) % 3
            g[0, 1, a, b] = (b - a - 1) % 3
    return g


s3 = np.sqrt(3)
BETA = ((16 + 24 * s3) - np.sqrt(3280 - 960 * s3)) / 54
r = np.array([1 + BETA * (0.5 - k) for k in range(3)])
QL = np.array([2 * (2 + s3) / 9, 2 * (2 - s3) / 9, 1 / 9])
S0 = float(QL @ np.log(r))
G = levels()
q0 = np.array([[q_link(A[x], Bs[y]) for y in range(2)] for x in range(2)])
# symmetric decomposition of p* = q0 / r*: facet strategies (sum g' = 2) with type weights
lams = list(itertools.product(range(3), repeat=4))
P = QL / r
wts = {}
for lam in lams:
    lv = [G[x, y, lam[x], lam[2 + y]] for x in range(2) for y in range(2)]   # order 00, 01, 10, 11
    if sum(lv) != 2:
        continue
    if 2 in lv:
        wts[lam] = 4 * P[2] / 12
    else:
        ones = {i for i in range(4) if lv[i] == 1}
        adj = [{0, 1}, {1, 3}, {3, 2}, {2, 0}]            # links sharing a party (00-01, 01-11, 11-10, 10-00)
        wts[lam] = P[1] / 12 if ones in adj else P[1] / 6
tot = sum(wts.values())
pst = np.zeros((2, 2, 3, 3))
for lam, wt in wts.items():
    for x in range(2):
        for y in range(2):
            pst[x, y, lam[x], lam[2 + y]] += wt
err_pstar = np.abs(pst - q0 / r[G]).max()
mu = np.zeros((3, 3))
for lam, wt in wts.items():
    mu[lam[0], lam[1]] += wt


def Phi(B, mu, iters=3000):
    qx = [q_link(A[x], B) for x in range(2)]
    K = np.full((3, 3, 3), 1 / 3)            # K[a0, a1, b]
    for _ in range(iters):
        num = np.zeros((3, 3, 3))
        for x in range(2):
            px = np.zeros((3, 3))
            for a0 in range(3):
                for a1 in range(3):
                    ax = (a0, a1)[x]
                    px[ax] += mu[a0, a1] * K[a0, a1]
            ratio = np.where(qx[x] > 0, qx[x] / np.maximum(px, 1e-300), 0)
            for a0 in range(3):
                for a1 in range(3):
                    ax = (a0, a1)[x]
                    num[a0, a1] += mu[a0, a1] * K[a0, a1] * ratio[ax]
        K = num / np.maximum(num.sum(axis=2, keepdims=True), 1e-300)
    val = 0.0
    for x in range(2):
        px = np.zeros((3, 3))
        for a0 in range(3):
            for a1 in range(3):
                px[(a0, a1)[x]] += mu[a0, a1] * K[a0, a1]
        m = qx[x] > 0
        val += 0.5 * np.sum(qx[x][m] * np.log(qx[x][m] / px[m]))
    return val


def herm(v):
    H = np.zeros((3, 3), complex)
    iu = np.triu_indices(3, 1)
    H[np.diag_indices(3)] = v[:3]
    H[iu] = v[3:6] + 1j * v[6:9]
    H = H + np.triu(H, 1).conj().T
    return H


if __name__ == "__main__":
    print(f"S0 = {S0 / np.log(2):.10f} bits; total weight of the decomposition {tot:.12f}; max |p* - q0/r*| "
          f"{err_pstar:.2e}")
    print(f"mu* (Alice joint law): {np.round(mu, 6).tolist()}")
    for y in range(2):
        print(f"Phi(A*, B*_{y}; mu*) = {Phi(Bs[y], mu) / np.log(2):.10f} bits")
    rng = np.random.default_rng(7)
    best = -1
    for t in range(40):
        U0 = expm(1j * herm(rng.normal(size=9)))
        f = lambda v: -Phi(U0 @ expm(1j * herm(v)), mu, iters=400)
        res = minimize(f, np.zeros(9), method="Nelder-Mead", options=dict(maxiter=1500, xatol=1e-6, fatol=1e-10))
        val = -res.fun
        if val > best:
            best = val
            bestU = U0 @ expm(1j * herm(res.x))
        print(f"  start {t}: local max Phi = {val / np.log(2):.8f} bits (best {best / np.log(2):.8f})", flush=True)
    print(f"max_B Phi(A*, B; mu*) >= {Phi(bestU, mu) / np.log(2):.10f} bits vs S0 = {S0 / np.log(2):.10f} bits")
