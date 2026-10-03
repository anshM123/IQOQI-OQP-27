"""Items 4 and 6 near the optimum: DKZ (x) 1_K with small NON-commuting perturbations of the four measurement bases.
Checks that (a) I_direct = I_chain to high relative accuracy in the gap I_ME - I (gap ~ s^2), (b) every LP-certificate direction pairs
nonpositively and their lambda-sum reproduces <v, delta> = 2 (F - F_DKZ), (c) each single all-positive-cell inequality (rotation c = 0)
is strict for the non-commuting perturbation, and its slack and the commutator norm of the reduced family scale like s^2 / s.
"""
import json, numpy as np, mpmath as mp
from k00_core import probs, cglmp, I_ME, reduce_to_clock, F_of_V, Qconfig, linear_form, rng
mp.mp.dps = 30


def u_and_K(n, q, d):
    N = 4 * d
    G = lambda j: -(mp.mpf(N) ** 2 / (2 * mp.pi ** 2)) * mp.clsin(2, 2 * mp.pi * mp.mpf(j) / (q * N))
    cache = {}
    Gq = lambda j: cache.setdefault(j, G(j))
    L = [0]
    for x in range(N):
        L.append(L[-1] + n[x % d])
    K = np.zeros((N, N))
    for x in range(N):
        for y in range(N):
            K[x, y] = float(Gq(L[x + 1] - L[y]) - Gq(L[x] - L[y]) - Gq(L[x + 1] - L[y + 1]) + Gq(L[x] - L[y + 1]))
    Kt = [sum(K[(r + m) % N, r] for r in range(d)) / d for m in range(N)]
    return np.array([Kt[m] + Kt[2 * d - m] for m in range(1, d)]), K


def dkz(d, K):
    alpha = [0.0, 0.5]; beta = [0.25, -0.25]; js = np.arange(d)
    PA = [[None] * d for _ in range(2)]; PB = [[None] * d for _ in range(2)]
    for x in range(2):
        for a in range(d):
            v = np.exp(-2j * np.pi * js * (a + alpha[x]) / d) / np.sqrt(d)
            PA[x][a] = np.kron(np.outer(v, v.conj()), np.eye(K))
    for y in range(2):
        for b in range(d):
            v = np.exp(2j * np.pi * js * (b - beta[y]) / d) / np.sqrt(d)
            PB[y][b] = np.kron(np.outer(v, v.conj()), np.eye(K))
    return PA, PB


def rot(P, H, s):
    w, U = np.linalg.eigh(H)
    Uu = U @ np.diag(np.exp(1j * s * w)) @ U.conj().T
    return [Uu @ p @ Uu.conj().T for p in P]


for d in [3, 5]:
    K = 2; D = d * K; N = 4 * d
    c = json.load(open(f'../../cone-certificates/certs/cert_d{d}.json'))
    UK = [u_and_K(n, c['q'], d) for n in c['cells']]
    U = np.array([u for u, _ in UK]).T
    v = 2 / np.sin(np.pi * np.arange(1, d) / (2 * d))
    lam = np.linalg.lstsq(U, v - U @ np.array(c['lam']), rcond=None)[0] + np.array(c['lam'])   # min-norm exact correction
    target = float(mp.mpf(N) ** 2 * mp.catalan / mp.pi ** 2)
    Hs = []
    for _ in range(4):
        H = rng.standard_normal((D, D)) + 1j * rng.standard_normal((D, D)); Hs.append((H + H.conj().T) / 2)
    FD = sum((d - m) / np.cos(np.pi * m / (2 * d)) for m in range(1, d))
    for s in [1e-1, 1e-2, 1e-3]:
        PA, PB = dkz(d, K)
        PA = [rot(PA[0], Hs[0], s), rot(PA[1], Hs[1], s)]
        PB = [rot(PB[0], Hs[2], s), rot(PB[1], Hs[3], s)]
        I1 = cglmp(probs(PA, PB, D, d), d)
        V, _ = reduce_to_clock(PA, PB, D, d)
        F = F_of_V(V, d)
        comm = max(np.abs(V[j] @ V[k] - V[k] @ V[j]).max() for j in range(d) for k in range(d))
        Q = Qconfig(V, d)
        Nm, AB = linear_form(Q, d)
        delta = np.array([Nm[m] - m for m in range(1, d)])
        pairs = U.T @ delta
        M = Q[0].shape[0]
        Tab = np.array([[np.trace(Q[x] @ Q[(y + d) % N]).real / M for y in range(N)] for x in range(N)])
        cellv = [float(np.sum(Kk * Tab)) - target for _, Kk in UK]
        gap = I_ME(d) - I1
        print(f"d={d} s={s:.0e}: I_ME - I = {gap:.3e};  |I - 4F/(d(d-1))|/gap = {abs(I1 - 4 * F / (d * (d - 1))) / gap:.1e};  "
              f"max_k <u_k,delta> = {pairs.max():.3e};  |sum lam_k <u_k,delta> - 2(F - F_DKZ)|/|2(F-F_DKZ)| = "
              f"{abs(lam @ pairs - 2 * (F - FD)) / abs(2 * (F - FD)):.1e};  max_k [Q^ell_k - N^2 Phi_c] = {max(cellv):.3e};  "
              f"max ||[V_j,V_k]|| = {comm:.2e}", flush=True)
