"""c05: sanity check of Theorem R itself (NUMERICAL, not part of the proof).
Maximise F(V) over reduced families V_k = U_k diag(i^{-s_k}) U_k^* (labels s fixed per run, unitaries free; BFGS on Hermitian
generators).  Theorem R predicts: any family with F = F_DKZ commutes, and near the optimum the commutators are O(sqrt(F_DKZ - F))
(the optimum is a Morse-Bott maximum modulo conjugation, B-T2).  Report per run: F_DKZ - F, max ||[V_j, V_k]||, ratio
max||[V_j,V_k]||^2 / (F_DKZ - F) for the runs that reach the top value.
"""
import sys
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize
from rcore import F_clock, F_DKZ, haar

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 5)


def herm(p, M):
    H = np.zeros((M, M), complex)
    iu = np.triu_indices(M, 1)
    k = M * (M - 1) // 2
    H[iu] = p[:k] + 1j * p[k:2 * k]
    H = H + H.conj().T
    H[np.diag_indices(M)] = p[2 * k:2 * k + M]
    return H


def run(d, M, S, U0, iters=3000):
    npar = M * M

    def fam(p):
        return np.array([U0[k] @ expm(1j * herm(p[k * npar:(k + 1) * npar], M)) @ np.diag((1j) ** (-S[k]))
                         @ expm(-1j * herm(p[k * npar:(k + 1) * npar], M)) @ U0[k].conj().T for k in range(d)])

    f = lambda p: -F_clock(fam(p))
    p0 = 0.3 * rng.standard_normal(d * npar)
    res = minimize(f, p0, method='BFGS', options=dict(maxiter=iters, gtol=1e-11))
    V = fam(res.x)
    gap = F_DKZ(d) - F_clock(V)
    comm = max(np.linalg.norm(V[j] @ V[k] - V[k] @ V[j]) for j in range(d) for k in range(d))
    return gap, comm


for d, M, nrun in ((3, 2, 12), (4, 2, 12), (5, 2, 10), (4, 3, 8), (6, 2, 8)):
    out = []
    for t in range(nrun):
        # labels: half the runs start from a two-window pattern (one-step mixtures), half random
        if t % 2 == 0:
            r1, r2 = rng.integers(0, d, 2)
            S = np.array([[0 if k < r1 else 1] + [int(rng.integers(0, 4)) if M > 2 else 0] * (M - 2) + [(2 if k < r2 else 3)]
                          for k in range(d)])[:, :M]
        else:
            S = rng.integers(0, 4, size=(d, M))
        U0 = np.array([haar(M, rng) for _ in range(d)])
        gap, comm = run(d, M, S, U0)
        out.append((gap, comm))
    top = [(g, c) for g, c in out if g < 1e-6]
    print(f"d={d} M={M}: runs={nrun}, reached F_DKZ (gap<1e-6): {len(top)};  "
          + ("max comm at top = %.2e, max comm^2/gap = %.2f" % (max(c for g, c in top), max(c * c / max(g, 1e-16) for g, c in top))
             if top else "") + f";  other gaps: {sorted(round(g, 4) for g, c in out if g >= 1e-6)}", flush=True)
