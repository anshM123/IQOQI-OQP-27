"""
ref_d3_direct.py -- referee: direct numerical test of Theorem 3 without the Hessian machinery.
Random perturbations of DKZ_3 in ALL 36 unitary directions (A_x -> exp(i eps H) A_x, B_y -> exp(i eps K) B_y,
H, K random Hermitian with Frobenius norm 1), radii eps in {0.2, 0.1, 0.05, 0.02}; for each: S^UNI (own dual
solver, float certificate) and S^COR = min_{p local} max_xy D(q_xy || p_xy) (convex program; Sion minimax).
Expected (Theorem 3): both strictly below S0 = 0.0577830254933 bits, decreasing ~ eps^2.
Also: S^UC via a grid over product setting distributions at a few points (must lie between UNI and COR).
usage: python ref_d3_direct.py [nsamples]
"""
import sys
import numpy as np
import cvxpy as cp
from scipy.linalg import expm
from ref_solver import solve, incidence, cells, corr_from_bases
from ref_blocks import block_bases

S0 = 0.05778302549332865
rng = np.random.default_rng(20261002)
ns = int(sys.argv[1]) if len(sys.argv) > 1 else 12
A0, B0 = block_bases("K3")
C, idx, S, E = incidence(3)


def herm(rng):
    X = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
    H = (X + X.conj().T) / 2
    return H / np.linalg.norm(H)


def scor(qf):
    w = cp.Variable(len(S), nonneg=True)
    p = E.T @ w
    tt = cp.Variable()
    cons = [cp.sum(w) == 1]
    for x in range(2):
        for y in range(2):
            sel = np.array([c[0] == x and c[1] == y for c in C])
            cons.append(cp.sum(cp.rel_entr(qf[sel], p[sel])) <= tt)
    cp.Problem(cp.Minimize(tt), cons).solve(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12,
                                            tol_feas=1e-12)
    return tt.value / np.log(2)


def suc(qf, grid=9):
    best = 0
    for sa in np.linspace(0.1, 0.9, grid):
        for sb in np.linspace(0.1, 0.9, grid):
            sig = {(0, 0): sa * sb, (0, 1): sa * (1 - sb), (1, 0): (1 - sa) * sb, (1, 1): (1 - sa) * (1 - sb)}
            best = max(best, solve(qf, 3, sigma=sig)["val"] / np.log(2))
    return best


worst = {}
for eps in (0.2, 0.1, 0.05, 0.02):
    rows = []
    for s in range(ns):
        Hs = [herm(rng) for _ in range(4)]
        nrm = np.sqrt(sum(np.linalg.norm(H) ** 2 for H in Hs))
        A = [expm(1j * eps * Hs[x] / nrm) @ A0[x] for x in range(2)]
        B = [expm(1j * eps * Hs[2 + y] / nrm) @ B0[y] for y in range(2)]
        qd = corr_from_bases(A, B)
        qf = np.array([qd[c] for c in C])
        u = solve(qf, 3)["val"] / np.log(2)
        c_ = scor(qf)
        rows.append((u, c_))
    du = max((u - S0) / eps ** 2 for u, c_ in rows)
    dc = max((c_ - S0) / eps ** 2 for u, c_ in rows)
    worst[eps] = (du, dc)
    print(f"eps={eps:5.2f}: max (S^UNI - S0)/eps^2 = {du:+.5f}, max (S^COR - S0)/eps^2 = {dc:+.5f} bits; "
          f"all below S0: UNI {all(u < S0 for u, _ in rows)}, COR {all(c_ < S0 for _, c_ in rows)}; "
          f"COR >= UNI: {all(c_ >= u - 1e-9 for u, c_ in rows)}", flush=True)
# S^UC spot check at a few eps = 0.1 points
for s in range(2):
    Hs = [herm(rng) for _ in range(4)]
    nrm = np.sqrt(sum(np.linalg.norm(H) ** 2 for H in Hs))
    A = [expm(1j * 0.1 * Hs[x] / nrm) @ A0[x] for x in range(2)]
    B = [expm(1j * 0.1 * Hs[2 + y] / nrm) @ B0[y] for y in range(2)]
    qd = corr_from_bases(A, B)
    qf = np.array([qd[c] for c in C])
    u = solve(qf, 3)["val"] / np.log(2)
    print(f"spot eps=0.1: S^UNI {u:.10f} <= S^UC(grid) {suc(qf):.10f} <= S^COR {scor(qf):.10f} < S0 {S0:.10f}",
          flush=True)
