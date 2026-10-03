"""
seesaw_check.py -- independent see-saw search (every best response is an SDP, cvxpy + Clarabel) for CGLMP_d on
Phi_D with general POVMs, and best-response gaps of the strategies saved by povm_search.py.
usage:  python seesaw_check.py search d D nstart seed      (see-saw from random POVMs)
        python seesaw_check.py gaps file.npz [file2.npz ...]   (best-response gaps of saved strategies)
Model as in povm_core.py:  Pi = (1/D) sum c[x,y,a,b] Tr(X^x_a Y^y_b) (minimised), I = 4 - 2(d Pi - 1)/(d-1).
"""
import sys
import numpy as np
import cvxpy as cp
from povm_core import cglmp_coeffs, I_from_Pi, I_ME, CGLMPPovm


def G_for(Es, g, c, D):
    X = [Es[0], Es[2]]
    Y = [Es[1], Es[3]]
    if g in (0, 2):
        x = g // 2
        return np.einsum('yab,ybij->aij', c[x], np.stack(Y)) / D
    y = g // 2
    return np.einsum('xab,xaij->bij', c[:, y], np.stack(X)) / D


def best_response(G):
    """min sum_a Re Tr(E_a G_a) over POVMs; returns (value, E)."""
    d, D, _ = G.shape
    Ev = [cp.Variable((D, D), hermitian=True) for _ in range(d)]
    cons = [E >> 0 for E in Ev] + [sum(Ev) == np.eye(D)]
    obj = cp.Minimize(sum(cp.real(cp.trace(Ev[a] @ G[a])) for a in range(d)))
    prob = cp.Problem(obj, cons)
    prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11)
    E = np.stack([(e.value + e.value.conj().T) / 2 for e in Ev])
    return prob.value, E


def value(Es, d, D):
    return CGLMPPovm(d, D).Pi_of_E(Es)


def gaps(Es, d, D):
    c = cglmp_coeffs(d)
    out = []
    for g in range(4):
        G = G_for(Es, g, c, D)
        cur = float(np.einsum('aij,aji->', Es[g], G).real)
        br, _ = best_response(G)
        out.append(cur - br)
    return out


def rand_povm(d, D, rng):
    G = rng.normal(size=(d, D, D)) + 1j * rng.normal(size=(d, D, D))
    K = np.einsum('aki,akj->ij', G.conj(), G)
    lam, U = np.linalg.eigh(K)
    S = (U * lam ** -0.5) @ U.conj().T
    return np.stack([S @ g.conj().T @ g @ S for g in G])


def search(d, D, nstart, seed, rounds=400, tol=1e-12):
    rng = np.random.default_rng(seed)
    c = cglmp_coeffs(d)
    best = -np.inf
    for s in range(nstart):
        Es = [rand_povm(d, D, rng) for _ in range(4)]
        prev = np.inf
        for r in range(rounds):
            for g in (0, 2, 1, 3):
                _, Es[g] = best_response(G_for(Es, g, c, D))
            Pi = value(Es, d, D)
            if prev - Pi < tol:
                break
            prev = Pi
        I = I_from_Pi(Pi, d)
        best = max(best, I)
        nonproj = max(float(np.abs(E @ E - E).max()) for E in Es)
        print(f"seesaw d={d} D={D} start {s}: I = {I:.12f}  I-I_ME = {I - I_ME(d):+.3e}  rounds {r + 1}  "
              f"nonproj {nonproj:.1e}", flush=True)
    print(f"# SEESAW BEST d={d} D={D}: I = {best:.12f}  I_ME = {I_ME(d):.12f}  I-I_ME = {best - I_ME(d):+.3e}",
          flush=True)


if __name__ == "__main__":
    if sys.argv[1] == 'search':
        search(*(int(t) for t in sys.argv[2:6]))
    else:
        for f in sys.argv[2:]:
            z = np.load(f)
            Es = list(z['Es'])
            d, D = Es[0].shape[0], Es[0].shape[1]
            gp = gaps(Es, d, D)
            print(f"{f}: d={d} D={D} I = {float(z['I']):.13f}  I-I_ME = {float(z['I']) - I_ME(d):+.2e}  "
                  f"best-response gaps (X1,Y1,X2,Y2) = {', '.join(f'{x:.1e}' for x in gp)}", flush=True)
