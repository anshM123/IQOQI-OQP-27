"""
lead1_hull.py -- C3 lead 1 test (numerics): is every PVM behaviour on Phi_3 in
    H = conv( relabelled F3 behaviours  U  deterministic points )?
(S^X is convex and relabelling-invariant, S^X <= S0 on F3 (Theorems F3, F3'), S^X = 0 on L, so S^X <= S0 on H.)
Doubly-stochastic local post-processings add nothing: they are convex combinations of relabellings (Birkhoff).
Relabellings: every permutation of Z_3 is affine (a -> eps a + c); the shifts c and the covariance-preserving maps
(all four signs equal, setting/party swaps) map F3 onto F3, so the relabelled copies of F3 are the 8 "sign sheets"
q'(a,b|x,y) = q(eps_x a, eta_y b | x, y), (eps_0, eps_1, eta_0, eta_1) in {+-1}^4 modulo a global sign.
Test: radial LP  t*(p) = max{ t : u + t (p - u) in H }   (p in H  iff  t* >= 1).
"""
import sys
import itertools
import numpy as np
from scipy.optimize import linprog
from c3core import *

def sheets_generators(n_grid=24, local_pts=None):
    g = np.linspace(0, 2 * np.pi, n_grid, endpoint=False)
    Z = np.array(list(itertools.product(g, g, g)))
    if local_pts is not None:
        Z = np.vstack([Z, local_pts])
    base = np.array([f3_corr(z) for z in Z])                     # N x 2x2x3x3
    gens = []
    pats = [p for p in itertools.product([1, -1], repeat=4) if p[0] == 1]
    for (e0, e1, h0, h1) in pats:
        eps = (e0, e1); eta = (h0, h1)
        G = np.empty_like(base)
        for x in range(2):
            for y in range(2):
                ia = (eps[x] * np.arange(3)) % 3
                ib = (eta[y] * np.arange(3)) % 3
                G[:, x, y] = base[:, x, y][:, ia][:, :, ib]
        gens.append(G.reshape(len(Z), 36))
    det = EMAT.copy()                                            # deterministic points (81 x 36)
    return np.vstack(gens + [det])


def radial_t(p, Gm, u):
    """max t s.t. sum lam_g g = u + t (p - u), lam >= 0, sum lam = 1."""
    n = Gm.shape[0]
    # variables: lam (n), t
    c = np.zeros(n + 1); c[-1] = -1.0
    Aeq = np.zeros((37, n + 1))
    Aeq[:36, :n] = Gm.T
    Aeq[:36, -1] = -(p - u)
    beq = np.zeros(37); beq[:36] = u
    Aeq[36, :n] = 1.0; beq[36] = 1.0
    bounds = [(0, None)] * n + [(None, None)]
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
    if res.status != 0:
        return np.nan
    return res.x[-1]


if __name__ == "__main__":
    rng = np.random.default_rng(2026)
    zs = np.array([-np.pi / 6, -np.pi / 2, np.pi / 6])
    loc = zs + 0.05 * rng.standard_normal((3000, 3))
    Gm = sheets_generators(24, loc)
    print("generators:", Gm.shape, flush=True)
    u = np.full(36, 1.0 / 9)
    U0 = dkz()
    p0 = corr(U0).reshape(36)
    print("t*(DKZ) =", radial_t(p0, Gm, u))
    # transverse first-order directions at DKZ
    J = jacobian(U0, h=1e-5)
    Uu, sv, Vt = np.linalg.svd(J)
    r = int((sv > 1e-6).sum())
    h = 1e-5
    JF = np.zeros((36, 3))
    for j in range(3):
        e = np.zeros(3); e[j] = h
        JF[:, j] = (f3_corr(zs + e) - f3_corr(zs - e)).reshape(36) / (2 * h)
    QF, _ = np.linalg.qr(JF)
    # chart directions whose image is orthogonal to the F3 tangent
    V = Vt[:r].T                       # chart directions with nonzero image
    img = J @ V
    img_perp = img - QF @ (QF.T @ img)
    Uq, sq, Wt = np.linalg.svd(img_perp, full_matrices=False)
    print("transverse image singular values:", np.round(sq, 6))
    for k in range(3):
        z = V @ Wt[k]                   # a chart direction with transverse image
        z /= np.linalg.norm(z)
        for s in [1e-3, 1e-2, 3e-2, 0.1, 0.2, 0.4]:
            pz = corr(chart(U0, s * z)).reshape(36)
            t = radial_t(pz, Gm, u)
            S, lb = s_uni(pz.reshape(2, 2, 3, 3), iters=4000)
            print(f"dir {k} s={s:6.3f}  t*={t:.6f}  S={S/LOG2:.6f} bits", flush=True)
    # random strategies
    cnt = 0
    ts = []
    for it in range(60):
        Ur = random_strategy(rng)
        pr = corr(Ur).reshape(36)
        t = radial_t(pr, Gm, u)
        ts.append(t)
    ts = np.array(ts)
    print("random strategies: fraction in H (t*>=1):", np.mean(ts >= 1 - 1e-9), " quantiles t*:",
          np.round(np.quantile(ts, [0, 0.1, 0.5, 0.9, 1]), 4))
