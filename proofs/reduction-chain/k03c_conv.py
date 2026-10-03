"""Item 2: boundary mean-value identity int u*_lam dm = M h_lam(1/4) for a configuration whose B_x all have rank 1 (M = 4),
so that the integrand is real-analytic inside every cell (no boundary eigenvalues); tanh-sinh refinement."""
import numpy as np, mpmath as mp, sys
src = open('k03_continuum.py').read().split('lamstar = np.log(2)')[0]
g = {}
exec(src, g)
rng = g['rng']; haar = g['haar']; tanh_sinh = g['tanh_sinh']; g_at = g['g_at']; h_li2 = g['h_li2']
PI = np.pi
d, M = 3, 4
N = 4 * d
Q = [None] * N
for k in range(d):
    U = haar(M); lab = rng.permutation(4)
    for a in range(4):
        Q[(k - d * a) % N] = np.outer(U[:, lab == a][:, 0], U[:, lab == a][:, 0].conj())
Bs = [Q[(x + d) % N] for x in range(N)]
ell = rng.dirichlet(np.ones(d)) * d
L = np.concatenate([[0.0], np.cumsum([ell[x % d] for x in range(N)])])
t = 2 * PI * L[:N] / N; tt = 2 * PI * L / N
for lam in [np.log(2) / (2 * PI), -0.3]:
    for h, umax in [(1/12, 3.0), (1/24, 3.2), (1/48, 3.4)]:
        tot = 0.0; minx = 1.0
        for x in range(N):
            dls, drs, ws = tanh_sinh(tt[x], tt[x + 1], h, umax)
            for dl, dr, w in zip(dls, drs, ws):
                gg = g_at(x, dl, dr, Bs, t)
                ev = np.linalg.eigvals(Bs[x] + 1j * gg)
                minx = min(minx, min(min(e.real, 1 - e.real) for e in ev))
                tot += w / (2 * PI) * sum(h_li2(lam, e) for e in ev) / M
        print(f"lam = {lam:+.4f} h = {h:.4f}: int u*/M - h(1/4) = {tot - h_li2(lam, 0.25 + 0j):+.3e}  (min distance of eigenvalues to strip edge {minx:.1e})", flush=True)
