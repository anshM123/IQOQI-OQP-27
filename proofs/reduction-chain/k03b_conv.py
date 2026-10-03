"""Convergence of the boundary mean-value identity int u*_lam dm = M h_lam(1/4) (item 2) under tanh-sinh refinement."""
import numpy as np, mpmath as mp, sys
sys.argv = ['x']
src = open('k03_continuum.py').read().split('lamstar = np.log(2)')[0]
g = {}
exec(src, g)
rng = g['rng']; Qconf = g['Qconf']; tanh_sinh = g['tanh_sinh']; g_at = g['g_at']; h_li2 = g['h_li2']
PI = np.pi
d, M = 3, 2
ell = rng.dirichlet(np.ones(d)) * d
N = 4 * d
Q = Qconf(d, M); Bs = [Q[(x + d) % N] for x in range(N)]
L = np.concatenate([[0.0], np.cumsum([ell[x % d] for x in range(N)])])
t = 2 * PI * L[:N] / N; tt = 2 * PI * L / N
lam = np.log(2) / (2 * PI)
for h, umax in [(1/12, 3.0), (1/24, 3.2), (1/48, 3.4), (1/96, 3.6)]:
    tot = 0.0
    for x in range(N):
        dls, drs, ws = tanh_sinh(tt[x], tt[x + 1], h, umax)
        for dl, dr, w in zip(dls, drs, ws):
            gg = g_at(x, dl, dr, Bs, t)
            ev = np.linalg.eigvals(Bs[x] + 1j * gg)
            tot += w / (2 * PI) * sum(h_li2(lam, e) for e in ev) / M
    print(f"h = {h:.4f}: int u*/M - h(1/4) = {tot - h_li2(lam, 0.25 + 0j):+.3e}", flush=True)
