"""Which (cells, configuration, rotation) attains Q^ell(rot_c Q) = N^2 Phi_c in k02?  (debug of a_max ~ 0)"""
import numpy as np, mpmath as mp, sys
src = open('k02_cells.py').read().split('report = dict(')[0]
g = {}
exec(src, g)
Kernel, rand_V, Qconf_from_V, pairmat, Nvec, rng = g['Kernel'], g['rand_V'], g['Qconf_from_V'], g['pairmat'], g['Nvec'], g['rng']
for d in [3, 4, 5]:
    N = 4 * d
    target = float(mp.mpf(N) ** 2 * mp.catalan / mp.pi ** 2)
    for supp in ['full', 'two', 'drop1']:
        e = rng.dirichlet(np.ones(d)) * d
        if supp == 'two':
            keep = [0, 1]
            e = np.array([e[i] if i in keep else 0 for i in range(d)]); e = e / e.sum() * d
        if supp == 'drop1':
            e[1] = 0; e = e / e.sum() * d
        Ker = Kernel(list(e), d)
        for M in [2, 3]:
            V = rand_V(d, M)
            Tab = pairmat(Qconf_from_V(V, d), d)
            vals = np.array([Ker.Q(Tab, c) - target for c in range(N)])
            print(f"d={d} {supp:5s} M={M}: max_c (Q^ell(rot_c Q) - N^2 Phi_c) = {vals.max():+.3e} at c = {vals.argmax()}; min = {vals.min():+.3e}")
