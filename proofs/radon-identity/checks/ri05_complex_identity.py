"""ri05: the complex Radon identity (PROOF.md Theorem RI-C) and Step 1 of its proof.

  Psi(c) := int_0^1 [S_+(tau,c) - S0_+(tau,c)] dtau  =  E(c) := Tr[(H_d + c)Log(H_d + c)] - Tr[(H + c)Log(H + c)],  Im c > 0.
  Step 1: d/dc Psi_delta(c) = (Lam_+ - Lam0_+)(1 - delta, c) - (Lam_+ - Lam0_+)(delta, c),  Psi_delta = int_delta^{1-delta}.
For Im c small the integrand has sharp (but analytic) features near the real-axis branch points tau*(Re c); these are added
as quadrature nodes (with clusters at distance ~ Im c) so that tanh-sinh resolves them.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, standard_instances

mp.mp.dps = 30
rng = np.random.default_rng(5)
insts = standard_instances()

def nodes_for(I, c):
    pts = [mp.mpf(0), mp.mpf(1)/4, mp.mpf(1)/2, mp.mpf(3)/4, mp.mpf(1)]
    if mp.im(c) < mp.mpf('0.2'):
        bps = I.breakpoints(mp.re(c))
        eps = mp.im(c)
        for b in bps:
            for k in [-30, -10, -3, -1, 0, 1, 3, 10, 30]:
                t = b + k*eps
                if 0 < t < 1:
                    pts.append(t)
    return sorted(set(pts))

worst = mp.mpf(0); rows = []
for I in insts:
    cs = [mp.mpc(rng.normal()*1.5, x) for x in [2.0, 0.5, 0.05]] + [mp.mpc(mp.re(I.lam[0]) + mp.mpf('0.1'), '0.003')]
    for c in cs:
        nd = nodes_for(I, c)
        ps = mp.quad(lambda t: I.diff_plus(t, c), nd, maxdegree=8)
        e = I.E(c)
        err = abs(ps - e)
        worst = max(worst, err/(1 + abs(e)))
        rows.append((I.name, c, ps, e, err))
        print(f'{I.name:18s} c={mp.nstr(c, 5):>24s}  Psi={mp.nstr(ps, 16):>40s}  |Psi - E|={mp.nstr(err, 3)}')
print(f'max relative |Psi - E| over {len(rows)} (instance, c) pairs: {mp.nstr(worst, 3)}')

# Step 1: derivative of the truncated integral
print('Step 1 check: d/dc Psi_delta vs boundary terms of Lam_+ - Lam0_+')
worst1 = mp.mpf(0)
for I in insts[:6]:
    c = mp.mpc(rng.normal(), 0.7)
    for dl in [mp.mpf('0.1'), mp.mpf('1e-3')]:
        Pd = lambda h: mp.quad(lambda t: I.diff_plus(t, c + h), [dl, mp.mpf(1)/2, 1 - dl])
        der = mp.diff(Pd, 0)
        bt = (I.Lam_plus(1 - dl, c) - I.Lam0_plus(1 - dl, c)) - (I.Lam_plus(dl, c) - I.Lam0_plus(dl, c))
        worst1 = max(worst1, abs(der - bt))
        print(f'  {I.name:18s} delta={mp.nstr(dl, 2):>6s}: d/dc Psi_delta = {mp.nstr(der, 14):>36s}, boundary terms = {mp.nstr(bt, 14):>36s}')
print(f'Step 1: max |difference| = {mp.nstr(worst1, 3)}')
print('ALL OK' if worst < 1e-15 and worst1 < 1e-15 else 'CHECK')
