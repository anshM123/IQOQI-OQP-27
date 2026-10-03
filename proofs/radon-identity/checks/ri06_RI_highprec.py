"""ri06: the Radon identity (RI) itself at high precision, its shifted form, and the boundary-value step (PROOF.md s.2).

 (1) RI:  L(H) = (1/2pi) int_0^1 sum_i |Im y_i(tau)| dtau  =  R(H) = Tr H_+ - Tr (H_d)_+,
     quadrature split at the exact branch points (real roots in (0,1) of the y-discriminant, a polynomial of degree <= M(M-1)
     in tau), tanh-sinh on each piece, 30 digits;
 (2) shifted form L(H + c0) = R(H + c0) on a grid of c0 crossing all eigenvalues of H and H_d (the profile is continuous,
     piecewise linear, with kinks exactly at -spec H (slope jump +1) and -spec H_d (slope jump -1));
 (3) the boundary-value step: Im Psi(c0 + i eps)/pi -> L(H + c0) as eps -> 0+ (Psi evaluated by its closed form E, which
     ri05 verifies; the limit of Im E is explicit), and directly by quadrature for moderate eps.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, rand_herm, standard_instances

mp.mp.dps = 30
insts = standard_instances()
rng = np.random.default_rng(31)
# larger-scale and wide-spectrum instances
insts.append(Inst(rand_herm(rng, 4, 40.0), 2, 'scale40_M4_r2'))
H = rand_herm(rng, 5, 1.0); H[0, 0] += 25; H[4, 4] -= 30
insts.append(Inst(H, 2, 'wide_spec_M5_r2'))
insts.append(Inst(rand_herm(rng, 6, 2.0), 1, 'rank1B_M6'))
insts.append(Inst(rand_herm(rng, 6, 2.0), 5, 'corank1_M6'))

print('(1) RI at c0 = 0')
worst = mp.mpf(0)
for I in insts:
    bps = I.breakpoints(0)
    Lv = I.L(0, bps); Rv = I.R(0)
    worst = max(worst, abs(Lv - Rv))
    print(f'  {I.name:18s} M={I.M} r={I.r} #branchpts={len(bps):2d}  L={mp.nstr(Lv, 22):>26s}  R={mp.nstr(Rv, 22):>26s}  |L-R|={mp.nstr(abs(Lv - Rv), 3)}')
print(f'  max |L - R| = {mp.nstr(worst, 3)}')

print('(2) shifted form L(H + c0) = R(H + c0)')
worst2 = mp.mpf(0)
for I in [insts[1], insts[4], insts[10]]:
    lo = -max(I.lam + I.lam0) - mp.mpf('0.3'); hi = -min(I.lam + I.lam0) + mp.mpf('0.3')
    grid = [lo + (hi - lo)*k/8 for k in range(9)] + [-I.lam[0], -I.lam0[-1]]
    for c0 in grid:
        Lv = I.L(c0); Rv = I.R(c0)
        worst2 = max(worst2, abs(Lv - Rv))
        print(f'  {I.name:18s} c0={mp.nstr(c0, 8):>12s}  L={mp.nstr(Lv, 18):>22s}  R={mp.nstr(Rv, 18):>22s}  diff={mp.nstr(abs(Lv - Rv), 3)}')
print(f'  max |L - R| = {mp.nstr(worst2, 3)}')

print('(3) boundary values: Im Psi(c0 + i eps)/pi -> L(H + c0)')
I = insts[4]; c0 = mp.mpf('0.17')
Lv = I.L(c0)
for eps in ['0.3', '0.1', '0.03', '0.01', '1e-3', '1e-4', '1e-6']:
    e = mp.mpf(eps)
    imE = mp.im(I.E(c0 + 1j*e))/mp.pi
    line = f'  eps={eps:>6s}: Im E/pi = {mp.nstr(imE, 16):>20s}  (Im E/pi - L = {mp.nstr(imE - Lv, 3):>10s})'
    if e >= mp.mpf('0.03'):
        q = mp.quad(lambda t: mp.im(I.diff_plus(t, c0 + 1j*e)), [0, 0.25, 0.5, 0.75, 1])/mp.pi
        line += f';  quadrature Im Psi/pi = {mp.nstr(q, 16)}'
    print(line)
print(f'  L(H + c0) = {mp.nstr(Lv, 16)},  R(H + c0) = {mp.nstr(I.R(c0), 16)}')
print('ALL OK' if worst < 1e-20 and worst2 < 1e-20 else 'CHECK')
