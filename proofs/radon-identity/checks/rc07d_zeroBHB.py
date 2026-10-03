"""rc07d: adaptive re-run of the one RI-C point of rc02 whose fixed-panel quadrature had not converged:
zero_BHB_M4 (BHB = 0), c = 0.0225 i, where rc02 gave |Psi - E| = 1.13e-7 = |GL - TS|.  With BHB = 0 and small Im c, T_0 = PHP + c
- PHB BHP / c has eigenvalues of size ~ 1/Im c, so S_+ - S0_+ has a boundary layer at tau ~ (Im c)^2: tau-cuts at 10^-k and
1 - 10^-k (k = 1..14), recursive-bisection Gauss-Legendre (24/48 points) on every cut interval.  Instances regenerated with the
rc02 seed and call order; c reproduced with rc02's formula."""
import time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline
from rc_adapt import adaptive

mp.mp.dps = 44
out = open('rc07d_zeroBHB.log', 'w')
rng = random.Random(777)


def block(PHP, BHB, X):
    r = BHB.shape[0]; q = PHP.shape[0]
    H = sp.zeros(r + q, r + q)
    H[:r, :r] = BHB; H[r:, r:] = PHP; H[r:, :r] = X; H[:r, r:] = X.H
    return H


def randX(q, r, nr=9, den=4, scale=1):
    return sp.Matrix(q, r, lambda i, j: (sp.Rational(rng.randint(-nr, nr), den)
                                         + sp.I*sp.Rational(rng.randint(-nr, nr), den))*scale)


insts = [Inst.proj(herm(rng, 3), 1, 'rand_M3_r1'),
         Inst.proj(herm(rng, 4), 2, 'rand_M4_r2'),
         Inst.proj(herm(rng, 5), 3, 'rand_M5_r3'),
         Inst.proj(herm(rng, 6), 1, 'rank1B_M6'),
         Inst.proj(herm(rng, 6), 5, 'corank1_M6'),
         Inst.proj(with_spectrum(rng, [1, 1, 1, -2, -2]), 2, 'degenH_M5'),
         Inst.proj(block(with_spectrum(rng, [1, 1]), with_spectrum(rng, [-1, -1]), randX(2, 2)), 2, 'degen_blocks_M4'),
         Inst.proj(block(herm(rng, 2), sp.zeros(2, 2), randX(2, 2)), 2, 'zero_BHB_M4')]
I = insts[-1]
I.mpready()
s = float(I.normH)
im_s = sp.Rational(sp.Rational(1, 300)*sp.Rational(s).limit_denominator(4))
c = mp.mpc(0, mp.mpf(im_s.p)/im_s.q)
logline(out, 'rc07d: %s, c = %s (rc02: |Psi - E| = 1.13e-7 = |GL - TS|)' % (I.name, mp.nstr(c, 10)))


def f(t):
    dv = I.dvec(t)
    return I.S_plus(dv, c) - I.S0_plus(dv, c)


cuts = sorted(set([mp.mpf(0), mp.mpf(1)] + [mp.mpf(10)**(-k) for k in range(1, 15)]
                  + [1 - mp.mpf(10)**(-k) for k in range(1, 15)] + [mp.mpf(k)/8 for k in range(1, 8)]))
t0 = time.time()
tot = mp.mpc(0)
stats = [0, mp.mpf(0)]
for a, b in zip(cuts[:-1], cuts[1:]):
    tot += adaptive(f, a, b, mp.mpf(10)**(-36), 0, stats)
Ev = I.E(c)
logline(out, '  Psi = %s\n  E   = %s\n  |Psi - E| = %s   panels = %d, max panel |G24 - G48| = %s  (%.0fs)' % (
    mp.nstr(tot, 30), mp.nstr(Ev, 30), mp.nstr(abs(tot - Ev), 3), stats[0], mp.nstr(stats[1], 2), time.time() - t0))
# where is the layer?  show S_+ - S0_+ near tau = 0
for k in (8, 6, 5, 4, 3, 2, 1):
    t = mp.mpf(10)**(-k)
    logline(out, '  tau = 1e-%d: S_+ - S0_+ = %s' % (k, mp.nstr(f(t), 12)))
out.close()
