"""rc02b: Lemma A(a) ratio Im c/((1-tau) Im y) for C_+ roots (and Im c/(tau|Im y|) for C_- roots) is <= 1 with equality iff
the eigenvector lies in ran P (resp. ran B); rc02 printed max = 1.0 (12 digits).  Here: the maximum minus 1, per instance, at
dps 60, same instances and same random sample stream as rc02 section (2)."""
import random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum

rng = random.Random(777)
def block(PHP, BHB, X):
    r = BHB.shape[0]; q = PHP.shape[0]
    H = sp.zeros(r + q, r + q)
    H[:r, :r] = BHB; H[r:, r:] = PHP; H[r:, :r] = X; H[:r, r:] = X.H
    return H
def randX(q, r, nr=9, den=4, scale=1):
    return sp.Matrix(q, r, lambda i, j: (sp.Rational(rng.randint(-nr, nr), den) + sp.I*sp.Rational(rng.randint(-nr, nr), den))*scale)
insts = [Inst.proj(herm(rng, 3), 1, 'rand_M3_r1'), Inst.proj(herm(rng, 4), 2, 'rand_M4_r2'), Inst.proj(herm(rng, 5), 3, 'rand_M5_r3'),
         Inst.proj(herm(rng, 6), 1, 'rank1B_M6'), Inst.proj(herm(rng, 6), 5, 'corank1_M6'),
         Inst.proj(with_spectrum(rng, [1, 1, 1, -2, -2]), 2, 'degenH_M5'),
         Inst.proj(block(with_spectrum(rng, [1, 1]), with_spectrum(rng, [-1, -1]), randX(2, 2)), 2, 'degen_blocks_M4'),
         Inst.proj(block(herm(rng, 2), sp.zeros(2, 2), randX(2, 2)), 2, 'zero_BHB_M4'),
         Inst.proj(block(herm(rng, 3), herm(rng, 2), randX(3, 2, scale=sp.Rational(1, 10**6))), 2, 'near_comm_1e-6_M5'),
         Inst.proj((herm(rng, 4)*1000).applyfunc(sp.expand), 2, 'scale1e3_M4')]
mp.mp.dps = 60
out = open('rc02b_lemmaA_equality.log', 'w')
for I in insts:
    I.mpready()
    mx = mp.mpf(-1)
    for _ in range(40):
        u = rng.random()
        tau = mp.mpf(10)**(-rng.uniform(0, 14)) if u < 0.3 else (1 - mp.mpf(10)**(-rng.uniform(0, 14)) if u < 0.6 else mp.mpf(rng.random()))
        c = mp.mpc(rng.uniform(-2, 2)*float(I.normH), mp.mpf(10)**rng.uniform(-25, 1))
        up, dn, ys = I.split(I.dvec(tau), c)
        for z in up:
            mx = max(mx, (mp.im(c)/(1 - tau))/mp.im(z) - 1)
        for z in dn:
            mx = max(mx, (mp.im(c)/tau)/(-mp.im(z)) - 1)
    line = '  %-20s max(ratio) - 1 = %s' % (I.name, mp.nstr(mx, 5))
    print(line); out.write(line + '\n')
out.close()
