"""rc08: remaining minor claims.
 (1) remark after Lemma D: for tau <= 1/2 the C_+ roots and spec T_0 lie in {Im >= Im c, |y| <= 2 K_1}, K_1 = K + ||H||^2/Im c;
 (2) (A') general B: C_+ roots have Im y >= Im c/(b_n - tau), exactly m^+ of them; C_- roots Im y <= -Im c/(tau - b_1);
 (3) general-B trace identity S_+ + S_- = S0_+ + S0_-."""
import random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, logline

mp.mp.dps = 50
out = open('rc08_misc.log', 'w')
rng = random.Random(8080)

# (1)
mx_im = mp.mpf(0); mx_abs = mp.mpf(0); mx_T = mp.mpf(0); n = 0
for (M, r) in [(3, 1), (4, 2), (5, 3), (6, 1), (6, 5)]:
    I = Inst.proj(herm(rng, M), r, 'M%d_r%d' % (M, r))
    I.mpready()
    for _ in range(25):
        tau = mp.mpf(10)**(-rng.uniform(0, 10))/2
        c = mp.mpc(rng.uniform(-3, 3), 10**rng.uniform(-3, 1))
        K = I.normH + abs(c)
        K1 = K + I.normH**2/mp.im(c)
        up, dn, ys = I.split(I.dvec(tau), c)
        for z in up:
            mx_im = max(mx_im, mp.im(c)/mp.im(z))
            mx_abs = max(mx_abs, abs(z)/(2*K1))
        Bi = list(range(r)); Pi = list(range(r, M))
        HBB = mp.matrix([[I.H[i, j] + (c if i == j else 0) for j in Bi] for i in Bi])
        HPP = mp.matrix([[I.H[i, j] + (c if i == j else 0) for j in Pi] for i in Pi])
        HPB = mp.matrix([[I.H[i, j] for j in Bi] for i in Pi])
        T0 = HPP - HPB*mp.inverse(HBB)*HPB.H
        for t in (mp.eig(T0, left=False, right=False) if T0.rows > 1 else [T0[0, 0]]):
            mx_T = max(mx_T, max(mp.im(c)/mp.im(t), abs(t)/(2*K1)))
        n += 1
logline(out, '(1) %d samples: max Im c/Im y (C_+) = %s (<= 1) ; max |y|/(2K_1) = %s (<= 1) ; spec T_0: max ratio = %s (<= 1)' % (
    n, mp.nstr(mx_im, 8), mp.nstr(mx_abs, 8), mp.nstr(mx_T, 8)))

# (2), (3)
mxa = mp.mpf(0); mxb = mp.mpf(0); mxtr = mp.mpf(0); fails = 0; n = 0
for (b, m) in [([0, sp.Rational(1, 3), 1], [1, 1, 2]), ([-1, 0, sp.Rational(1, 2), 2], [2, 1, 1, 1]),
               ([0, sp.Rational(1, 10), sp.Rational(11, 100), 1], [1, 2, 1, 2])]:
    I = Inst(herm(rng, sum(m)), b, m, 'b=%s' % b)
    I.mpready()
    for _ in range(40):
        l = rng.randrange(I.n - 1)
        ta, tb = I.bmp[l], I.bmp[l + 1]
        tau = ta + (tb - ta)*mp.mpf(rng.uniform(1e-9, 1 - 1e-9))
        c = mp.mpc(rng.uniform(-3, 3), 10**rng.uniform(-6, 1))
        dv = I.dvec(tau)
        up, dn, ys = I.split(dv, c)
        n += 1
        if len(up) != I.nplus(dv):
            fails += 1
            continue
        for z in up:
            mxa = max(mxa, (mp.im(c)/(I.bmp[-1] - tau))/mp.im(z))
        for z in dn:
            mxb = max(mxb, (mp.im(c)/(tau - I.bmp[0]))/(-mp.im(z)))
        Sp, Sm = mp.fsum(up), mp.fsum(dn)
        mxtr = max(mxtr, abs(Sp + Sm - I.S0_plus(dv, c) - I.S0_minus(dv, c))/(abs(Sp) + abs(Sm)))
logline(out, '(2) %d samples, count failures %d ; max [Im c/(b_n - tau)]/Im y over C_+ = %s (<= 1) ; '
             'max [Im c/(tau - b_1)]/|Im y| over C_- = %s (<= 1)' % (n, fails, mp.nstr(mxa, 8), mp.nstr(mxb, 8)))
logline(out, '(3) general-B trace identity: max relative defect %s' % mp.nstr(mxtr, 3))
out.close()
