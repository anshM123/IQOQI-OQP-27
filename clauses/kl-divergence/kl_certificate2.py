"""
kl_certificate2.py -- certified KL lower bounds (exact rational test factors + interval arithmetic)
for Fourier-diagonal measurements with a Schmidt-diagonal state lam (clock basis):
    P_xy(m) = (1/d) | sum_k lam_k e^{-i(theta_x(k)+eta_y(k))} w^{km} |^2,   p(a,b|x,y) = P_xy(b-a)/d.
(lam = maximally entangled when all lam_k = d^-1/2.)  Phases are rounded to rational multiples of pi,
lam to rationals and renormalised in interval arithmetic, so the certified number refers to an
explicit valid quantum strategy.
usage: kl_certificate2.py file1.npy [file2.npy ...]   (files from fourier_grad.py: 4 x d; or from
fourier_state.py: 5 x d with lam in the last row)
"""
import sys
import itertools
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf
from zd import zd_vertices, kl_zd

iv.dps = 50
LN2 = iv.log(iv.mpf(2))


def P_interval(th, et, lamq, d):
    PI = iv.pi
    lam = [iv.mpf(l.numerator) / l.denominator for l in lamq]
    nrm = iv.sqrt(sum(l * l for l in lam))
    lam = [l / nrm for l in lam]
    P = [[[None] * d for _ in range(2)] for _ in range(2)]
    for x in range(2):
        for y in range(2):
            for m in range(d):
                re = iv.mpf(0)
                im = iv.mpf(0)
                for k in range(d):
                    ph = PI * (-(iv.mpf(th[x][k].numerator) / th[x][k].denominator
                                 + iv.mpf(et[y][k].numerator) / et[y][k].denominator) + iv.mpf(2 * k * m) / d)
                    re += lam[k] * iv.cos(ph)
                    im += lam[k] * iv.sin(ph)
                P[x][y][m] = (re * re + im * im) / d
    return P


def certify_lower(P, d):
    Pf = np.array([[[float(mpf(P[x][y][m].mid)) for m in range(d)] for y in range(2)] for x in range(2)])
    ub, lb, w, r = kl_zd(Pf)
    S, V = zd_vertices(d)
    Pl = (w @ V).reshape(2, 2, d)
    R = [[[Fr(float(Pf[x, y, m] / Pl[x, y, m])).limit_denominator(10 ** 12) for m in range(d)]
          for y in range(2)] for x in range(2)]
    Mx = Fr(0)
    for (a1, b0, b1) in itertools.product(range(d), repeat=3):
        a = (0, a1)
        b = (b0, b1)
        s = sum(R[x][y][(b[y] - a[x]) % d] for x in range(2) for y in range(2)) / 4
        Mx = max(Mx, s)
    Rn = [[[R[x][y][m] / Mx * (1 - Fr(1, 10 ** 9)) for m in range(d)] for y in range(2)] for x in range(2)]
    L = iv.mpf(0)
    for x in range(2):
        for y in range(2):
            for m in range(d):
                rr = Rn[x][y][m]
                L += P[x][y][m] * iv.log(iv.mpf(rr.numerator) / rr.denominator) / 4
    return L / LN2, ub / np.log(2)


if __name__ == "__main__":
    for fn in sys.argv[1:]:
        X = np.load(fn)
        d = X.shape[1]
        th = [[Fr(float(X[x, k] / np.pi)).limit_denominator(10 ** 6) for k in range(d)] for x in range(2)]
        et = [[Fr(float(X[2 + y, k] / np.pi)).limit_denominator(10 ** 6) for k in range(d)] for y in range(2)]
        if X.shape[0] >= 5:
            lamq = [Fr(float(abs(X[4, k]))).limit_denominator(10 ** 9) for k in range(d)]
        else:
            lamq = [Fr(1)] * d
        P = P_interval(th, et, lamq, d)
        L, num = certify_lower(P, d)
        print(f"{fn}: d={d}, state {'max-ent' if X.shape[0] < 5 else 'Schmidt-diagonal'}: certified KL >= "
              f"{float(mpf(L.a)):.12f} bits  (numerical {num:.12f})", flush=True)
