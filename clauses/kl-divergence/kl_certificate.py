"""
kl_certificate.py -- rigorous comparison of KL statistical strengths on |Phi_d> (uniform settings),
DKZ versus explicit competitor strategies, with exact rational certificates and interval arithmetic.

For a correlation q (conditional p(a,b|x,y)) and sigma = uniform:
  LOWER bound (competitor):  any r >= 0 with  sum_{xy} (1/4) r(lam_x, lam_y | x,y) <= 1  for every
      deterministic strategy lam  gives  KL(q) >= sum_{xyab} (1/4) q log r   (Gibbs inequality).
      r: rational, checked EXACTLY (fractions) against all d^4 strategies (or all d^3 shift orbits
      when r depends only on b - a; this is equivalent because the constraint value depends only on
      the differences b_y - a_x).
  UPPER bound (DKZ): any explicit local model p gives KL(q) <= sum (1/4) q log(q/p); p = mixture of
      deterministic strategies (shift-orbit averages) with rational weights summing exactly to 1.
q is evaluated with mpmath interval arithmetic (iv, 50 digits) from exact formulas:
  Fourier-diagonal strategies on |Phi_d>:  p(a,b|x,y) = P_xy(b-a)/d,
      P_xy(m) = d^-2 |sum_k exp(-i(theta_x(k)+eta_y(k))) w^{km}|^2,
  with phases given as exact rational multiples of pi.
Symmetry lemma (THEOREM.md, Lemma S): for DKZ on |Phi_d> the optimal setting distribution is uniform,
so the vDGG strengths S^UNI = S^UC = S^COR for DKZ; for any competitor S^X >= S^UNI.
"""
import itertools
import sys
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf
from zd import zd_vertices, kl_zd, fourier_P

iv.dps = 50
LN2 = iv.log(iv.mpf(2))


def P_interval(theta_q, eta_q, d):
    """theta_q, eta_q: 2 x d lists of Fractions (phase / pi). returns P[x][y][m] as iv intervals."""
    PI = iv.pi
    P = [[[None] * d for _ in range(2)] for _ in range(2)]
    for x in range(2):
        for y in range(2):
            for m in range(d):
                re = iv.mpf(0)
                im = iv.mpf(0)
                for k in range(d):
                    # phase = -(theta+eta)*pi + 2 pi k m / d
                    ph = PI * (-(iv.mpf(theta_q[x][k].numerator) / theta_q[x][k].denominator
                                 + iv.mpf(eta_q[y][k].numerator) / eta_q[y][k].denominator)
                               + iv.mpf(2 * k * m) / d)
                    re += iv.cos(ph)
                    im += iv.sin(ph)
                P[x][y][m] = (re * re + im * im) / (d * d)
    return P


def to_float_P(P, d):
    return np.array([[[float(mpf(P[x][y][m].mid)) for m in range(d)] for y in range(2)] for x in range(2)])


def lower_bound_zd(P_iv, d, shrink=Fr(1, 10 ** 9)):
    """dual certificate from the numerical optimum (shift-invariant r(x,y,m))."""
    Pf = to_float_P(P_iv, d)
    ub, lb, w, r = kl_zd(Pf)
    S, V = zd_vertices(d)
    Pl = (w @ V).reshape(2, 2, d)
    # r(x,y,m) = P/Pl  (test factor), rational, slightly shrunk, then exact normalisation
    R = [[[Fr(float(Pf[x, y, m] / Pl[x, y, m])).limit_denominator(10 ** 12) for m in range(d)]
          for y in range(2)] for x in range(2)]
    # exact check over all shift orbits lam = (0, a1, b0, b1)
    Mx = Fr(0)
    for (a1, b0, b1) in itertools.product(range(d), repeat=3):
        a = (0, a1)
        b = (b0, b1)
        s = sum(R[x][y][(b[y] - a[x]) % d] for x in range(2) for y in range(2)) / 4
        if s > Mx:
            Mx = s
    Rn = [[[R[x][y][m] / Mx * (1 - shrink) for m in range(d)] for y in range(2)] for x in range(2)]
    # certified lower bound: sum_xy 1/4 sum_m P log r
    L = iv.mpf(0)
    for x in range(2):
        for y in range(2):
            for m in range(d):
                rr = Rn[x][y][m]
                L += P_iv[x][y][m] * iv.log(iv.mpf(rr.numerator) / rr.denominator) / 4
    return L / LN2, float(ub / np.log(2)), Mx


def upper_bound_zd(P_iv, d):
    """explicit shift-invariant local model with rational weights."""
    Pf = to_float_P(P_iv, d)
    ub, lb, w, r = kl_zd(Pf)
    S, V = zd_vertices(d)
    keep = np.where(w > 1e-13)[0]
    W = [Fr(float(w[i])).limit_denominator(10 ** 14) for i in keep]
    tot = sum(W)
    W = [x / tot for x in W]                         # exact normalisation
    Vr = V.reshape(-1, 2, 2, d)
    Pl = [[[Fr(0)] * d for _ in range(2)] for _ in range(2)]
    for wi, i in zip(W, keep):
        for x in range(2):
            for y in range(2):
                m = int(np.argmax(Vr[i, x, y]))
                Pl[x][y][m] += wi
    U = iv.mpf(0)
    for x in range(2):
        for y in range(2):
            for m in range(d):
                pl = Pl[x][y][m]
                assert pl > 0
                U += P_iv[x][y][m] * iv.log(P_iv[x][y][m] / (iv.mpf(pl.numerator) / pl.denominator)) / 4
    return U / LN2, float(lb / np.log(2))


def dkz_phases_q(d):
    # theta_x(k) = 2 k alpha_x / d (units of pi), eta_y(k) = -2 k beta_y / d ; alpha=(1/2,0), beta=(1/4,-1/4)
    th = [[Fr(2 * k, d) * Fr(1, 2) for k in range(d)], [Fr(0)] * d]
    et = [[-Fr(2 * k, d) * Fr(1, 4) for k in range(d)], [Fr(2 * k, d) * Fr(1, 4) for k in range(d)]]
    return th, et


def r5_phases_q():
    d = 5
    th = [[Fr(0)] * d, [Fr(6 * k, 5) + (1 if k == 4 else 0) for k in range(d)]]
    psi0 = [Fr(0), Fr(0), Fr(1), Fr(1), Fr(1, 2)]
    psi1 = [Fr(0), Fr(0), Fr(1), Fr(1), Fr(3, 2)]
    et = [psi0, [Fr(-2 * k, 5) + psi1[k] for k in range(d)]]
    return th, et


def phases_from_file(fn, denom=10 ** 6):
    X = np.load(fn)
    th = [[Fr(float(X[x, k] / np.pi)).limit_denominator(denom) for k in range(X.shape[1])] for x in range(2)]
    et = [[Fr(float(X[2 + y, k] / np.pi)).limit_denominator(denom) for k in range(X.shape[1])] for y in range(2)]
    return th, et


def certify(name, th, et, d, mode):
    P = P_interval(th, et, d)
    if mode == "lower":
        L, ub, Mx = lower_bound_zd(P, d)
        print(f"  {name} (d={d}): certified KL >= {float(mpf(L.a)):.12f} bits   (numerical value {ub:.12f}; "
              f"test-factor normaliser {float(Mx):.12f})", flush=True)
        return L
    U, lb = upper_bound_zd(P, d)
    print(f"  {name} (d={d}): certified KL <= {float(mpf(U.b)):.12f} bits   (numerical value {lb:.12f})", flush=True)
    return U


if __name__ == "__main__":
    print("Certified KL statistical strengths on |Phi_d> (uniform settings), bits")
    results = {}
    for d in (3, 4, 5, 6, 7):
        th, et = dkz_phases_q(d)
        results[("DKZ", d)] = certify("DKZ", th, et, d, "upper")
    # competitors
    comp = {4: phases_from_file("fgrad_kl_d4_s1.npy"), 5: r5_phases_q(),
            6: phases_from_file("fgrad_kl_d6_s1.npy"), 7: phases_from_file("fgrad_kl_d7_s1.npy")}
    for d, (th, et) in comp.items():
        L = certify("competitor", th, et, d, "lower")
        U = results[("DKZ", d)]
        verdict = "COMPETITOR STRICTLY BETTER (rigorous)" if L.a > U.b else "not separated"
        print(f"  d={d}: {verdict}: lower(competitor) - upper(DKZ) >= {float(mpf((L - U).a)):.6f} bits", flush=True)
