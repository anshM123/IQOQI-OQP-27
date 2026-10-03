"""
ref_prop11.py -- referee check of Proposition 11 (v_c(DKZ_d) = 2/I_ME(d) exactly, d = 3, 4, 5), independent of P2's
dkz_exact.py and WITHOUT any facet list of K_d:

  * arithmetic in the cyclotomic field Q(zeta), zeta = exp(i pi/(4d)), elements = polynomials mod the (irreducible)
    cyclotomic polynomial Phi_{8d}; zero test exact; sign of a real element decided by a 120-digit evaluation
    (only used for strictly nonzero elements; the observed magnitudes are >= 1e-6, so the decision is safe);
  * T^{v*}_xy(m) = v* h_xy(m) + (1 - v*)/d, v* = 2/I_ME(d), built exactly;
  * a float LP over the d^3 covariant strategies (Lemma 8) suggests a support; the linear system on that support is
    solved EXACTLY in Q(zeta) and ALL 4d marginal equations and mu >= 0 are verified exactly.
  => T^{v*} is realised by a distribution on M, so DKZ_d at visibility 2/I_ME(d) is local (Lemma 8).
usage: python ref_prop11.py
"""
import sys
import time

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import linprog

mp.mp.dps = 120
X = sp.symbols("X")
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
DELTA4 = {(0, 0): 1, (0, 1): -1, (1, 0): 3, (1, 1): 1}       # 4 * delta_xy (P2 orientation, Lemma 7)


class Cyc:
    def __init__(self, d):
        self.N = 8 * d
        self.Phi = sp.Poly(sp.cyclotomic_poly(self.N, X), X, domain="QQ")
        self.z = mp.exp(1j * mp.pi / (4 * d))

    def el(self, p):
        return sp.Poly(p, X, domain="QQ").rem(self.Phi)

    def zeta_pow(self, k):
        k %= self.N
        return self.el(X ** k)

    def cos_k(self, k):
        """cos(k pi/(4d)) = (zeta^k + zeta^-k)/2."""
        return self.el((self.zeta_pow(k) + self.zeta_pow(-k)).as_expr() / 2)

    def mul(self, a, b):
        return (a * b).rem(self.Phi)

    def inv(self, a):
        r = sp.Poly(sp.invert(a.as_expr(), self.Phi.as_expr(), X), X, domain="QQ")
        assert self.mul(a, r) == sp.Poly(1, X, domain="QQ")
        return r

    def num(self, a):
        cs = a.all_coeffs()[::-1]
        return sum(mp.mpf(sp.Rational(c).p) / sp.Rational(c).q * self.z ** k for k, c in enumerate(cs))


def run(d):
    t0 = time.time()
    K = Cyc(d)
    one = sp.Poly(1, X, domain="QQ")
    # I_ME = 4/(d(d-1)) sum_j (d-j) / cos(pi j/(2d)) ; pi j/(2d) = 2j * pi/(4d)
    S = sp.Poly(0, X, domain="QQ")
    for j in range(1, d):
        S = S + K.inv(K.cos_k(2 * j)) * (d - j)
    ime = (S * sp.Rational(4, d * (d - 1))).rem(K.Phi)
    vstar = (K.inv(ime) * 2).rem(K.Phi)
    T = {}
    for xy in LINKS:
        for m in range(d):
            k = 4 * m - DELTA4[xy]                       # pi (m - delta)/d = k pi/(4d)
            s2 = ((one - K.cos_k(2 * k)) * sp.Rational(1, 2)).rem(K.Phi)     # sin^2(k pi/(4d))
            h = (K.inv(s2) * sp.Rational(1, 2 * d * d)).rem(K.Phi)
            T[(xy, m)] = (K.mul(vstar, h) + (one - vstar) * sp.Rational(1, d)).rem(K.Phi)
    ok = all(sum((T[(xy, m)] for m in range(d)), sp.Poly(0, X, domain="QQ")).rem(K.Phi) == one for xy in LINKS)
    # float LP over covariant strategies (m00, m01, m10), m11 = m01 + m10 - m00
    St = [(a, b, c, (b + c - a) % d) for a in range(d) for b in range(d) for c in range(d)]
    rows = [(xy, m) for xy in LINKS for m in range(d)]
    A = np.array([[1.0 if s[LINKS.index(xy)] == m else 0.0 for s in St] for (xy, m) in rows])
    Tf = np.array([float(mp.re(K.num(T[r]))) for r in rows])
    res = linprog(np.zeros(len(St)), A_eq=A, b_eq=Tf, bounds=[(0, None)] * len(St), method="highs-ds")
    assert res.status == 0, res.message
    supp = [i for i in range(len(St)) if res.x[i] > 1e-12]
    # independent columns of the support, then independent rows
    cols = []
    for i in supp:
        if np.linalg.matrix_rank(A[:, cols + [i]]) == len(cols) + 1:
            cols.append(i)
    sel = []
    for r in range(len(rows)):
        if np.linalg.matrix_rank(A[np.ix_(sel + [r], cols)]) == len(sel) + 1:
            sel.append(r)
        if len(sel) == len(cols):
            break
    n = len(cols)
    # exact Gauss-Jordan in Q(zeta)
    M = [[sp.Poly(int(A[sel[i], cols[j]]), X, domain="QQ") for j in range(n)] + [T[rows[sel[i]]]] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if not M[r][c].is_zero)
        M[c], M[piv] = M[piv], M[c]
        iv = K.inv(M[c][c])
        M[c] = [K.mul(x, iv) for x in M[c]]
        for r in range(n):
            if r != c and not M[r][c].is_zero:
                f = M[r][c]
                M[r] = [(x - K.mul(f, y)).rem(K.Phi) for x, y in zip(M[r], M[c])]
    w = [M[i][n] for i in range(n)]
    # exact verification of ALL 4d equations
    for r, (xy, m) in enumerate(rows):
        lhs = sp.Poly(0, X, domain="QQ")
        for j, i in enumerate(cols):
            if A[r, i] == 1.0:
                lhs = lhs + w[j]
        ok &= (lhs - T[(xy, m)]).rem(K.Phi).is_zero
    # nonnegativity: each weight is real; exact zero or numerically clearly positive
    mags = []
    for x in w:
        if x.is_zero:
            mags.append(0)
            continue
        val = K.num(x)
        ok &= abs(mp.im(val)) < mp.mpf(10) ** -100 and mp.re(val) > mp.mpf(10) ** -30
        mags.append(float(mp.re(val)))
    print(f"d={d}: field Q(zeta_{K.N}) of degree {K.Phi.degree()}; v* = {mp.nstr(mp.re(K.num(vstar)), 15)}; "
          f"support {n} covariant strategies; all {4 * d} marginal equations exact; min weight {min(mags):.3e}; "
          f"=> T^(2/I_ME) local: {ok}  ({time.time() - t0:.0f}s)", flush=True)
    return ok


if __name__ == "__main__":
    ds = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    ok = all(run(d) for d in ds)
    print("RESULT:", "PASS" if ok else "FAIL")
