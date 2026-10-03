"""
phi3.py -- d = 3 (Theorem 3 of THEOREM.md): exact checks.

(1) Every facet of L(2,2,3) is positivity, a lifted CHSH inequality (each measurement coarse-grained by {k}|{rest}) or
    a relabelled CGLMP_3 (facets223.py, exact double description) -- re-derived here with the generating data kept.
(2) Lifted CHSH:  value under u (Gill noise, uniform on 3 x 3) lies in {-2/9, +2/9} for all 648 facets.
    CGLMP class:   value under u is exactly 0 for all 432 facets.
(3) Exact thresholds:  2/I_ME(3) = 3 sqrt3 - 9/2;  lifted-CHSH threshold bound 4/(3 sqrt2 + 1) > 2/I_ME(3);
    Phi_2 counterexample 8/(9 sqrt2 - 1) < 2/I_ME(3);  Phi_D block constructions (D odd) below 2/I_ME(3) iff D >= 17.
(4) I_3(DKZ_3) = I_ME(3) = (12 + 8 sqrt3)/9 exactly (sympy, radicals), DKZ_3 in the convention of dkz_cert.py.
(5) Numerical sanity check (not used in the proof): max of the CHSH value on Phi_3 over all +-1 observables (any
    traces) found by local optimisation equals (4 sqrt2 + 2)/3.
"""
import itertools
import sys
from fractions import Fraction as Fr

import sympy as sp

from facets223 import (D, apply_symmetry, cglmp_beta, ineq_from_full, positivity_ineqs, zero_beta)

THIRD = Fr(1, 9)


def value_u(beta):
    return sum(beta[x][y][a][b] for x in range(2) for y in range(2) for a in range(D) for b in range(D)) * THIRD


def lifted_chsh_with_data():
    out = {}
    for Sa0, Sa1, Sb0, Sb1 in itertools.product(range(D), repeat=4):
        for s in itertools.product((1, -1), repeat=4):
            if s[0] * s[1] * s[2] * s[3] != -1:
                continue
            Sa, Sb = (Sa0, Sa1), (Sb0, Sb1)
            beta = zero_beta()
            for x in range(2):
                for y in range(2):
                    for a in range(D):
                        for b in range(D):
                            beta[x][y][a][b] += s[2 * x + y] * (1 if a == Sa[x] else -1) * (1 if b == Sb[y] else -1)
            h = ineq_from_full(beta, 2)
            out.setdefault(h, []).append(value_u(beta))
    return out


def cglmp_with_data():
    beta0 = cglmp_beta()
    out = {}
    perms_all = list(itertools.permutations(range(D)))
    for P in itertools.product(perms_all, repeat=4):
        for sx, sy, spp in itertools.product((0, 1), repeat=3):
            b = apply_symmetry(beta0, P, sx, sy, spp)
            out.setdefault(ineq_from_full(b, 2), []).append(value_u(b))
    return out


def run():
    ok = True
    F = {}
    for line in open("facets223.txt"):
        if line.startswith("#"):
            continue
        a, c = line.split(";")
        F[tuple(int(t) for t in a.split())] = c.strip()
    chsh = lifted_chsh_with_data()
    cgl = cglmp_with_data()
    pos = positivity_ineqs()
    allc = set(chsh) | set(cgl) | pos
    ok &= (set(F) == allc and len(F) == 1116)
    print(f"(1) facet list = positivity ({len(pos)}) + lifted CHSH ({len(chsh)}) + CGLMP orbit ({len(cgl)}): "
          f"{set(F) == allc}")
    vals_chsh = set(v for L in chsh.values() for v in L)
    vals_cgl = set(v for L in cgl.values() for v in L)
    ok &= vals_chsh <= {Fr(2, 9), Fr(-2, 9)} and vals_cgl == {Fr(0)}
    print(f"(2) CHSH_F(u) over all lifted CHSH representations: {sorted(vals_chsh)};  I_F(u) over the CGLMP orbit: "
          f"{sorted(vals_cgl)}")
    # (3) exact thresholds with sympy (radicals)
    s2, s3 = sp.sqrt(2), sp.sqrt(3)
    IME3 = sp.Rational(4, 6) * sum((3 - j) * sp.sec(sp.pi * j / 6) for j in (1, 2))
    IME3 = sp.nsimplify(sp.simplify(IME3))
    target = (12 + 8 * s3) / 9
    ok &= sp.simplify(IME3 - target) == 0
    vstar = sp.radsimp(2 / target)
    ok &= sp.simplify(vstar - (3 * s3 - sp.Rational(9, 2))) == 0
    vchsh = (2 - sp.Rational(2, 9)) / ((4 * s2 + 2) / 3 - sp.Rational(2, 9))
    ok &= sp.simplify(vchsh - 4 / (3 * s2 + 1)) == 0
    vphi2 = sp.Rational(8, 1) / (9 * s2 - 1)
    # exact comparisons of algebraic numbers: sympy decides the sign of a - b exactly via minimal polynomials
    c1 = sp.simplify(vchsh - vstar).is_positive
    c2 = sp.simplify(vstar - vphi2).is_positive
    ok &= bool(c1) and bool(c2)
    print(f"(3) I_ME(3) = {target} (exact), 2/I_ME(3) = 3 sqrt3 - 9/2 = {float(vstar):.12f};  lifted-CHSH bound "
          f"4/(3 sqrt2+1) = {float(vchsh):.12f} > 2/I_ME(3): {c1};  Phi_2: 8/(9 sqrt2-1) = {float(vphi2):.12f} "
          f"< 2/I_ME(3): {c2}")
    # interval double check of the two comparisons with rational bounds of sqrt2, sqrt3 (independent of sympy)
    r2lo, r2hi = Fr(14142135623, 10 ** 10), Fr(14142135624, 10 ** 10)
    r3lo, r3hi = Fr(17320508075, 10 ** 10), Fr(17320508076, 10 ** 10)
    assert r2lo ** 2 < 2 < r2hi ** 2 and r3lo ** 2 < 3 < r3hi ** 2
    vstar_hi = 3 * r3hi - Fr(9, 2)
    vstar_lo = 3 * r3lo - Fr(9, 2)
    vchsh_lo = 4 / (3 * r2hi + 1)
    vphi2_hi = Fr(8) / (9 * r2lo - 1)
    ok &= vchsh_lo > vstar_hi and vphi2_hi < vstar_lo
    print(f"    interval re-check: {float(vchsh_lo):.10f} > {float(vstar_hi):.10f} and {float(vphi2_hi):.10f} < "
          f"{float(vstar_lo):.10f}: {vchsh_lo > vstar_hi and vphi2_hi < vstar_lo}")
    # Phi_D, D odd: (D-1)/2 CHSH blocks + 1 deterministic dimension; CHSH-witness upper bound on v_c
    Dmin = None
    for Dd in range(3, 41, 2):
        w = sp.Rational(Dd - 1, Dd)
        vD = sp.Rational(16, 9) / (sp.Rational(16, 9) + w * (2 * s2 - 2))
        if sp.simplify(vstar - vD).is_positive and Dmin is None:
            Dmin = Dd
    ok &= Dmin == 17
    print(f"    Phi_D (D odd) block construction beats 2/I_ME(3) first at D = {Dmin} (and for all larger odd D, the "
          f"bound being decreasing in D)")
    # (4) exact CGLMP value of DKZ_3
    d = 3
    delta = {(0, 0): sp.Rational(1, 4), (0, 1): sp.Rational(-1, 4), (1, 0): sp.Rational(3, 4), (1, 1): sp.Rational(1, 4)}
    beta0 = cglmp_beta()
    I = 0
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    w = beta0[x][y][a][b]
                    if w:
                        pr = 1 / (2 * d ** 3 * sp.sin(sp.pi * (b - a - delta[(x, y)]) / d) ** 2)
                        I += sp.Rational(w.numerator, w.denominator) * pr
    I = sp.nsimplify(sp.simplify(sp.expand_trig(I)))
    okI = sp.simplify(I - target) == 0
    ok &= okI
    print(f"(4) I_3(DKZ_3) = {I}  == I_ME(3): {okI}")
    return ok


def numeric_chsh_phi3(nstart=200, seed=0):
    """sanity check only: max over +-1 observables (Hermitian unitaries, arbitrary traces) on C^3 of
    (1/3) sum s_xy Tr(A_x^T B_y)."""
    import numpy as np
    rng = np.random.default_rng(seed)
    s = np.array([[1, 1], [1, -1]])
    best = -np.inf
    for k in range(nstart):
        # observables = 2P - 1, P projector of random rank (0..3) -- the maximum over B for fixed A is a trace norm
        def obs():
            r = rng.integers(0, 4)
            Z = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
            Q, _ = np.linalg.qr(Z)
            P = Q[:, :r] @ Q[:, :r].conj().T
            return 2 * P - np.eye(3)
        B = [obs(), obs()]
        for it in range(50):
            # optimal A_x given B: A_x^T = sign(sum_y s_xy B_y)  (polar part)
            A = []
            for x in range(2):
                M = s[x, 0] * B[0] + s[x, 1] * B[1]
                w, V = np.linalg.eigh(M)
                A.append(((V * np.where(w >= 0, 1, -1)) @ V.conj().T).T)
            Bn = []
            for y in range(2):
                M = s[0, y] * A[0].T + s[1, y] * A[1].T
                w, V = np.linalg.eigh(M)
                Bn.append((V * np.where(w >= 0, 1, -1)) @ V.conj().T)
            B = Bn
        val = sum(s[x, y] * np.trace(A[x].T @ B[y]).real for x in range(2) for y in range(2)) / 3
        best = max(best, val)
    return best


if __name__ == "__main__":
    ok = run()
    import math
    nb = numeric_chsh_phi3()
    print(f"(5) numerical max CHSH on Phi_3 (seesaw, any traces) = {nb:.12f}; (4 sqrt2 + 2)/3 = "
          f"{(4 * math.sqrt(2) + 2) / 3:.12f}")
    print("RESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
