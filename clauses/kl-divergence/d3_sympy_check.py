"""
d3_sympy_check.py -- independent EXACT re-check (sympy, explicit radicals; no code shared with cyc12.py/d3_cert.py)
of the algebraic facts used in Theorem 3:
  (a) DKZ_3 correlations: q0(a,b|x,y) = Q_{g'}/3 with Q = (2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9);
  (b) criticality: for every one of the 36 chart directions, d/dt Pi_k = 0 at t = 0 (k = 0, 1, 2);
  (c) beta = [(16+24 sqrt3) - sqrt(3280 - 960 sqrt3)]/54 solves 27 b^2 - (16+24 sqrt3) b + 16 sqrt3 - 12 = 0 and
      gives sum_k Q_k/r_k = 1 and sum_k k Q_k/r_k = 1/2 (r_k = 1 + beta(1/2 - k)).
Derivatives are computed symbolically from q(t) = |<a|exp(-i t G)...|^2 via the exact first-order formula
  d/dt q = 2 Re( conj(M0) * dM ),  dM = 3^(-3/2) Ahat^+ (-i G) conj(Bhat),
with G = H (Alice) or conj(K) (Bob) for each Hermitian basis element.
"""
import itertools
import sympy as sp

w = sp.exp(2 * sp.pi * sp.I / 3)
k = range(3)


def col_A(x, a):
    al = [sp.Rational(1, 2), 0][x]
    return sp.Matrix([sp.exp(2 * sp.pi * sp.I * kk * (a + al) / 3) for kk in k])


def col_B(y, b):
    be = [sp.Rational(1, 4), -sp.Rational(1, 4)][y]
    return sp.Matrix([sp.exp(-2 * sp.pi * sp.I * kk * (b + be) / 3) for kk in k])


Ah = [sp.Matrix.hstack(*[col_A(x, a) for a in range(3)]) for x in range(2)]
Bh = [sp.Matrix.hstack(*[col_B(y, b) for b in range(3)]) for y in range(2)]
c = sp.Rational(1, 3) ** sp.Rational(3, 2)


def herm_basis():
    Hs = []
    for i in range(3):
        H = sp.zeros(3, 3); H[i, i] = 1; Hs.append(H)
    for i in range(3):
        for j in range(i + 1, 3):
            H = sp.zeros(3, 3); H[i, j] = H[j, i] = 1; Hs.append(H)
            H = sp.zeros(3, 3); H[i, j] = -sp.I; H[j, i] = sp.I; Hs.append(H)
    return Hs


Hs = herm_basis()


def gp(x, y, a, b):
    if (x, y) in ((0, 0), (1, 1)):
        return (a - b) % 3
    if (x, y) == (1, 0):
        return (b - a) % 3
    return (b - a - 1) % 3


def simp(e):
    return sp.nsimplify(sp.simplify(sp.expand_complex(sp.expand(e))))


LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
M0 = {L: c * Ah[L[0]].H * Bh[L[1]].conjugate() for L in LINKS}
s3 = sp.sqrt(3)
Q = [2 * (2 + s3) / 9, 2 * (2 - s3) / 9, sp.Rational(1, 9)]
for (x, y) in LINKS:
    for a, b in itertools.product(range(3), repeat=2):
        q = simp(sp.Abs(M0[(x, y)][a, b]) ** 2)
        assert sp.simplify(q - Q[gp(x, y, a, b)] / 3) == 0, (x, y, a, b, q)
print("(a) q0 = Q_{g'}/3 exactly (sympy)")

for m in range(4):
    for j, H in enumerate(Hs):
        G = H if m < 2 else H.conjugate()
        tot = [0, 0, 0]
        for (x, y) in LINKS:
            if (m < 2 and m != x) or (m >= 2 and m - 2 != y):
                continue
            dM = c * Ah[x].H * (-sp.I * G) * Bh[y].conjugate()
            for a, b in itertools.product(range(3), repeat=2):
                dq = 2 * sp.re(sp.conjugate(M0[(x, y)][a, b]) * dM[a, b])
                tot[gp(x, y, a, b)] += dq
        for kk in range(3):
            v = simp(tot[kk])
            assert v == 0, (m, j, kk, v)
print("(b) d Pi_k = 0 exactly for all 36 directions and k = 0, 1, 2 (sympy)")

beta = ((16 + 24 * s3) - sp.sqrt(3280 - 960 * s3)) / 54
assert sp.simplify(sp.expand(27 * beta ** 2 - (16 + 24 * s3) * beta + 16 * s3 - 12)) == 0
r = [1 + beta * (sp.Rational(1, 2) - kk) for kk in range(3)]
e1 = sp.simplify(sp.radsimp(sum(Q[kk] / r[kk] for kk in range(3)) - 1))
e2 = sp.simplify(sp.radsimp(sum(kk * Q[kk] / r[kk] for kk in range(3)) - sp.Rational(1, 2)))
print("(c) residuals (should be 0):", e1, e2, "; numerically:", sp.N(e1, 50), sp.N(e2, 50))
print("    beta =", sp.N(beta, 30), " S(DKZ_3) =", sp.N(sum(Q[kk] * sp.log(r[kk]) for kk in range(3)) / sp.log(2), 25), "bits")
