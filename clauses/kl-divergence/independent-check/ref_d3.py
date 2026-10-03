"""
ref_d3.py -- referee's independent certificate for Theorem 3 (strict local optimality of DKZ_3), kl-divergence/THEOREM.md.

Independent of d3_cert.py / cyc12.py / d3_sympy_check.py:
  * own exact arithmetic in Q(i, sqrt3) (class K below);
  * DIFFERENT chart: right multiplication A_x(z) = A_x^0 exp(i sum_j z_xj g_j), B_y(z) = B_y^0 exp(i sum_j z_yj g_j),
    g_j = Gell-Mann matrices lambda_1..lambda_8 and the identity;
  * DIFFERENT slice: the exact orthogonal complement (in z-coordinates) of the gauge tangent space;
  * DIFFERENT right inverse Psi of the level-sum map (least-norm, exact rationals via sympy);
  * own least-squares choice of the V0 part; own interval assembly and interval LDL^T.
Checks (exact): level law, CGLMP Pi-form bound and facet (30 strategies, affine dim 23), p* in relint F (explicit
positive weights), criticality d Pi_k = 0 in all 36 directions, gauge rank 20, complement dim 16.
Interval: Hbar on the slice <= -c I.
usage: python ref_d3.py
"""
import itertools
from fractions import Fraction as Fr
import numpy as np
import sympy as sp
from mpmath import iv, mp, mpf

iv.dps = 50
mp.dps = 50


# ------------------------------------------------------------------ Q(sqrt3) and Q(i, sqrt3)
class R3:
    __slots__ = ("a", "b")          # a + b sqrt3

    def __init__(self, a=0, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(s, o):
        o = o if isinstance(o, R3) else R3(o)
        return R3(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __neg__(s):
        return R3(-s.a, -s.b)

    def __sub__(s, o):
        return s + (-(o if isinstance(o, R3) else R3(o)))

    def __mul__(s, o):
        if not isinstance(o, R3):
            o = R3(o)
        return R3(s.a * o.a + 3 * s.b * o.b, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__

    def inv(s):
        n = s.a * s.a - 3 * s.b * s.b
        assert n != 0
        return R3(s.a / n, -s.b / n)

    def iszero(s):
        return s.a == 0 and s.b == 0

    def __eq__(s, o):
        o = o if isinstance(o, R3) else R3(o)
        return s.a == o.a and s.b == o.b

    def ivv(s):
        return iv.mpf(s.a.numerator) / s.a.denominator + iv.mpf(s.b.numerator) / s.b.denominator * iv.sqrt(3)

    def f(s):
        return float(s.a) + float(s.b) * 3 ** 0.5


class K:
    __slots__ = ("re", "im")         # re + i im, re, im in Q(sqrt3)

    def __init__(self, re=None, im=None):
        self.re = re if isinstance(re, R3) else R3(re or 0)
        self.im = im if isinstance(im, R3) else R3(im or 0)

    def __add__(s, o):
        return K(s.re + o.re, s.im + o.im)

    def __sub__(s, o):
        return K(s.re - o.re, s.im - o.im)

    def __mul__(s, o):
        if isinstance(o, K):
            return K(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
        return K(s.re * o, s.im * o)

    def conj(s):
        return K(s.re, -s.im)

    def iszero(s):
        return s.re.iszero() and s.im.iszero()


ZERO = K()
ONE = K(1)
IU = K(0, 1)
SQ3 = R3(0, 1)


def zeta12(n):
    n %= 12
    c = {0: R3(1), 1: R3(0, Fr(1, 2)), 2: R3(Fr(1, 2)), 3: R3(0), 4: R3(Fr(-1, 2)), 5: R3(0, Fr(-1, 2)),
         6: R3(-1), 7: R3(0, Fr(-1, 2)), 8: R3(Fr(-1, 2)), 9: R3(0), 10: R3(Fr(1, 2)), 11: R3(0, Fr(1, 2))}[n]
    s = {0: R3(0), 1: R3(Fr(1, 2)), 2: R3(0, Fr(1, 2)), 3: R3(1), 4: R3(0, Fr(1, 2)), 5: R3(Fr(1, 2)),
         6: R3(0), 7: R3(Fr(-1, 2)), 8: R3(0, Fr(-1, 2)), 9: R3(-1), 10: R3(0, Fr(-1, 2)), 11: R3(Fr(-1, 2))}[n]
    return K(c, s)


# sanity: zeta12^n * zeta12^m = zeta12^(n+m)
for n_ in range(12):
    for m_ in range(12):
        p_ = zeta12(n_) * zeta12(m_)
        q_ = zeta12(n_ + m_)
        assert (p_.re == q_.re) and (p_.im == q_.im)


def mm(X, Y):
    n, k, m = len(X), len(Y), len(Y[0])
    return [[sum((X[i][l] * Y[l][j] for l in range(k)), ZERO) for j in range(m)] for i in range(n)]


def madd(X, Y):
    return [[X[i][j] + Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]


def msc(X, s):
    return [[X[i][j] * s for j in range(len(X[0]))] for i in range(len(X))]


def mconj(X):
    return [[X[i][j].conj() for j in range(len(X[0]))] for i in range(len(X))]


def mdag(X):
    return [[X[j][i].conj() for j in range(len(X))] for i in range(len(X[0]))]


# ------------------------------------------------------------------ DKZ_3 (unnormalised, entries in Q(zeta12))
# |a>_x = 3^-1/2 sum_k w^{k(a + alpha_x)} |k>, alpha = (1/2, 0);  |b>_y = 3^-1/2 sum_k w^{-k(b + beta_y)} |k>,
# beta = (1/4, -1/4);  w = zeta12^4.   Ahat[k][a] = zeta12^{4k(a+alpha)} etc.
Ahat = [[[zeta12(4 * k * a + 2 * k) for a in range(3)] for k in range(3)],
        [[zeta12(4 * k * a) for a in range(3)] for k in range(3)]]
Bhat = [[[zeta12(-(4 * k * b + k)) for b in range(3)] for k in range(3)],
        [[zeta12(-(4 * k * b - k)) for b in range(3)] for k in range(3)]]
# unitarity: Ahat^dag Ahat = 3 I
for U in Ahat + Bhat:
    G = mm(mdag(U), U)
    for i in range(3):
        for j in range(3):
            assert G[i][j].re == (R3(3) if i == j else R3(0)) and G[i][j].im.iszero()

# Gell-Mann basis + identity (Hermitian, trace-orthogonal); entries in Q(i, sqrt3) with 1/sqrt3 = sqrt3/3
def E(i, j, v):
    M = [[ZERO] * 3 for _ in range(3)]
    M[i][j] = v
    return M


inv_s3 = R3(0, Fr(1, 3))
GM = [
    madd(E(0, 1, ONE), E(1, 0, ONE)),
    madd(E(0, 1, K(0, -1)), E(1, 0, K(0, 1))),
    madd(E(0, 0, ONE), E(1, 1, K(-1))),
    madd(E(0, 2, ONE), E(2, 0, ONE)),
    madd(E(0, 2, K(0, -1)), E(2, 0, K(0, 1))),
    madd(E(1, 2, ONE), E(2, 1, ONE)),
    madd(E(1, 2, K(0, -1)), E(2, 1, K(0, 1))),
    madd(madd(E(0, 0, K(inv_s3)), E(1, 1, K(inv_s3))), E(2, 2, K(inv_s3 * (-2)))),
    madd(madd(E(0, 0, ONE), E(1, 1, ONE)), E(2, 2, ONE)),
]
GMc = [mconj(g) for g in GM]
GMnorm = [R3(2)] * 8 + [R3(3)]           # tr(g^2)


def herm_coords(X):
    """coordinates c_j (real, in Q(sqrt3)) with X = sum c_j g_j  (X Hermitian)"""
    out = []
    for j, g in enumerate(GM):
        tr = sum((g[i][k] * X[k][i] for i in range(3) for k in range(3)), ZERO)
        assert tr.im.iszero()
        out.append(tr.re * GMnorm[j].inv())
    return out


LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
CELLS = [(x, y, a, b) for (x, y) in LINKS for a in range(3) for b in range(3)]
NDIR = 36   # direction index: 9*m + j, m = 0,1 (Alice x = m), 2,3 (Bob y = m-2)


def gp(x, y, a, b):
    if (x, y) in ((0, 0), (1, 1)):
        return (a - b) % 3
    if (x, y) == (1, 0):
        return (b - a) % 3
    return (b - a - 1) % 3


LEV = [gp(*c) for c in CELLS]

# N0_xy = Ahat_x^dag conj(Bhat_y);  amplitude = 3^{-3/2} n,  q = |n|^2 / 27
N0 = {(x, y): mm(mdag(Ahat[x]), mconj(Bhat[y])) for (x, y) in LINKS}


def dn(i, x, y):
    """d n / d z_i at 0 (3x3) or None.  Alice: -i g n0 ; Bob: n0 (-i conj g)."""
    m, j = divmod(i, 9)
    if m < 2:
        if m != x:
            return None
        return msc(mm(GM[j], N0[(x, y)]), K(0, -1))
    if m - 2 != y:
        return None
    return msc(mm(N0[(x, y)], GMc[j]), K(0, -1))


def d2n(i, j, x, y):
    mi, gi = divmod(i, 9)
    mj, gj = divmod(j, 9)
    acti = (mi < 2 and mi == x) or (mi >= 2 and mi - 2 == y)
    actj = (mj < 2 and mj == x) or (mj >= 2 and mj - 2 == y)
    if not (acti and actj):
        return None
    if mi < 2 and mj < 2:          # Alice-Alice: -(1/2)(g_i g_j + g_j g_i) n0
        S = madd(mm(GM[gi], GM[gj]), mm(GM[gj], GM[gi]))
        return msc(mm(S, N0[(x, y)]), K(Fr(-1, 2)))
    if mi >= 2 and mj >= 2:        # Bob-Bob: n0 (-(1/2))(cg_i cg_j + cg_j cg_i)
        S = madd(mm(GMc[gi], GMc[gj]), mm(GMc[gj], GMc[gi]))
        return msc(mm(N0[(x, y)], S), K(Fr(-1, 2)))
    if mi < 2:                     # Alice i, Bob j: (-i g_i) n0 (-i cg_j) = - g_i n0 cg_j
        return msc(mm(mm(GM[gi], N0[(x, y)]), GMc[gj]), K(-1))
    return msc(mm(mm(GM[gj], N0[(x, y)]), GMc[gi]), K(-1))


def re_cprod(u, v):
    """Re(conj(u) v)"""
    return (u.conj() * v).re


q0 = [re_cprod(N0[c[:2]][c[2]][c[3]], N0[c[:2]][c[2]][c[3]]) * Fr(1, 27) for c in CELLS]
QLEV = [R3(Fr(4, 9), Fr(2, 9)), R3(Fr(4, 9), Fr(-2, 9)), R3(Fr(1, 9))]
for c in range(36):
    assert q0[c] == QLEV[LEV[c]] * Fr(1, 3)
print("[X1] exact: q0 = Q_{g'}/3 with Q = (2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9) on every link")

DN = {(i, L): dn(i, *L) for i in range(NDIR) for L in LINKS}
dq = [[R3(0)] * 36 for _ in range(NDIR)]
for i in range(NDIR):
    for c, cell in enumerate(CELLS):
        D = DN[(i, cell[:2])]
        if D is not None:
            dq[i][c] = re_cprod(N0[cell[:2]][cell[2]][cell[3]], D[cell[2]][cell[3]]) * Fr(2, 27)
# criticality + per-link normalisation of derivatives
for i in range(NDIR):
    for k in range(3):
        s = sum((dq[i][c] for c in range(36) if LEV[c] == k), R3(0))
        assert s.iszero(), (i, k)
    for L in LINKS:
        s = sum((dq[i][c] for c in range(36) if CELLS[c][:2] == L), R3(0))
        assert s.iszero()
print("[X2] exact criticality in the right-multiplication Gell-Mann chart: d Pi_k = 0, k = 0,1,2, all 36 directions")
nz = sum(1 for i in range(NDIR) for c in range(36) if not dq[i][c].iszero())
print(f"     (non-trivial: {nz} nonzero first derivatives dq_i(c))")

# ------------------------------------------------------------------ CGLMP facet, p* in relint F
sums = {lam: sum(gp(x, y, lam[x], lam[2 + y]) for (x, y) in LINKS) for lam in itertools.product(range(3), repeat=4)}
assert min(sums.values()) == 2
facet = [lam for lam, s in sums.items() if s == 2]
assert len(facet) == 30


def detv(lam):
    return [1 if (lam[c[0]], lam[2 + c[1]]) == (c[2], c[3]) else 0 for c in CELLS]


Fm = sp.Matrix([[detv(l)[k] - detv(facet[0])[k] for k in range(36)] for l in facet[1:]])
assert Fm.rank() == 23
cons = []
for L in LINKS:
    cons.append([1 if c[:2] == L else 0 for c in CELLS])
for x in range(2):
    for a in range(3):
        cons.append([(1 if c[:3] == (x, 0, a) else 0) - (1 if c[:3] == (x, 1, a) else 0) for c in CELLS])
for y in range(2):
    for b in range(3):
        cons.append([(1 if (c[0], c[1], c[3]) == (0, y, b) else 0) - (1 if (c[0], c[1], c[3]) == (1, y, b) else 0)
                     for c in CELLS])
glev = [LEV[k] for k in range(36)]
Vb = sp.Matrix(cons + [glev]).nullspace()
assert len(Vb) == 23
# direction space of aff F inside V (dimensions equal -> equal)
assert sp.Matrix.hstack(*Vb).rank() == 23 and (sp.Matrix(cons + [glev]) * Fm.T).is_zero_matrix
print("[X3] exact: CGLMP Pi-form min 2, facet = 30 strategies, aff dim 23 = dim V (V = NS + level-sum zero)")

# beta, r*, P* (intervals); p* = q0 / r* as an explicit positive mixture of the 30 facet strategies (solve exactly
# in terms of the level law: each facet strategy is determined by its level pattern; find weights per pattern)
S3i = iv.sqrt(iv.mpf(3))
beta = ((16 + 24 * S3i) - iv.sqrt(3280 - 960 * S3i)) / 54
Qi = [q.ivv() for q in QLEV]
r = [1 + beta * (iv.mpf(1) / 2 - k) for k in range(3)]
Pst = [Qi[k] / r[k] for k in range(3)]
# independent check of beta: it must solve sum_k Q_k / (1 + b (1/2 - k)) = 1 -- verify with mpmath root finding
mp.dps = 50
Qm = [mpf(2) * (2 + mp.sqrt(3)) / 9, mpf(2) * (2 - mp.sqrt(3)) / 9, mpf(1) / 9]
froot = mp.findroot(lambda b: sum(Qm[k] / (1 + b * (mpf(1) / 2 - k)) for k in range(3)) - 1, 0.3)
assert abs(froot - beta.mid) < mpf(10) ** -40
tot = Pst[0] + Pst[1] + Pst[2]
assert (tot - 1).a < iv.mpf(10) ** -40 and (tot - 1).b > -iv.mpf(10) ** -40
mean = Pst[1] + 2 * Pst[2]
assert abs(mpf((mean - iv.mpf(1) / 2).mid)) < mpf(10) ** -40
# weights: pattern 'single link at level 2' (4 patterns x 3 shifts), 'two links at level 1' (6 patterns x 3 shifts)
# link law of the mixture: P(level 2) = (1/4) W2 * ... ; we take all 12 two-link strategies with equal weight
# w1 each and all 12 single-link ones with weight w2 each: level-2 prob per link = 3 w2, level-1 prob per link =
# (3 two-link patterns contain a given link) * 3 shifts * w1 = 9 w1.
w2 = Pst[2] / 3
w1 = Pst[1] / 9
assert w2.a > 0 and w1.a > 0
# exact check that this mixture reproduces q0/r* cellwise (in intervals): build it
mix = [iv.mpf(0)] * 36
for lam in facet:
    pat = [gp(x, y, lam[x], lam[2 + y]) for (x, y) in LINKS]
    wt = w2 if 2 in pat else w1
    for k, v in enumerate(detv(lam)):
        if v:
            mix[k] += wt
pstar = [Qi[LEV[c]] / 3 / r[LEV[c]] for c in range(36)]
dev = max(abs(mpf((mix[c] - pstar[c]).mid)) + mpf((mix[c] - pstar[c]).delta) for c in range(36))
assert dev < mpf(10) ** -40
print(f"[X4] beta = {mp.nstr(mpf(beta.mid), 16)} (independent root find agrees); p* = q0/r* = positive mixture of ALL 30 facet "
      f"strategies (w(single level-2) = P*_2/3, w(two level-1) = P*_1/9), max dev {float(dev):.1e} => p* in relint F")
S0 = sum(Qi[k] * iv.log(r[k]) for k in range(3))
print(f"     S(DKZ_3) = sum Q_k log r_k = {mp.nstr(mpf((S0 / iv.log(2)).mid), 16)} bits")

# ------------------------------------------------------------------ gauge tangent space in the right chart
gauge = []
for m in range(4):
    for a in range(3):
        Eaa = E(a, a, ONE)                  # A -> A diag(e^{i th}) = A exp(i th E_aa)
        v = [R3(0)] * NDIR
        v[9 * m:9 * m + 9] = herm_coords(Eaa)
        gauge.append(v)
Uh = [Ahat[0], Ahat[1], Bhat[0], Bhat[1]]
for j in range(9):
    v = [R3(0)] * NDIR
    for m in range(4):
        if m < 2:   # W A = A exp(i A^dag h A)
            X = msc(mm(mm(mdag(Uh[m]), GM[j]), Uh[m]), K(Fr(1, 3)))
        else:       # conj(W) B = B exp(-i B^dag conj(h) B)
            X = msc(mm(mm(mdag(Uh[m]), GMc[j]), Uh[m]), K(Fr(-1, 3)))
        v[9 * m:9 * m + 9] = herm_coords(X)
    gauge.append(v)


def rref_null(rows, ncol):
    """exact row reduction over Q(sqrt3); returns rank and a basis of the nullspace {v : rows v = 0}"""
    R = [list(r_) for r_ in rows]
    piv_cols = []
    rk = 0
    for col in range(ncol):
        piv = next((i for i in range(rk, len(R)) if not R[i][col].iszero()), None)
        if piv is None:
            continue
        R[rk], R[piv] = R[piv], R[rk]
        inv = R[rk][col].inv()
        R[rk] = [x * inv for x in R[rk]]
        for i in range(len(R)):
            if i != rk and not R[i][col].iszero():
                f = R[i][col]
                R[i] = [R[i][c] - f * R[rk][c] for c in range(ncol)]
        piv_cols.append(col)
        rk += 1
    free = [c for c in range(ncol) if c not in piv_cols]
    basis = []
    for fcol in free:
        v = [R3(0)] * ncol
        v[fcol] = R3(1)
        for i, pc in enumerate(piv_cols):
            v[pc] = -R[i][fcol]
        basis.append(v)
    return rk, basis


rk, Pbasis = rref_null(gauge, NDIR)          # orthogonal complement of the gauge span
assert rk == 20 and len(Pbasis) == 16
# verify: gauge vectors annihilated by... (orthogonality check) and q constant to first order along gauge
for g in gauge:
    for v in Pbasis:
        assert sum((g[i] * v[i] for i in range(NDIR)), R3(0)).iszero()
    for c in range(36):
        assert sum((g[i] * dq[i][c] for i in range(NDIR)), R3(0)).iszero()
print("[X5] exact: gauge tangent space rank 20 (21 generators), dq vanishes on it; slice = its orthogonal "
      "complement (dim 16), transversal by construction")

# ------------------------------------------------------------------ second derivatives (exact) projected on slice
NS = 16
P = Pbasis      # list of 16 vectors (each 36 R3)
# dq along slice vectors
dqs = [[sum((P[s][i] * dq[i][c] for i in range(NDIR) if not P[s][i].iszero()), R3(0)) for c in range(36)]
       for s in range(NS)]
# d2q_c restricted: H2[c][s][t] = sum_ij P[s][i] P[t][j] d2q_ij(c)
H2 = [[[R3(0)] * NS for _ in range(NS)] for _ in range(36)]
for L in LINKS:
    x, y = L
    act = [i for i in range(NDIR) if (i // 9 == x) or (i // 9 - 2 == y and i // 9 >= 2)]
    act = [i for i in act if (i // 9 < 2 and i // 9 == x) or (i // 9 >= 2 and i // 9 - 2 == y)]
    D1 = {i: DN[(i, L)] for i in act}
    D2 = {}
    for i in act:
        for j in act:
            if j < i:
                D2[(i, j)] = D2[(j, i)]
                continue
            D2[(i, j)] = d2n(i, j, x, y)
    for c, cell in enumerate(CELLS):
        if cell[:2] != L:
            continue
        a, b = cell[2], cell[3]
        n0 = N0[L][a][b]
        M = {}
        for i in act:
            for j in act:
                if j < i:
                    M[(i, j)] = M[(j, i)]
                    continue
                v = re_cprod(n0, D2[(i, j)][a][b]) + re_cprod(D1[i][a][b], D1[j][a][b])
                M[(i, j)] = v * Fr(2, 27)
        # project
        PM = [[sum((P[s][i] * M[(i, j)] for i in act if not P[s][i].iszero()), R3(0)) for j in act] for s in range(NS)]
        for s in range(NS):
            for t in range(s, NS):
                val = sum((PM[s][jj] * P[t][j] for jj, j in enumerate(act) if not P[t][j].iszero()), R3(0))
                H2[c][s][t] = val
                H2[c][t][s] = val
print("[X6] exact second derivatives of q on the slice computed")

# ------------------------------------------------------------------ facet direction space, V0, least-norm Psi
cons_lev = []
for L in LINKS:
    cons_lev.append([LEV[k] if CELLS[k][:2] == L else 0 for k in range(36)])
V0b = sp.Matrix(cons + cons_lev).nullspace()
assert len(V0b) == 20
V0M = sp.Matrix.hstack(*V0b)                    # 36 x 20
Vfull = sp.Matrix.hstack(*Vb)                   # 36 x 23
LSm = sp.Matrix(cons_lev)                       # 4 x 36 level sums per link
# least-norm right inverse: Psi(z) = V w with min |V w|^2 s.t. LS V w = z.  Solve via normal equations exactly:
#   minimise w^T G w, G = V^T V, s.t. C w = z, C = LS V  ->  w = G^-1 C^T (C G^-1 C^T)^+ z  (z sum-zero, rank 3)
Gm = Vfull.T * Vfull
Cm = LSm * Vfull
Gi = Gm.inv()
Mm = Cm * Gi * Cm.T                             # 4 x 4, rank 3 (kernel = (1,1,1,1))
assert Mm.rank() == 3
Mp = Mm.pinv()
PsiM = Vfull * Gi * Cm.T * Mp                   # 36 x 4 exact rational
for l in range(3):
    zz = sp.Matrix([1 if k == l else 0 for k in range(4)]) - sp.Matrix([0, 0, 0, 1])
    u = PsiM * zz
    assert (sp.Matrix(cons) * u).is_zero_matrix
    assert LSm * u == zz
PsiF = [[Fr(int(sp.fraction(PsiM[i, j])[0]), int(sp.fraction(PsiM[i, j])[1])) for j in range(4)] for i in range(36)]
V0F = [[Fr(int(sp.fraction(V0M[i, j])[0]), int(sp.fraction(V0M[i, j])[1])) for j in range(20)] for i in range(36)]
print("[X7] exact: dim V0 = 20; least-norm Psi maps sum-zero z to u in V with per-link level sums z")

# ------------------------------------------------------------------ u1 on slice vectors, Hbar in intervals
ell = [iv.log(x) for x in r]
kap1 = -(ell[1] - ell[0]) / beta
kap2 = -(ell[2] - ell[0]) / beta
q0i = [q0[c].ivv() for c in range(36)]
rst = [r[LEV[c]] for c in range(36)]


def pis(s, k):
    return [sum((dqs[s][c] for c in range(36) if CELLS[c][:2] == L and LEV[c] == k), R3(0)) for L in LINKS]


Ufix = []
for s in range(NS):
    p1 = [v.ivv() for v in pis(s, 1)]
    p2 = [v.ivv() for v in pis(s, 2)]
    Ufix.append([sum((iv.mpf(PsiF[k][l].numerator) / PsiF[k][l].denominator * (kap1 * p1[l] + kap2 * p2[l])
                      for l in range(4)), iv.mpf(0)) for k in range(36)])
# optimal V0 coefficients (float least squares), rationalised -> exact rational V0 part (any choice is valid)
qf = np.array([float(mpf(x.mid)) for x in q0i])
rf = np.array([float(mpf(x.mid)) for x in rst])
V0f = np.array([[float(v) for v in row] for row in V0F])
U = []
for s in range(NS):
    uf = np.array([float(mpf(x.mid)) for x in Ufix[s]])
    dqf = np.array([v.f() for v in dqs[s]])
    Wt = 1 / np.sqrt(qf)
    cvec = np.linalg.lstsq((rf[:, None] * V0f) * Wt[:, None], (dqf - rf * uf) * Wt, rcond=None)[0]
    crat = [Fr(float(v)).limit_denominator(10 ** 12) for v in cvec]
    v0 = [sum((crat[j] * V0F[k][j] for j in range(20)), Fr(0)) for k in range(36)]
    U.append([Ufix[s][k] + iv.mpf(v0[k].numerator) / v0[k].denominator for k in range(36)])
# check: first-order term of every link vanishes: sum_cells(link) [dq log r* - r* u] = 0
for s in range(NS):
    for L in LINKS:
        tot_ = sum((dqs[s][c].ivv() * ell[LEV[c]] - rst[c] * U[s][c] for c in range(36) if CELLS[c][:2] == L),
                   iv.mpf(0))
        assert abs(mpf(tot_.mid)) + mpf(tot_.delta) < mpf(10) ** -35, (s, L)
print("[X8] first-order terms of all four link functions vanish on the slice (interval check, < 1e-35)")

Hb = [[None] * NS for _ in range(NS)]
Rres = [[dqs[s][c].ivv() - rst[c] * U[s][c] for c in range(36)] for s in range(NS)]
for s in range(NS):
    for t in range(s, NS):
        acc = iv.mpf(0)
        for c in range(36):
            acc += H2[c][s][t].ivv() * ell[LEV[c]] + Rres[s][c] * Rres[t][c] / q0i[c]
        Hb[s][t] = Hb[t][s] = acc / 4
Hm = np.array([[float(mpf(Hb[s][t].mid)) for t in range(NS)] for s in range(NS)])
ev = np.linalg.eigvalsh(Hm)
# normalise by the slice metric for an intrinsic spectrum: generalized eigenvalues w.r.t. Gram matrix P P^T
Gram = np.array([[sum(P[s][i].f() * P[t][i].f() for i in range(NDIR)) for t in range(NS)] for s in range(NS)])
import scipy.linalg as sla
evg = sla.eigh(Hm, Gram, eigvals_only=True)
print(f"[X9] Hbar on slice (basis P): eigenvalues in [{ev.min():.6f}, {ev.max():.6f}]; "
      f"metric-normalised (generalized w.r.t. Gram): [{evg.min():.6f}, {evg.max():.6f}]")


def interval_ldl_pd(Mx):
    n = len(Mx)
    Lm = [[iv.mpf(0)] * n for _ in range(n)]
    Dg = [None] * n
    for j in range(n):
        dj = Mx[j][j] - sum((Lm[j][k] * Lm[j][k] * Dg[k] for k in range(j)), iv.mpf(0))
        if not dj.a > 0:
            return False, j
        Dg[j] = dj
        for i in range(j + 1, n):
            Lm[i][j] = (Mx[i][j] - sum((Lm[i][k] * Lm[j][k] * Dg[k] for k in range(j)), iv.mpf(0))) / dj
    return True, None


# certify  -Hbar - c * Gram  > 0  (i.e. Hbar <= -c |z|^2 on the slice, in the z-metric)
cc = iv.mpf(1) / 1000
Mx = [[-Hb[s][t] - cc * iv.mpf(Gram[s][t]) * 0 - cc * sum((P[s][i].ivv() * P[t][i].ivv() for i in range(NDIR)),
                                                           iv.mpf(0)) for t in range(NS)] for s in range(NS)]
ok, where = interval_ldl_pd(Mx)
print(f"[X10] interval LDL^T of -Hbar - (1/1000) Gram succeeds: {ok}  => Hbar <= -(1/1000)|z|^2 on the slice")
print("REFEREE d = 3 CERTIFICATE:", "PASSED" if ok else f"FAILED at pivot {where}")
np.savez("ref_d3_data.npz", Hm=Hm, Gram=Gram, P=np.array([[v.f() for v in row] for row in P]),
         U=np.array([[float(mpf(x.mid)) for x in row] for row in U]), beta=float(mpf(beta.mid)))
