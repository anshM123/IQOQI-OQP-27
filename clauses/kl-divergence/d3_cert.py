"""
d3_cert.py -- RIGOROUS certificate for THEOREM 3 (DKZ_3 is a strict local maximiser of the KL strength on Phi_3,
for S^UNI, S^UC and S^COR, modulo the gauge group).  See THEOREM.md, section 3.

Chart: A_x = exp(i H_x) A_x^0, B_y = exp(i K_y) B_y^0 (columns = basis vectors), H_x = sum_j z_(x,j) Hs_j etc.,
36 real parameters; DKZ_3 at z = 0.  Amplitudes M_xy = 3^(-3/2) Ahat_x^+ e^(-iH_x) e^(-i conj K_y) conj(Bhat_y),
Ahat, Bhat = unnormalised DKZ_3 bases with entries in Q(zeta_12).

EXACT (field Q(zeta_12), real subfield Q(sqrt3)):
  E1  q0, first derivatives dq_i (all 36 directions), second derivatives on the slice.
  E2  CGLMP_3 in Pi-form: sum_xy g'_xy >= 2 on all 81 deterministic strategies, equality on 30.
  E3  DKZ_3 level law Q = (2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9) on every link.
  E4  criticality: d_i Pi_k = 0 for k = 0,1,2 and all 36 directions (Pi_k = total probability of CGLMP level k).
  E5  gauge tangent space (21 generators, rank 20) and a coordinate slice I (16 coordinates) with
      span(gauge) + span(e_I) = R^36 (exact rank).
  E6  Psi (exact right inverse of the per-link level-sum map on V) and an exact rational basis of V_0.
INTERVAL (mpmath iv, 50 digits):
  beta = [(16 + 24 sqrt3) - sqrt(3280 - 960 sqrt3)]/54 (root of 27 b^2 - (16+24 sqrt3) b + 16 sqrt3 - 12 = 0),
  r_k = 1 + beta(1/2 - k), l_k = log r_k, S0 = sum Q_k l_k;  P*_k = Q_k / r_k > 0, sum = 1;
  Hbar (16 x 16): Hbar_ij = 1/4 [ sum d2q_ij log r* + sum (dq_i - r* u_i)(dq_j - r* u_j)/q0 ],
  u_i = kappa_1 Psi(pi1_i) + kappa_2 Psi(pi2_i) + V0 c_i  (link-equalising, kappa_k = -(l_k - l_0)/beta);
  interval Cholesky of -Hbar - c I with c = 1/200  =>  Hbar <= -c I on the slice.
usage: python d3_cert.py
"""
import itertools
import sys
from fractions import Fraction as Fr
import numpy as np
import sympy as sp
from mpmath import iv, mpf

sys.path.insert(0, ".")
from cyc12 import Z12, Q3, I_

iv.dps = 50
LN2 = iv.log(iv.mpf(2))
zp = Z12.zp

# ------------------------------------------------------------------ exact bases and amplitudes
Ah = [[[zp((4 * a + 2) * k) for a in range(3)] for k in range(3)],      # x = 0 (alpha = 1/2): A[k][a]
      [[zp(4 * a * k) for a in range(3)] for k in range(3)]]            # x = 1 (alpha = 0)
Bh = [[[zp(-(4 * b + 1) * k) for b in range(3)] for k in range(3)],     # y = 0 (beta = 1/4)
      [[zp(-(4 * b - 1) * k) for b in range(3)] for k in range(3)]]     # y = 1 (beta = -1/4)
ZERO = Z12()
ONE = Z12((1, 0, 0, 0))


def mat(f):
    return [[f(i, j) for j in range(3)] for i in range(3)]


def mmul(X, Y):
    return [[sum((X[i][k] * Y[k][j] for k in range(3)), ZERO) for j in range(3)] for i in range(3)]


def madd(X, Y, s=1):
    return [[X[i][j] + Y[i][j] * s for j in range(3)] for i in range(3)]


def mscale(X, s):
    return [[X[i][j] * s for j in range(3)] for i in range(3)]


def mconj(X):
    return [[X[i][j].conj() for j in range(3)] for i in range(3)]


Hs = []
for i in range(3):
    Hs.append(mat(lambda r, c, i=i: ONE if (r == c == i) else ZERO))
for i in range(3):
    for j in range(i + 1, 3):
        Hs.append(mat(lambda r, c, i=i, j=j: ONE if (r, c) in ((i, j), (j, i)) else ZERO))
        Hs.append(mat(lambda r, c, i=i, j=j: (-I_) if (r, c) == (i, j) else (I_ if (r, c) == (j, i) else ZERO)))
n = 36
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
CELLS = [(x, y, a, b) for (x, y) in LINKS for a in range(3) for b in range(3)]


def direction(i):
    m, j = divmod(i, 9)
    if m < 2:
        return ("A", m, Hs[j])                 # Alice, setting m, generator H
    return ("B", m - 2, mconj(Hs[j]))          # Bob, setting m-2, generator conj(K) appears in the amplitude


def sandwich(x, y, X):
    """(Ahat_x^+ X conj(Bhat_y))_{ab} for all a, b"""
    out = [[ZERO] * 3 for _ in range(3)]
    for a in range(3):
        for b in range(3):
            s = ZERO
            for k in range(3):
                ca = Ah[x][k][a].conj()
                if ca.is_zero():
                    continue
                for l in range(3):
                    if X[k][l].is_zero():
                        continue
                    s = s + ca * X[k][l] * Bh[y][l][b].conj()
            out[a][b] = s
    return out


IDM = mat(lambda r, c: ONE if r == c else ZERO)
m0 = {(x, y): sandwich(x, y, IDM) for (x, y) in LINKS}


def dm(i, x, y):
    side, s, G = direction(i)
    if (side == "A" and s != x) or (side == "B" and s != y):
        return None
    return sandwich(x, y, mscale(G, -I_))


def d2m(i, j, x, y):
    si, ti, Gi = direction(i)
    sj, tj, Gj = direction(j)
    act_i = (si == "A" and ti == x) or (si == "B" and ti == y)
    act_j = (sj == "A" and tj == x) or (sj == "B" and tj == y)
    if not (act_i and act_j):
        return None
    if si == sj:
        X = mscale(madd(mmul(Gi, Gj), mmul(Gj, Gi)), Fr(-1, 2))
    elif si == "A":
        X = mscale(mmul(Gi, Gj), -1)            # -H_i conj(K_j): Alice factor stands left
    else:
        X = mscale(mmul(Gj, Gi), -1)
    return sandwich(x, y, X)


def re_prod(u, v):
    """Re(conj(u) v) as Q3"""
    return (u.conj() * v).re().real_q3()


q0 = {}
for (x, y, a, b) in CELLS:
    q0[(x, y, a, b)] = re_prod(m0[(x, y)][a][b], m0[(x, y)][a][b]) * Fr(1, 27)
DM = {}
for i in range(n):
    for (x, y) in LINKS:
        DM[(i, x, y)] = dm(i, x, y)
dq = np.empty((n, 36), dtype=object)
for i in range(n):
    for c, (x, y, a, b) in enumerate(CELLS):
        D = DM[(i, x, y)]
        dq[i, c] = Q3(0) if D is None else re_prod(m0[(x, y)][a][b], D[a][b]) * Fr(2, 27)
print("[E1] exact q0 and first derivatives computed")

# ------------------------------------------------------------------ levels, CGLMP bound, level law
def gp(x, y, a, b):
    if (x, y) in ((0, 0), (1, 1)):
        return (a - b) % 3
    if (x, y) == (1, 0):
        return (b - a) % 3
    return (b - a - 1) % 3


LEV = [gp(*c) for c in CELLS]
sums = {}
for lam in itertools.product(range(3), repeat=4):
    sums[lam] = sum(gp(x, y, lam[x], lam[2 + y]) for (x, y) in LINKS)
assert min(sums.values()) == 2
facet = [lam for lam, s in sums.items() if s == 2]
assert len(facet) == 30
print("[E2] min over deterministic strategies of sum g' = 2; facet has 30 strategies")
Qlev = [Q3(Fr(4, 9), Fr(2, 9)), Q3(Fr(4, 9), Fr(-2, 9)), Q3(Fr(1, 9))]
for c, cell in enumerate(CELLS):
    assert q0[cell] == Qlev[LEV[c]] * Fr(1, 3), (cell, q0[cell])
print("[E3] DKZ_3: q0(a,b|xy) = Q_{g'}/3 exactly, Q = (2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9)")

# ------------------------------------------------------------------ criticality
for i in range(n):
    for k in range(3):
        s = sum((dq[i, c] for c in range(36) if LEV[c] == k), Q3(0))
        assert s.is_zero(), (i, k, s)
    for (x, y) in LINKS:      # per link normalisation of the derivative
        s = sum((dq[i, c] for c, cell in enumerate(CELLS) if cell[:2] == (x, y)), Q3(0))
        assert s.is_zero()
print("[E4] exact criticality: d_i Pi_k = 0 for k = 0,1,2 and all 36 directions")

# ------------------------------------------------------------------ gauge space and slice (exact rank over Q(sqrt3))
def herm_coords(H):
    """coordinates (9 Q3 numbers) of a Hermitian Z12 matrix in the Hs basis"""
    co = [H[i][i].re().real_q3() for i in range(3)]
    for i in range(3):
        for j in range(i + 1, 3):
            co.append(H[i][j].re().real_q3())
            co.append(-H[i][j].im().real_q3())
    return co


gauge = []
Ubases = [Ah[0], Ah[1], Bh[0], Bh[1]]
for m in range(4):
    U = Ubases[m]
    for a in range(3):
        P = mat(lambda r, c: U[r][a] * U[c][a].conj() * Fr(1, 3))      # |u_a><u_a| (normalised vector)
        v = [Q3(0)] * n
        v[m * 9:(m + 1) * 9] = herm_coords(P)
        gauge.append(v)
for j in range(9):
    v = [Q3(0)] * n
    hc = herm_coords(Hs[j])
    hb = herm_coords(mscale(mconj(Hs[j]), -1))
    for m in range(2):
        v[m * 9:(m + 1) * 9] = hc
    for m in range(2, 4):
        v[m * 9:(m + 1) * 9] = hb
    gauge.append(v)


def rank_q3(rows):
    rows = [list(r) for r in rows]
    rk = 0
    ncol = len(rows[0])
    for col in range(ncol):
        piv = next((r for r in range(rk, len(rows)) if not rows[r][col].is_zero()), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = rows[rk][col].inv()
        for r in range(len(rows)):
            if r != rk and not rows[r][col].is_zero():
                f = rows[r][col] * inv
                rows[r] = [rows[r][c] - f * rows[rk][c] for c in range(ncol)]
        rk += 1
    return rk


rg = rank_q3(gauge)
assert rg == 20
# choose slice coordinates greedily (float), verify exactly
Gf = np.array([[float(x) for x in v] for v in gauge])
I_sl = []
cur = Gf.copy()
for i in range(n):
    trial = np.vstack([cur, np.eye(n)[i]])
    if np.linalg.matrix_rank(trial, tol=1e-9) > np.linalg.matrix_rank(cur, tol=1e-9):
        I_sl.append(i)
        cur = trial
assert len(I_sl) == 16
unit = lambda i: [Q3(1) if k == i else Q3(0) for k in range(n)]
assert rank_q3(gauge + [unit(i) for i in I_sl]) == 36
print(f"[E5] gauge tangent space has rank 20 (exact); slice coordinates {I_sl}: gauge + slice = R^36 (exact)")

# ------------------------------------------------------------------ V0 (exact rational basis) and Psi
cons = []
for (x, y) in LINKS:                                  # normalisation
    cons.append([1 if c[:2] == (x, y) else 0 for c in CELLS])
for x in range(2):                                    # Alice marginals: y = 0 vs y = 1
    for a in range(3):
        cons.append([(1 if c[:3] == (x, 0, a) else 0) - (1 if c[:3] == (x, 1, a) else 0) for c in CELLS])
for y in range(2):
    for b in range(3):
        cons.append([(1 if (c[0], c[1], c[3]) == (0, y, b) else 0) - (1 if (c[0], c[1], c[3]) == (1, y, b) else 0)
                     for c in CELLS])
lev_rows = []
for (x, y) in LINKS:                                  # per-link level sums
    lev_rows.append([LEV[k] if c[:2] == (x, y) else 0 for k, c in enumerate(CELLS)])
V0 = sp.Matrix(cons + lev_rows).nullspace()
V0 = [[Fr(int(sp.fraction(e)[0]), int(sp.fraction(e)[1])) for e in vec] for vec in V0]
Vfull = sp.Matrix(cons + [[sum(lev_rows[l][k] for l in range(4)) for k in range(36)]]).nullspace()
print(f"[E6] dim V = {len(Vfull)} (facet direction space), dim V0 = {len(V0)}")
assert len(Vfull) == 23 and len(V0) == 20


def det_vec(lam):
    return [Fr(1) if (lam[c[0]], lam[2 + c[1]]) == (c[2], c[3]) else Fr(0) for c in CELLS]


# facet dimension: the 30 saturating strategies span an affine space of dimension 23 = dim V (exact rank)
F0 = det_vec(facet[0])
dif = sp.Matrix([[det_vec(l)[k] - F0[k] for k in range(36)] for l in facet[1:]])
assert dif.rank() == 23
print("[E7] the 30 facet strategies span an affine space of dimension 23 (exact): aff(F) = p* + V")
reps = []
for L in range(4):
    want = [2 if l == L else 0 for l in range(4)]
    lam = next(l for l in facet if [gp(x, y, l[x], l[2 + y]) for (x, y) in LINKS] == want)
    reps.append(det_vec(lam))


def Psi(z):
    """exact right inverse: level sums of Psi(z) on the four links = z (z sum-zero)"""
    out = [Fr(0)] * 36
    for i in range(3):
        for k in range(36):
            out[k] += (Fr(1, 2) * z[i]) * (reps[i][k] - reps[3][k]) if not isinstance(z[i], Q3) else 0
    return out


# Psi applied to Q3 data: keep as Q3 linear combinations
def Psi_q3(z):
    out = [Q3(0)] * 36
    for i in range(3):
        for k in range(36):
            dlt = reps[i][k] - reps[3][k]
            if dlt:
                out[k] = out[k] + z[i] * (Fr(1, 2) * dlt)
    return out


# checks: Psi(e) in V and has the right level sums
for i in range(3):
    zt = [Q3(0)] * 4
    zt[i] = Q3(1)
    zt[3] = Q3(-1)
    u = Psi_q3(zt)
    for row in cons:
        assert sum((u[k] * row[k] for k in range(36)), Q3(0)).is_zero()
    for l in range(4):
        assert sum((u[k] * lev_rows[l][k] for k in range(36)), Q3(0)) == zt[l]

# ------------------------------------------------------------------ interval data: beta, r*, S0
S3 = iv.sqrt(iv.mpf(3))
beta = ((16 + 24 * S3) - iv.sqrt(3280 - 960 * S3)) / 54
assert beta.a > 0 and beta.b < iv.mpf(2) / 3
res = 27 * beta ** 2 - (16 + 24 * S3) * beta + (16 * S3 - 12)
assert abs(float(mpf(res.mid))) < 1e-40
r = [1 + beta * (iv.mpf(1) / 2 - k) for k in range(3)]
assert all(x.a > 0 for x in r)
ell = [iv.log(x) for x in r]
Qi = [x.iv() for x in Qlev]
Pst = [Qi[k] / r[k] for k in range(3)]
assert all(p.a > 0 for p in Pst)
tot = Pst[0] + Pst[1] + Pst[2]
facet_val = Pst[1] + 2 * Pst[2]
assert abs(float(mpf(tot.mid)) - 1) < 1e-40 and abs(float(mpf(facet_val.mid)) - 0.5) < 1e-40
S0 = sum(Qi[k] * ell[k] for k in range(3))
print(f"[I1] beta in [{float(mpf(beta.a)):.15f}, {float(mpf(beta.b)):.15f}]; S(DKZ_3) = {float(mpf((S0/LN2).mid)):.13f} "
      f"bits; P* = ({', '.join(f'{float(mpf(p.mid)):.6f}' for p in Pst)}), sum = 1, P*_1 + 2 P*_2 = 1/2")
kappa = [None, -(ell[1] - ell[0]) / beta, -(ell[2] - ell[0]) / beta]

# ------------------------------------------------------------------ slice second derivatives (exact) and Hbar
q0i = [q0[c].iv() for c in CELLS]
rst = [r[LEV[c]] for c in range(36)]
lgr = [ell[LEV[c]] for c in range(36)]
dqi = [[dq[i, c].iv() for c in range(36)] for i in range(n)]

# pi_k (per-link level derivative sums), exact
def pis(i, k):
    return [sum((dq[i, c] for c, cell in enumerate(CELLS) if cell[:2] == L and LEV[c] == k), Q3(0)) for L in LINKS]


# numerical optimum for the V0 part (float least squares), then rationalised
V0f = np.array([[float(x) for x in v] for v in V0]).T              # 36 x 20
qf = np.array([float(mpf(x.mid)) for x in q0i])
rf = np.array([float(mpf(x.mid)) for x in rst])
kf = [None, float(mpf(kappa[1].mid)), float(mpf(kappa[2].mid))]
U_fixed = {}
C_rat = {}
for i in I_sl:
    pz1 = pis(i, 1)
    pz2 = pis(i, 2)
    u_fix = [Psi_q3(pz1)[k].iv() * kappa[1] + Psi_q3(pz2)[k].iv() * kappa[2] for k in range(36)]
    U_fixed[i] = u_fix
    uf = np.array([float(mpf(x.mid)) for x in u_fix])
    dqf = np.array([float(x) for x in dq[i]])
    W = 1 / np.sqrt(qf)
    Aml = (rf[:, None] * V0f) * W[:, None]
    bml = (dqf - rf * uf) * W
    c = np.linalg.lstsq(Aml, bml, rcond=None)[0]
    C_rat[i] = [Fr(float(x)).limit_denominator(10 ** 10) for x in c]
U = {}
for i in I_sl:
    v0part = [sum((C_rat[i][j] * V0[j][k] for j in range(20)), Fr(0)) for k in range(36)]
    U[i] = [U_fixed[i][k] + iv.mpf(v0part[k].numerator) / v0part[k].denominator for k in range(36)]

# exact equalisation check (structure): level sums of u_i = kappa1 pi1 + kappa2 pi2 (V0 part has zero level sums)
for i in I_sl:
    for l, L in enumerate(LINKS):
        lhs = sum((U[i][k] * rst[k] for k in range(36) if CELLS[k][:2] == L), iv.mpf(0))
        rhs = sum((dqi[i][k] * lgr[k] for k in range(36) if CELLS[k][:2] == L), iv.mpf(0))
        assert abs(float(mpf((lhs - rhs).mid))) < 1e-35, (i, L)

ns = len(I_sl)
Hb = [[None] * ns for _ in range(ns)]
d2cache = {}
for p, i in enumerate(I_sl):
    for s_, j in enumerate(I_sl):
        if s_ < p:
            Hb[p][s_] = Hb[s_][p]
            continue
        acc = iv.mpf(0)
        for c, (x, y, a, b) in enumerate(CELLS):
            D2 = d2m(i, j, x, y)
            Di, Dj = DM[(i, x, y)], DM[(j, x, y)]
            val = Q3(0)
            if D2 is not None:
                val = val + re_prod(m0[(x, y)][a][b], D2[a][b])
            if Di is not None and Dj is not None:
                val = val + re_prod(Di[a][b], Dj[a][b])
            val = val * Fr(2, 27)
            acc += val.iv() * lgr[c]
            acc += (dqi[i][c] - rst[c] * U[i][c]) * (dqi[j][c] - rst[c] * U[j][c]) / q0i[c]
        Hb[p][s_] = acc / 4
Hmid = np.array([[float(mpf(Hb[p][s].mid)) for s in range(ns)] for p in range(ns)])
print(f"[I2] Hbar on the slice: float eigenvalues max {np.linalg.eigvalsh(Hmid).max():+.6f}, "
      f"min {np.linalg.eigvalsh(Hmid).min():+.6f}; max interval width "
      f"{max(float(mpf(Hb[p][s].b - Hb[p][s].a)) for p in range(ns) for s in range(ns)):.1e}")


def interval_cholesky_pd(Mx):
    """True if every symmetric matrix in the interval matrix Mx is positive definite (interval Cholesky)."""
    m = len(Mx)
    L = [[iv.mpf(0)] * m for _ in range(m)]
    for j in range(m):
        s = Mx[j][j] - sum((L[j][k] ** 2 for k in range(j)), iv.mpf(0))
        if not s.a > 0:
            return False
        L[j][j] = iv.sqrt(s)
        for i in range(j + 1, m):
            L[i][j] = (Mx[i][j] - sum((L[i][k] * L[j][k] for k in range(j)), iv.mpf(0))) / L[j][j]
    return True


cmar = iv.mpf(1) / 200
negH = [[-Hb[p][s] - (cmar if p == s else 0) for s in range(ns)] for p in range(ns)]
ok = interval_cholesky_pd(negH)
print(f"[I3] interval Cholesky of -Hbar - (1/200) I succeeds: {ok}  =>  Hbar <= -0.005 I on the slice (certified)")
print("THEOREM 3 certificate:", "PASSED" if ok else "FAILED")

# ------------------------------------------------------------------ export data for the float cross-check
np.savez("d3_cert_data.npz", I_sl=np.array(I_sl), Hbar=Hmid,
         U=np.array([[float(mpf(U[i][k].mid)) for k in range(36)] for i in I_sl]),
         beta=float(mpf(beta.mid)))
