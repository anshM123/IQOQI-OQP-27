"""
GLOBAL_fam3BB.py -- rigorous branch-and-bound (python-flint arb, 106-bit balls): within the 3-parameter Fourier-shift
family F3 on Phi_3, S^UNI <= S(DKZ_3) with equality exactly at the DKZ copies.  Ansh Mishra, Aryan Senthilkumar,
2026-10-09.  Own code (does not import GLOBAL_famBB.py, whose Taylor model is wrong on mixed boxes, see
GLOBAL_NOTES.md Sec. 5).

Family (GLOBAL_fam3_exact.py): z = (phi_00, phi_01, phi_10), phi_11 = phi_01 + phi_10 - phi_00, link laws
Q_l(m) = K(phi_l + 2 pi m/3), K(psi) = (3 + 4 cos psi + 2 cos 2 psi)/9, m = b - a.  Shift-invariant, so (Lemma SI)
S^UNI(z) = min over laws mu of lambda = (alpha, b0, b1) in Z_3^3 of F(z; mu) = (1/4) sum_l D(Q_l || P_l(mu)),
P_l(mu)(m) = mu{hit_l(lambda) = m}, hit = (b0, b1, b0 - alpha, b1 - alpha).  For ANY weights w >= 0 with
sum w <= 1 the sub-probability P(w) is dominated by a local model, so S^UNI(z) <= F(z; w).

Box bound.  On a box B = c +- h the model is w(z) = w_c + M (z - c) (checked: w >= 0 and sum w <= 1 on B).
Per link l: if every Q_l(m) and P_l(m) is >= QMIN on B, the link divergence D_l is C^2 on B and
   D_l(c + d) = D_l(c) + g_l.d + (1/2) d^T H_l(xi) d,   xi in B,
with (all cells of the link included, so the '+1' terms of the derivative of Q log Q cancel: sum_m dQ = 0)
   g_l = sum_m [ dQ log(Q/P) - Q dP/P ](c),   H_l(xi) = sum_m [ d2Q log(Q/P) + Q a a^T ](xi),  a = dQ/Q - dP/P,
H_l enclosed by naive ball evaluation over B (dQ = K'(phi) L_l, d2Q = K''(phi) L_l L_l^T, dP = M rows, d2P = 0).
Otherwise the link is bounded crudely: D_l <= sum_m [ sup_{Q in [Qlo, Qhi]} Q log Q + Qhi (-log Plo) ].
Then  F <= (1/4) [ sum_good (D_l(c) + max_d (g.d + d^T H d / 2)) + sum_bad crude ],  and the quadratic maximum
over |d_i| <= h_i is bounded by the Lagrangian dual (any nu+, nu- >= 0) when -Hmid is positive definite (arb
Cholesky), else by the Gershgorin-type bound; the radius of [H] is added as (1/2) sum_ij rad(H_ij) h_i h_j.
Local cubes: at a DKZ copy z_c (exact, multiples of pi/6) the model is the exact KKT model (type weights, Prop K3)
plus a dyadic M supported on the 10 facet strategies with exactly zero column sums; then F(z_c) = S0 and
grad F(z_c) = 0 exactly (GLOBAL_fam3_exact.py: criticality, KKT identities), so negative definiteness of the
Hessian enclosure over the cube (arb Cholesky) gives F(z) < S0 for z != z_c in the cube.
usage: python GLOBAL_fam3BB.py check | cubes | run
"""
import sys
import json
import math
import time
import itertools
from fractions import Fraction
import numpy as np
from flint import arb, ctx

ctx.prec = 106
PI = arb.pi()
S3 = arb(3).sqrt()
BETA = ((16 + 24 * S3) - (3280 - 960 * S3).sqrt()) / 54
QLEV = [2 * (2 + S3) / 9, 2 * (2 - S3) / 9, arb(1) / 9]
RLEV = [1 + BETA * (arb(1) / 2 - k) for k in range(3)]
S0 = sum(QLEV[k] * RLEV[k].log() for k in range(3))              # S(DKZ_3) in nats (ball)
PSTAR = [QLEV[k] / RLEV[k] for k in range(3)]
LV = np.array([(1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 1, 1)], dtype=np.int64)
TRIP = list(itertools.product(range(3), repeat=3))
HIT = np.array([[b0 % 3, b1 % 3, (b0 - al) % 3, (b1 - al) % 3] for (al, b0, b1) in TRIP], dtype=np.int64)
E27 = np.zeros((27, 12))
for _i in range(27):
    for _l in range(4):
        E27[_i, 3 * _l + HIT[_i, _l]] = 1
QMIN = 1e-3
TWO_PI3 = 2 * math.pi / 3


# ------------------------------------------------------------------------------------------- float helpers
def Kf(psi):
    return (3 + 4 * np.cos(psi) + 2 * np.cos(2 * psi)) / 9


def dKf(psi):
    return (-4 * np.sin(psi) - 4 * np.sin(2 * psi)) / 9


def Qf(z):
    ph = LV @ z
    return np.array([[Kf(ph[l] + TWO_PI3 * m) for m in range(3)] for l in range(4)])


def gradQf(z):
    """[3, 4, 3]: dQ_l(m)/dz_i"""
    ph = LV @ z
    out = np.zeros((3, 4, 3))
    for l in range(4):
        for m in range(3):
            out[:, l, m] = dKf(ph[l] + TWO_PI3 * m) * LV[l]
    return out


def em(Q, w=None, iters=4000):
    q = Q.reshape(-1) / 4
    w = np.full(27, 1 / 27) if w is None else np.maximum(w, 1e-15) / np.maximum(w, 1e-15).sum()
    for it in range(iters):
        p = np.maximum(w @ E27, 1e-300)
        g = E27 @ (q / p)
        w = w * g
        w /= w.sum()
        if it % 50 == 49 and g.max() - 1 < 1e-13:
            break
    return w


def S_float(z, w=None):
    Q = Qf(z)
    w = em(Q, w)
    P = (w @ E27).reshape(4, 3)
    with np.errstate(divide="ignore", invalid="ignore"):
        t = np.where(Q > 0, Q * np.log(Q / P), 0.0)
    return 0.25 * t.sum(), w


def model_at(c, h, w0=None, eps=1e-7):
    """float model: EM weights at c and a first-order correction M (27 x 3) on the support (least squares that
    makes the model track the optimal face), scaled so that w >= 0 on the box; tiny uniform admixture."""
    Q = Qf(c)
    w = em(Q, w0)
    P = w @ E27
    q = Q.reshape(-1)
    supp = np.nonzero(w > 1e-9 * w.max())[0]
    M = np.zeros((27, 3))
    dQ = gradQf(c).reshape(3, 12)
    if len(supp) >= 2:
        k = len(supp)
        N = np.zeros((k, k - 1))
        for j in range(k - 1):
            N[j, j] = 1
            N[k - 1, j] = -1
        r = np.where(P > 0, q / np.maximum(P, 1e-300), 0)
        A = (r[:, None] * E27[supp].T) @ N
        wt = 1 / np.sqrt(np.maximum(q, 1e-9))
        for i in range(3):
            t = np.linalg.lstsq(A * wt[:, None], dQ[i] * wt, rcond=None)[0]
            M[supp, i] = N @ t
    need = np.abs(M) @ h
    with np.errstate(divide="ignore", invalid="ignore"):
        s = np.min(np.where(need > 0, 0.8 * w / need, np.inf))
    if s < 1:
        M = M * s
    w = (1 - eps) * w + eps / 27
    M = (1 - eps) * M
    return w * (1 - 1e-12), M


# ------------------------------------------------------------------------------------------- arb helpers
def A(x):
    return arb(float(x))


def K_arb(psi):
    return (3 + 4 * psi.cos() + 2 * (2 * psi).cos()) / 9


def dK_arb(psi):
    return (-4 * psi.sin() - 4 * (2 * psi).sin()) / 9


def d2K_arb(psi):
    return (-4 * psi.cos() - 8 * (2 * psi).cos()) / 9


UNIT = arb("0.5 +/- 0.5")


def link_data(phi_c, rad):
    """for one link: point values at phi_c (arb) and enclosures over phi_c +- rad (Q intersected with [0,1])."""
    out_c, out_b = [], []
    for m in range(3):
        pc = phi_c + 2 * PI * m / 3
        out_c.append((K_arb(pc), dK_arb(pc)))
        pb = pc + arb(0, rad)
        Kb = K_arb(pb)
        try:
            Kb = Kb.intersection(UNIT)
        except Exception:
            pass
        out_b.append((Kb, dK_arb(pb), d2K_arb(pb)))
    return out_c, out_b


def xlogx_sup(lo, hi):
    f = lambda x: 0.0 if x <= 0 else x * math.log(x)
    return max(f(max(lo, 0.0)), f(min(hi, 1.0)), 0.0 if lo <= 0 <= hi else -math.inf)


def quad_max(gm, Hm, h):
    """rigorous upper bound (arb) of max_{|d_i| <= h_i} gm.d + (1/2) d^T Hm d  (gm, Hm floats, exact as arb)."""
    n = 3
    negH = [[A(-Hm[i][j]) for j in range(n)] for i in range(n)]
    Lf = chol(negH)
    crude = sum((abs(A(gm[i])) * A(h[i]) for i in range(n)), arb(0)) + \
        sum((A(max(Hm[i][i], 0.0)) * A(h[i]) ** 2 for i in range(n)), arb(0)) / 2 + \
        sum((abs(A(Hm[i][j])) * A(h[i]) * A(h[j]) for i in range(n) for j in range(n) if i != j), arb(0)) / 2
    if Lf is None:
        return crude
    Hn = np.array(Hm, float)
    gn = np.array(gm, float)
    d = np.zeros(n)
    for _ in range(100):
        grad = gn + Hn @ d
        free = ~(((d >= h) & (grad > 0)) | ((d <= -h) & (grad < 0)))
        dn = d.copy()
        if free.any():
            try:
                dn[free] = np.linalg.solve(Hn[np.ix_(free, free)], -(gn[free] + Hn[np.ix_(free, ~free)] @ d[~free]))
            except np.linalg.LinAlgError:
                break
        dn = np.clip(dn, -h, h)
        if np.allclose(dn, d, atol=1e-16, rtol=0):
            break
        d = dn
    grad = gn + Hn @ d
    nup = np.where((d >= h * (1 - 1e-9)) & (grad > 0), grad, 0.0)
    num = np.where((d <= -h * (1 - 1e-9)) & (grad < 0), -grad, 0.0)
    w = [A(gm[i]) - A(nup[i]) + A(num[i]) for i in range(n)]
    y = [arb(0)] * n
    for i in range(n):
        y[i] = (w[i] - sum((Lf[i][k] * y[k] for k in range(i)), arb(0))) / Lf[i][i]
    dual = sum((t * t for t in y), arb(0)) / 2 + sum((A(nup[i] + num[i]) * A(h[i]) for i in range(n)), arb(0))
    return dual if dual.upper() < crude.upper() else crude


def chol(Mx):
    n = len(Mx)
    Lf = [[arb(0)] * n for _ in range(n)]
    for j in range(n):
        s = Mx[j][j] - sum((Lf[j][k] * Lf[j][k] for k in range(j)), arb(0))
        if not s > 0:
            return None
        Lf[j][j] = s.sqrt()
        for i in range(j + 1, n):
            Lf[i][j] = (Mx[i][j] - sum((Lf[i][k] * Lf[j][k] for k in range(j)), arb(0))) / Lf[j][j]
    return Lf


def model_cells(wa, Ma, h, exact_mass=False):
    """P_l(m) at the centre, its gradient (3-vector, constant), and the enclosure over the box; validity flag."""
    Pc = [[arb(0) for _ in range(3)] for _ in range(4)]
    Pg = [[[arb(0)] * 3 for _ in range(3)] for _ in range(4)]
    for lam in range(27):
        for l in range(4):
            m = int(HIT[lam, l])
            Pc[l][m] += wa[lam]
            for i in range(3):
                Pg[l][m][i] += Ma[lam][i]
    hb = [arb(0, float(h[i])) for i in range(3)]
    Pb = [[Pc[l][m] + sum((Pg[l][m][i] * hb[i] for i in range(3)), arb(0)) for m in range(3)] for l in range(4)]
    ok = True
    for lam in range(27):
        lo = wa[lam] - sum((abs(Ma[lam][i]) * A(h[i]) for i in range(3)), arb(0))
        if not lo >= 0:
            ok = False
    if not exact_mass:
        tot = sum(wa, arb(0)) + sum((abs(sum((Ma[lam][i] for lam in range(27)), arb(0))) * A(h[i]) for i in range(3)),
                                    arb(0))
        if not tot <= 1:
            ok = False
    # exact_mass: copy models, total mass exactly 1 (4 P*_2 + 2 P*_1 = 1, Prop K3 / GLOBAL_fam3_exact E4) and
    # column sums of M exactly 0 (dyadic, checked in load_copies)
    return Pc, Pg, Pb, ok


def F_bound(zc_arb, h, wa, Ma, require_all_good=False, exact_mass=False):
    """returns (Fc_good, g (arb 3), H (arb 3x3), crude) or None."""
    Pc, Pg, Pb, ok = model_cells(wa, Ma, h, exact_mass)
    if not ok:
        return None
    Fc = arb(0)
    g = [arb(0)] * 3
    H = [[arb(0)] * 3 for _ in range(3)]
    crude = arb(0)
    for l in range(4):
        Lv = [int(x) for x in LV[l]]
        phi_c = sum((Lv[i] * zc_arb[i] for i in range(3)), arb(0))
        rad = sum(abs(Lv[i]) * float(h[i]) for i in range(3)) * (1 + 1e-12)
        dc, db = link_data(phi_c, rad)
        for m in range(3):
            Qc, dKc = dc[m]
            Qb, dKb, d2Kb = db[m]
            good = (Qb > QMIN) and (Pb[l][m] > QMIN)
            if not good:
                # zeroth order, per cell: Q log(Q/P) <= sup_{Q in [lo, hi]} Q log(Q / P_lo) (decreasing in P;
                # convex in Q with value 0 at Q = 0, so the sup is at an endpoint)
                if require_all_good or not Pb[l][m] > 0:
                    return None
                plo = Pb[l][m].lower()
                lo = Qb.lower()
                hi = Qb.upper()
                if lo < 0:
                    lo = arb(0)
                if hi > 1:
                    hi = arb(1)
                fl = arb(0) if lo == 0 else lo * (lo.log() - plo.log())
                fh = arb(0) if hi == 0 else hi * (hi.log() - plo.log())
                crude += fl.upper() if fl.upper() > fh.upper() else fh.upper()
                continue
            # Taylor, per cell, with the complete derivatives of Q log(Q/P) (P affine in z):
            #   d f = dQ (log(Q/P) + 1) - Q dP/P,   d2 f = d2Q (log(Q/P) + 1) + Q a a^T,  a = dQ/Q - dP/P
            lr_c = Qc.log() - Pc[l][m].log()
            Fc += Qc * lr_c
            for i in range(3):
                g[i] += dKc * Lv[i] * (lr_c + 1) - Qc * Pg[l][m][i] / Pc[l][m]
            lr_b = Qb.log() - Pb[l][m].log()
            a = [dKb * Lv[i] / Qb - Pg[l][m][i] / Pb[l][m] for i in range(3)]
            for i in range(3):
                for j in range(i, 3):
                    v = d2Kb * Lv[i] * Lv[j] * (lr_b + 1) + Qb * a[i] * a[j]
                    H[i][j] += v
    for i in range(3):
        for j in range(i + 1, 3):
            H[j][i] = H[i][j]
    q4 = arb(1) / 4
    return Fc * q4, [x * q4 for x in g], [[x * q4 for x in row] for row in H], crude * q4


def box_ub(c, h, w, M):
    zc = [A(x) for x in c]
    wa = [A(x) for x in w]
    Ma = [[A(M[lam, i]) for i in range(3)] for lam in range(27)]
    T = F_bound(zc, h, wa, Ma)
    if T is None:
        return None
    Fc, g, H, crude = T
    gm = [float(x.mid()) for x in g]
    Hm = [[float(H[i][j].mid()) for j in range(3)] for i in range(3)]
    gerr = sum((abs(g[i] - A(gm[i])).upper() * A(h[i]) for i in range(3)), arb(0))
    herr = sum((abs(H[i][j] - A(Hm[i][j])).upper() * A(h[i]) * A(h[j]) for i in range(3) for j in range(3)),
               arb(0)) / 2
    return Fc + quad_max(gm, Hm, np.asarray(h, float)) + gerr + herr + crude


def separable_ub(c, h, w, piece=0.004):
    """constant model w (no slope): F(z) <= (1/4) sum_l sup_{phi in I_l} D(Q(phi) || P_l), I_l = phi_l(c) +- r_l.
    Each sup: I_l cut into pieces of length <= piece; on a piece J and for each cell m, K(J + c_m) in [lo, hi]
    (ball evaluation) and x -> x log(x/P) is convex with value 0 at 0, so its sup over the piece is at most
    max(f(lo), f(hi)).  Returns arb or None (model invalid)."""
    wa = [A(x) for x in w]
    tot_w = sum(wa, arb(0))
    if not tot_w <= 1 or any(not x >= 0 for x in wa):
        return None
    P = [[arb(0) for _ in range(3)] for _ in range(4)]
    for lam in range(27):
        for l in range(4):
            P[l][int(HIT[lam, l])] += wa[lam]
    total = arb(0)
    for l in range(4):
        Lv = [int(x) for x in LV[l]]
        phc = sum(Lv[i] * float(c[i]) for i in range(3))                 # float centre of the phase interval
        r = sum(abs(Lv[i]) * float(h[i]) for i in range(3))
        npc = max(1, int(math.ceil(2 * r / piece)))
        lo_end = A(phc) - A(r) * (1 + 1e-12) - 1e-15                      # enclose the exact interval
        step = (2 * A(r) * (1 + 1e-12) + 2e-15) / npc
        best = None
        plog = [P[l][m].log() for m in range(3)]
        if any(not P[l][m] > 0 for m in range(3)):
            return None
        for k in range(npc):
            a = lo_end + k * step
            mid = a + step / 2
            J = mid + arb(0, float((step / 2).upper()) * (1 + 1e-12))     # encloses the piece [a, a + step]
            s = arb(0)
            for m in range(3):
                Kb = K_arb(J + 2 * PI * m / 3)
                klo = Kb.lower()
                khi = Kb.upper()
                if klo < 0:
                    klo = arb(0)
                if khi > 1:
                    khi = arb(1)
                fl = arb(0) if klo == 0 else klo * (klo.log() - plog[m])
                fh = arb(0) if khi == 0 else khi * (khi.log() - plog[m])
                s += fl.upper() if fl.upper() > fh.upper() else fh.upper()
            if best is None or s.upper() > best.upper():
                best = s
        total += best
    return total / 4


def copy_taylor_ub(cp, c, h):
    """Taylor bound on the box c +- h with the exact copy model w(z) = w* + M (z - z_c) (valid only where w >= 0)."""
    zc = [A(x) for x in c]
    d0 = [zc[i] - cp["z_arb"][i] for i in range(3)]
    wa = [cp["wa"][lam] + sum((A(cp["M"][lam, i]) * d0[i] for i in range(3)), arb(0)) for lam in range(27)]
    Ma = [[A(cp["M"][lam, i]) for i in range(3)] for lam in range(27)]
    T = F_bound(zc, h, wa, Ma, exact_mass=True)
    if T is None:
        return None
    Fc, g, H, crude = T
    gm = [float(x.mid()) for x in g]
    Hm = [[float(H[i][j].mid()) for j in range(3)] for i in range(3)]
    gerr = sum((abs(g[i] - A(gm[i])).upper() * A(h[i]) for i in range(3)), arb(0))
    herr = sum((abs(H[i][j] - A(Hm[i][j])).upper() * A(h[i]) * A(h[j]) for i in range(3) for j in range(3)),
               arb(0)) / 2
    return Fc + quad_max(gm, Hm, np.asarray(h, float)) + gerr + herr + crude


# ------------------------------------------------------------------------------------------- copies and cubes
def load_copies():
    D = json.load(open("GLOBAL_fam3_copies.json"))
    out = []
    for cp in D["copies"]:
        p = cp["p"]
        z_arb = [PI * int(t) / 6 for t in p]
        z_f = np.array([math.pi * int(t) / 6 for t in p])
        lev = np.array(cp["levels"])
        facet = cp["facet"]
        types = cp["types"]
        W = {"A": PSTAR[2], "B": PSTAR[1] / 4, "C": PSTAR[1] / 2}
        wa = [arb(0)] * 27
        for lam, t in zip(facet, types):
            wa[lam] = W[t]
        # dyadic first-order correction on the facet, column sums exactly zero (least squares on the Hessian PSD term)
        q = Qf(z_f).reshape(-1)
        rk = np.array([float(RLEV[k].mid()) for k in range(3)])
        r = rk[lev.reshape(-1)]
        dQ = gradQf(z_f).reshape(3, 12)
        k = len(facet)
        N = np.zeros((k, k - 1))
        for j in range(k - 1):
            N[j, j] = 1
            N[k - 1, j] = -1
        Acols = (r[:, None] * E27[facet].T) @ N
        wt = 1 / np.sqrt(q)
        M = np.zeros((27, 3))
        for i in range(3):
            t = np.linalg.lstsq(Acols * wt[:, None], dQ[i] * wt, rcond=None)[0]
            col = np.round((N @ t) * 2 ** 30) / 2 ** 30
            col[-1] = -np.sum(col[:-1])
            assert Fraction(float(col.sum())) == 0 and all(Fraction(float(x)) * 2 ** 30 == int(round(x * 2 ** 30))
                                                           for x in col)
            M[facet, i] = col
        out.append(dict(p=p, z_arb=z_arb, z_f=z_f, wa=wa, M=M))
    return out


def certify_cube(cp, rho):
    """True iff on |z - z_c|_inf <= rho the exact copy model is valid, every cell is good, and -[H] is PD."""
    h = np.full(3, rho)
    Ma = [[arb(Fraction(float(cp["M"][lam, i])).numerator) / arb(Fraction(float(cp["M"][lam, i])).denominator)
           for i in range(3)] for lam in range(27)]
    zbox = [cp["z_arb"][i] for i in range(3)]
    T = F_bound(zbox, h, cp["wa"], Ma, require_all_good=True, exact_mass=True)
    if T is None:
        return False, None
    Fc, g, H, crude = T
    Lf = chol([[-H[i][j] for j in range(3)] for i in range(3)])
    # consistency of the exact identities (not used as proof; they are exact facts): F(c) = S0, g = 0
    assert abs(float((Fc - S0).mid())) < 1e-25 and all(abs(float(x.mid())) < 1e-20 for x in g)
    return Lf is not None, [[float(H[i][j].mid()) for j in range(3)] for i in range(3)]


# ------------------------------------------------------------------------------------------- branch and bound
def run(max_boxes=3_000_000, min_h=1e-7, init=8):
    copies = load_copies()
    # the only DKZ copies within distance 0.36 of [0, 9/4]^3 are the two copies of the fundamental domain (their
    # translates by (2 pi/3) Z^3 lie at sup-distance >= 5 pi/6 - 9/4 > 0.36 from the box); the copy model is used
    # only for boxes within 0.12 of these two points.
    copies_all = copies
    cubes = []
    for cp in copies:
        rho = None
        for r in (0.05, 0.03, 0.02, 0.01, 0.007, 0.005, 0.003, 0.002, 0.001, 5e-4, 2e-4, 1e-4):
            ok, Hm = certify_cube(cp, r)
            if ok:
                rho = r
                break
        assert rho is not None, "no local cube certified"
        lo = [(cp["z_arb"][i] - rho).upper() for i in range(3)]
        hi = [(cp["z_arb"][i] + rho).lower() for i in range(3)]
        cubes.append((lo, hi, rho))
        print(f"local cube at {cp['p']} (pi/6 units): rho = {rho}; Hessian at the copy (float) eigenvalues "
              f"{np.round(np.linalg.eigvalsh(np.array(Hm)), 5)}", flush=True)
    import heapq
    T0 = time.time()
    # dyadic grid covering [0, 9/4]^3, which contains the fundamental domain [0, 2 pi/3]^3; all centres and
    # half-widths stay dyadic, so the float bisection is exact and the children tile the parent exactly.
    hw = 0.125
    side = 9 * 2 * hw
    heap = []
    cnt = 0
    for idx in itertools.product(range(9), repeat=3):
        c = np.array([(2 * k + 1) * hw for k in idx])
        heapq.heappush(heap, (-hw, cnt, c, np.full(3, hw), None))
        cnt += 1
    n_cert = n_cube = 0
    n_proc = 0
    vol_cert = 0.0
    smallest = math.inf
    worst_gap = math.inf
    eps_used = {}
    rows = []                 # certificate: c(3), h(3), method (0 cube, 1 copy-Taylor, 2 EM-Taylor, 3 separable), eps, copy
    models = []               # w (27) and M (27 x 3) for methods 2, 3
    while heap:
        _, _, c, h, w0 = heapq.heappop(heap)
        n_proc += 1
        if n_proc > max_boxes:
            print("ABORT: box budget exhausted", flush=True)
            return False
        inside = False
        for (lo, hi, rho) in cubes:
            if all((arb(float(c[i])) - arb(float(h[i]))) >= lo[i] and (arb(float(c[i])) + arb(float(h[i]))) <= hi[i]
                   for i in range(3)):
                inside = True
                break
        if inside:
            rows.append(list(c) + list(h) + [0, 0.0, -1])
            models.append(np.zeros(27 + 81))
            n_cube += 1
            vol_cert += float(np.prod(2 * h))
            continue
        certified = False
        w = None
        near = [k for k, cp in enumerate(copies_all) if np.max(np.abs(c - cp["z_f"])) < 0.12]
        rec = None
        if near:
            for k in near:
                ub = copy_taylor_ub(copies_all[k], c, h)
                if ub is not None and ub < S0:
                    certified = True
                    eps_used["copy"] = eps_used.get("copy", 0) + 1
                    rec = (1, 0.0, k, np.zeros(27 + 81))
                    break
        if not certified:
            for eps in (1e-7, 1e-3, 1e-2):
                w, M = model_at(c, h, w0, eps)
                ub = box_ub(c, h, w, M)
                if ub is not None and ub < S0:
                    certified = True
                    eps_used["tay%g" % eps] = eps_used.get("tay%g" % eps, 0) + 1
                    rec = (2, eps, -1, np.concatenate([w, M.reshape(-1)]))
                    break
                ub = separable_ub(c, h, w)
                if ub is not None and ub < S0:
                    certified = True
                    eps_used["sep%g" % eps] = eps_used.get("sep%g" % eps, 0) + 1
                    rec = (3, eps, -1, np.concatenate([w, np.zeros(81)]))
                    break
        if certified:
            rows.append(list(c) + list(h) + [rec[0], rec[1], rec[2]])
            models.append(rec[3])
            n_cert += 1
            vol_cert += float(np.prod(2 * h))
            smallest = min(smallest, float(h.max()))
            worst_gap = min(worst_gap, float((S0 - ub).lower()))
            continue
        if h.max() < min_h:
            print(f"FAIL: box at {c} half-width {h} not certified (ub {ub})", flush=True)
            return False
        i = int(np.argmax(h))
        h2 = h.copy()
        h2[i] /= 2
        for s in (-1, 1):
            c2 = c.copy()
            c2[i] += s * h2[i]
            assert c2[i] - s * h2[i] == c[i]                      # exact dyadic bisection
            heapq.heappush(heap, (-float(h2.max()), cnt, c2, h2, w))
            cnt += 1
        if n_proc % 5000 == 0:
            print(f"  processed {n_proc}, pending {len(heap)} (largest half-width {-heap[0][0]:.2e}), certified "
                  f"{n_cert} + {n_cube} in cubes, volume fraction {vol_cert / side ** 3:.6f}, eps used {eps_used}  "
                  f"[{time.time() - T0:.0f}s]", flush=True)
    print(f"DONE: [0, 9/4]^3 (contains the fundamental domain [0, 2pi/3]^3) covered exactly: {n_cert} boxes certified "
          f"by the Taylor/zeroth-order bound, {n_cube} inside the local cubes; boxes processed {n_proc}; certified "
          f"volume fraction {vol_cert / side ** 3:.12f}; smallest certified half-width {smallest:.2e}; smallest "
          f"certified gap S0 - UB {worst_gap:.3e} nats; eps used {eps_used}  [{time.time() - T0:.0f}s]", flush=True)
    np.savez_compressed("GLOBAL_fam3BB_cert.npz", rows=np.array(rows), models=np.array(models),
                        cubes=np.array([[cb[2]] for cb in cubes]))
    print("certificate written: GLOBAL_fam3BB_cert.npz", flush=True)
    return True


def check():
    """consistency of the family with the actual strategy on Phi_3 and with S(DKZ_3) (float)."""
    rng = np.random.default_rng(1)
    w3 = np.exp(2j * np.pi / 3)
    phi = np.ones(3) / np.sqrt(3)
    phi3 = np.eye(3).reshape(-1) / np.sqrt(3)
    err = 0
    for t in range(20):
        s = rng.uniform(-2, 2, 2)
        tt = rng.uniform(-2, 2, 2)
        z = 2 * np.pi / 3 * np.array([tt[0] - s[0], tt[1] - s[0], tt[0] - s[1]])
        Q = Qf(z)
        for x in range(2):
            for y in range(2):
                l = [0, 1, 2, 3][2 * x + y]
                for a in range(3):
                    for b in range(3):
                        va = np.array([w3 ** (k * (a + s[x])) for k in range(3)]) / np.sqrt(3)
                        vb = np.array([w3 ** (-k * (b + tt[y])) for k in range(3)]) / np.sqrt(3)
                        qq = abs(np.kron(va, vb).conj() @ phi3) ** 2
                        err = max(err, abs(qq - Q[l, (b - a) % 3] / 3))
    zs = np.array([-math.pi / 6, -math.pi / 2, math.pi / 6])
    Sd, _ = S_float(zs)
    print(f"family vs quantum strategy on Phi_3: max error {err:.2e}; S(DKZ point) = {Sd / math.log(2):.10f} bits; "
          f"S0 = {float(S0.mid()) / math.log(2):.10f} bits; S0 ball {S0}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd == "check":
        check()
    elif cmd == "cubes":
        for cp in load_copies():
            for r in (0.05, 0.02, 0.01, 0.005, 0.002, 0.001, 5e-4):
                ok, Hm = certify_cube(cp, r)
                print(cp["p"], r, ok)
    elif cmd == "run":
        ok = run()
        print("THEOREM VERIFIED" if ok else "NOT VERIFIED")
