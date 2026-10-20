"""Third-order box bound for  g(y) = (1/2) sum_cells q log(q/p(y)) >= Phi(A*, Bt(y); mu*)  (see nash_core.py).

On a box c +- h, for the 'good' cells (q bounded away from 0 on the box):
    g(c + t) = g(c) + grad g(c).t + (1/2) t^T H(c) t + (1/6) D3g(xi)[t, t, t],   xi in the box,
with g(c), grad g(c), H(c) evaluated at the centre (tight intervals) and D3g enclosed over the box.  So
    max over the box of g_good <= g(c) + QPmax(grad g(c), H(c), h) + (1/6) sum_{ijk} |D3g_ijk| h_i h_j h_k.
Bad cells are bounded by the vertex maximum of the jointly convex q log(q/p), as in nash_core.
QPmax is the smallest of three rigorous bounds: separable (scaled Gershgorin), separable (certified isotropic
eigenvalue bound), and the Lagrangian dual (1/2) g^T (Lam - H)^{-1} g + (1/2) sum lam_i h_i^2 (exact for concave H,
with lam from a float solve of the box QP and Lam - H certified positive definite by interval Cholesky).
Third derivative of q log(q/p) (p linear in y, a = dq/q - dp/p, pi = dp/p):
    q_ijk (L + 1) + q_ij a_k + q_ik a_j + q_jk a_i - q [a_i a_j a_k + a_i a_j pi_k + a_j a_k pi_i + a_i a_k pi_j].
"""
import itertools
import numpy as np

import nash_iv as V
from nash_iv import IV
import nash_core as C
from nash_core import NP, TI, TJ, NH, PIDX, DIAG

TRI = [t for t in itertools.combinations_with_replacement(range(NP), 3)]
I3 = np.array([t[0] for t in TRI])
J3 = np.array([t[1] for t in TRI])
K3 = np.array([t[2] for t in TRI])
PJK = np.array([PIDX[(t[1], t[2])] for t in TRI])
PIK = np.array([PIDX[(t[0], t[2])] for t in TRI])
PIJ = np.array([PIDX[(t[0], t[1])] for t in TRI])
MULT = np.array([len(set(itertools.permutations(t))) for t in TRI], dtype=float)
DIAG3 = np.array([TRI.index((k, k, k)) for k in range(NP)])
NT = len(TRI)


# triple index of sorted (i, j, k) for packed pair p = (i, j) and k
PK3 = np.zeros((NH, NP), dtype=int)
for _p, (_i, _j) in enumerate(zip(TI, TJ)):
    for _k in range(NP):
        PK3[_p, _k] = TRI.index(tuple(sorted((int(_i), int(_j), _k))))
# packed pair index of (i, j) for gradient refinement
PIJF = np.array([[PIDX[(i, j)] for j in range(NP)] for i in range(NP)])


def _meet(a, b):
    return IV(np.maximum(a.lo, b.lo), np.minimum(a.hi, b.hi))


def refine(cv, cg, cH, qv, qg, qH, qT, h):
    """nested mean-value refinement of the box enclosures (all arrays (N, 18, ...)):
       H_box <- H(c) + sum_k T_box[., k] [-h_k, h_k],  g_box <- g(c) + sum_j H_box[., j] [-h_j, h_j],
       v_box <- v(c) + sum_i g_box[i] [-h_i, h_i]   (each intersected with the naive enclosure)."""
    hb = IV(-h, h)[:, None, :]                                   # (N, 1, 6)
    if qT is not None and cH is not None:
        Tk = qT[:, :, PK3]                                       # (N, 18, 21, 6)
        add = V.isum(Tk * hb[:, :, None, :], axis=3)
        qH = _meet(qH, cH + add)
    Hj = qH[:, :, PIJF]                                          # (N, 18, 6, 6)
    addg = V.isum(Hj * hb[:, :, None, :], axis=3)
    qg = _meet(qg, cg + addg)
    addv = V.isum(qg * hb, axis=2)
    qv = _meet(qv, cv + addv)
    return qv, qg, qH


class Jet3:
    """value v, gradient g (6), packed Hessian H (21), packed third derivatives T (56) or None."""
    __slots__ = ("v", "g", "H", "T")

    def __init__(self, v, g, H, T):
        self.v, self.g, self.H, self.T = v, g, H, T

    def __add__(self, o):
        return Jet3(self.v + o.v, self.g + o.g, self.H + o.H, None if self.T is None else self.T + o.T)

    def __sub__(self, o):
        return Jet3(self.v - o.v, self.g - o.g, self.H - o.H, None if self.T is None else self.T - o.T)

    def __neg__(self):
        return Jet3(-self.v, -self.g, -self.H, None if self.T is None else -self.T)

    def __mul__(self, o):
        f, h = self, o
        v = f.v * h.v
        g = f.g * h.v[..., None] + f.v[..., None] * h.g
        H = (f.H * h.v[..., None] + f.v[..., None] * h.H + f.g[..., TI] * h.g[..., TJ] + f.g[..., TJ] * h.g[..., TI])
        if f.T is None:
            return Jet3(v, g, H, None)
        T = (f.v[..., None] * h.T + f.T * h.v[..., None]
             + f.g[..., I3] * h.H[..., PJK] + f.g[..., J3] * h.H[..., PIK] + f.g[..., K3] * h.H[..., PIJ]
             + f.H[..., PIJ] * h.g[..., K3] + f.H[..., PIK] * h.g[..., J3] + f.H[..., PJK] * h.g[..., I3])
        return Jet3(v, g, H, T)

    def scale(self, c):
        return Jet3(self.v * c, self.g * c, self.H * c, None if self.T is None else self.T * c)

    def sqr(self):
        f = self
        v = f.v.sqr()
        g = (f.v[..., None] * f.g) * 2.0
        H = (f.v[..., None] * f.H + f.g[..., TI] * f.g[..., TJ]) * 2.0
        if f.T is None:
            return Jet3(v, g, H, None)
        T = (f.v[..., None] * f.T + f.g[..., I3] * f.H[..., PJK] + f.g[..., J3] * f.H[..., PIK]
             + f.g[..., K3] * f.H[..., PIJ]) * 2.0
        return Jet3(v, g, H, T)


def _z(shape):
    return IV(np.zeros(shape))


def pjets(k, s, c, order3):
    """jets of sin and cos of coordinate k with value enclosures s, c (IV (N,))."""
    N = s.lo.shape[0]
    gs, gc = _z((N, NP)), _z((N, NP))
    Hs, Hc = _z((N, NH)), _z((N, NH))
    gs[:, k] = c
    gc[:, k] = -s
    Hs[:, DIAG[k]] = -s
    Hc[:, DIAG[k]] = -c
    if order3:
        Ts, Tc = _z((N, NT)), _z((N, NT))
        Ts[:, DIAG3[k]] = -c
        Tc[:, DIAG3[k]] = s
    else:
        Ts = Tc = None
    return Jet3(s, gs, Hs, Ts), Jet3(c, gc, Hc, Tc)


def pjets_affine(Tk, s, c, order3):
    """jets in u of sin and cos of x = x0 + Tk.u (Tk: IV row (6,), may be an interval)."""
    N = s.lo.shape[0]
    Tg = IV(np.broadcast_to(Tk.lo, (N, NP)).copy(), np.broadcast_to(Tk.hi, (N, NP)).copy())
    TT = Tk[TI] * Tk[TJ]
    TT = IV(np.broadcast_to(TT.lo, (N, NH)).copy(), np.broadcast_to(TT.hi, (N, NH)).copy())
    gs = c[:, None] * Tg
    gc = (-s)[:, None] * Tg
    Hs = (-s)[:, None] * TT
    Hc = (-c)[:, None] * TT
    if order3:
        T3_ = Tk[I3] * Tk[J3] * Tk[K3]
        T3_ = IV(np.broadcast_to(T3_.lo, (N, NT)).copy(), np.broadcast_to(T3_.hi, (N, NT)).copy())
        Ts = (-c)[:, None] * T3_
        Tc = s[:, None] * T3_
    else:
        Ts = Tc = None
    return Jet3(s, gs, Hs, Ts), Jet3(c, gc, Hc, Tc)


class CJ:
    __slots__ = ("re", "im")

    def __init__(self, re, im):
        self.re, self.im = re, im

    def __mul__(self, o):
        if isinstance(o, Jet3):
            return CJ(self.re * o, self.im * o)
        return CJ(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def __add__(self, o):
        if isinstance(o, Jet3):
            return CJ(self.re + o, self.im)
        return CJ(self.re + o.re, self.im + o.im)

    def __sub__(self, o):
        if isinstance(o, Jet3):
            return CJ(self.re - o, self.im)
        return CJ(self.re - o.re, self.im - o.im)

    def __neg__(self):
        return CJ(-self.re, -self.im)


def _zero_like(j):
    return Jet3(_z(j.v.shape), _z(j.g.shape), _z(j.H.shape), None if j.T is None else _z(j.T.shape))


def bt3(lo, hi, point, order3, T=None, x0=None):
    """jets of Bt over boxes [lo, hi] (point=False) or at the points lo (point=True).
    With T (IV 6x6) and x0 (IV (6,)), [lo, hi] are boxes in u and x = x0 + T u (jets in u)."""
    if T is None:
        if point:
            sc = [V.sincos_point(lo[:, k]) for k in range(NP)]
        else:
            sc = [V.sincos(IV(lo[:, k], hi[:, k])) for k in range(NP)]
        J = [pjets(k, sc[k][0], sc[k][1], order3) for k in range(NP)]
    else:
        U = IV(lo, hi)
        J = []
        for k in range(NP):
            Tk = T[k]
            xk = V.isum(U * IV(np.broadcast_to(Tk.lo, lo.shape).copy(), np.broadcast_to(Tk.hi, lo.shape).copy()),
                        axis=1) + x0[k]
            s_, c_ = V.sincos(xk)
            J.append(pjets_affine(Tk, s_, c_, order3))
    s12, c12 = J[0]
    s13, c13 = J[1]
    s23, c23 = J[2]
    sd, cd = J[3]
    s1, c1 = J[4]
    s2, c2 = J[5]
    e1 = CJ(c1, s1)
    e2 = CJ(c2, s2)
    se = CJ(s13 * cd, s13 * sd)
    c12c23, s12s23, c12s23, s12c23 = c12 * c23, s12 * s23, c12 * s23, s12 * c23

    def R(j):
        return CJ(j, _zero_like(j))
    V00 = R(c12 * c13)
    V01 = R(s12 * c13)
    V02 = CJ(s13 * cd, -(s13 * sd))
    V10 = -(se * c12s23 + s12c23)
    V11 = R(c12c23) - se * s12s23
    V12 = R(s23 * c13)
    V20 = R(s12s23) - se * c12c23
    V21 = -(se * s12c23 + c12s23)
    V22 = R(c23 * c13)
    return [[V00, V01, V02], [e1 * V10, e1 * V11, e1 * V12], [e2 * V20, e2 * V21, e2 * V22]]


def q3(B):
    """jets of the 18 cell probabilities, stacked: v (N,18), g (N,18,6), H (N,18,21), T (N,18,56) or None."""
    out = []
    for x in range(2):
        for a in range(3):
            for b in range(3):
                z = None
                for k in range(3):
                    wr, wi = C.OM_RE[x, a, k], C.OM_IM[x, a, k]
                    t = CJ(B[k][b].re.scale(wr) - B[k][b].im.scale(wi), B[k][b].re.scale(wi) + B[k][b].im.scale(wr))
                    z = t if z is None else z + t
                q = (z.re.sqr() + z.im.sqr()).scale(C.NINTH)
                out.append(q)

    def st(attr, axis):
        parts = [getattr(q, attr) for q in out]
        return IV(np.stack([p.lo for p in parts], axis), np.stack([p.hi for p in parts], axis))
    T = st("T", -2) if out[0].T is not None else None
    return st("v", -1), st("g", -2), st("H", -2), T


# ------------------------------------------------------------------------------------------- QP bounds
def chol(A):
    """interval Cholesky of symmetric IV A (N, n, n): (ok, L) with L lower triangular IV."""
    N, n, _ = A.lo.shape
    L = IV(np.zeros((N, n, n)))
    ok = np.ones(N, dtype=bool)
    for j in range(n):
        s = A[:, j, j]
        for k in range(j):
            s = s - L[:, j, k].sqr()
        ok &= s.lo > 0
        s = IV(np.where(ok, s.lo, 1.0), np.where(ok, s.hi, 1.0))
        d = V.isqrt(s)
        L[:, j, j] = d
        for i in range(j + 1, n):
            v = A[:, i, j]
            for k in range(j):
                v = v - L[:, i, k] * L[:, j, k]
            L[:, i, j] = v / d
    return ok, L


def full_from_packed(Hp):
    N = Hp.lo.shape[0]
    lo = np.zeros((N, NP, NP))
    hi = np.zeros((N, NP, NP))
    lo[:, TI, TJ] = Hp.lo
    hi[:, TI, TJ] = Hp.hi
    lo[:, TJ, TI] = Hp.lo
    hi[:, TJ, TI] = Hp.hi
    return IV(lo, hi)


def box_qp_float(g, H, h, sweeps=200):
    """float maximiser of g.t + t^T H t / 2 over |t_i| <= h_i for concave H (coordinate ascent); returns lam >= 0."""
    N = g.shape[0]
    t = np.zeros_like(g)
    d = np.minimum(np.einsum("nii->ni", H), -1e-300)
    for _ in range(sweeps):
        for i in range(NP):
            r = g[:, i] + np.einsum("nj,nj->n", H[:, i, :], t) - H[:, i, i] * t[:, i]
            t[:, i] = np.clip(-r / d[:, i], -h[:, i], h[:, i])
    grad = g + np.einsum("nij,nj->ni", H, t)
    act = np.abs(t) >= h * (1 - 1e-9)
    lam = np.where(act & (h > 0), np.maximum(grad / np.where(t == 0, 1.0, t), 0.0), 0.0)
    return lam


def qp_bound(g, Hp, h):
    """rigorous upper bound of max over |t_i| <= h_i of g.t + (1/2) t^T H t for all H in the packed IV Hp, g IV."""
    N = h.shape[0]
    gm = g.mag()
    Hf = full_from_packed(Hp)
    mag = np.maximum(np.abs(Hf.lo), np.abs(Hf.hi))
    off = mag.copy()
    off[:, np.arange(NP), np.arange(NP)] = 0.0
    hs = np.maximum(h, 1e-300)
    gam1 = V.up(Hp.hi[:, DIAG] + V.up(np.einsum("nij,nj->ni", off, h) / hs) * (1 + 1e-12))
    b1 = C._sep_bound(gm, gam1, h)
    Hm = Hf.mid()
    ev = np.linalg.eigvalsh(Hm)[:, -1]
    rad = np.max(np.sum(Hf.rad(), axis=2), axis=1)
    gam = ev + rad + 1e-12 + 1e-7 * np.abs(ev)
    A = IV(-Hf.hi, -Hf.lo)
    dd = np.arange(NP)
    A.lo[:, dd, dd] = V.dn(gam[:, None] - Hf.hi[:, dd, dd])
    A.hi[:, dd, dd] = V.up(gam[:, None] - Hf.lo[:, dd, dd])
    ok, _ = chol(A)
    b2 = np.where(ok, C._sep_bound(gm, np.repeat(gam[:, None], NP, axis=1), h), np.inf)
    # Lagrangian dual (only where H is negative definite in float)
    b3 = np.full(N, np.inf)
    neg = np.linalg.eigvalsh(Hm)[:, -1] < 0
    if np.any(neg):
        idx = np.nonzero(neg)[0]
        lam = box_qp_float(g.mid()[idx], Hm[idx], h[idx]) * (1 + 1e-9) + 1e-15
        Ai = IV(-Hf.hi[idx], -Hf.lo[idx])
        Ai.lo[:, dd, dd] = V.dn(lam - Hf.hi[idx][:, dd, dd])
        Ai.hi[:, dd, dd] = V.up(lam - Hf.lo[idx][:, dd, dd])
        ok3, L = chol(Ai)
        # y = L^{-1} g (forward substitution), value (1/2)|y|^2 + (1/2) lam.h^2
        gi = IV(np.where(ok3[:, None], g.lo[idx], 0.0), np.where(ok3[:, None], g.hi[idx], 0.0))
        ys = []
        for i in range(NP):
            acc = gi[:, i]
            for k in range(i):
                acc = acc - L[:, i, k] * ys[k]
            dgi = L[:, i, i]
            dgi = IV(np.where(ok3, dgi.lo, 1.0), np.where(ok3, dgi.hi, 1.0))
            ys.append(acc / dgi)
        val = None
        for y in ys:
            val = y.sqr() if val is None else val + y.sqr()
        val = val * 0.5 + V.isum(IV(lam) * IV(h[idx]).sqr(), axis=1) * 0.5
        b3[idx] = np.where(ok3, val.hi, np.inf)
    return np.minimum(np.minimum(b1, b2), b3)


# ------------------------------------------------------------------------------------------- the bound
QGOOD = 1e-4
KAPPA = 0.25


def box_bound3(lo, hi, K, M, Kint=None, return_parts=False, T=None, x0=None, chart=None):
    """rigorous upper bound of g over the boxes [lo, hi] for the kernel model K + M (y - c)
    (K float exact (N,3,3,3), or Kint an IV kernel at the centre; M exact floats (N,27,6) or None).
    With T, x0: boxes are in u-coordinates, x = x0 + T u, and M is the slope in u."""
    N = lo.shape[0]
    c, h = C.box_geometry(lo, hi)
    if chart is not None:
        qv, qg, qH, qT = q3(chart(lo, hi, True))
        cv, cg, cH, _ = q3(chart(c, c, False))
    else:
        qv, qg, qH, qT = q3(bt3(lo, hi, point=False, order3=True, T=T, x0=x0))
        if T is None:
            cv, cg, cH, _ = q3(bt3(c, c, point=True, order3=False))
        else:
            cv, cg, cH, _ = q3(bt3(c, c, point=False, order3=False, T=T, x0=x0))
    qv, qg, qH = refine(cv, cg, cH, qv, qg, qH, qT, h)
    p_c, dp = C.p_model(K if Kint is None else Kint, M)
    hb = IV(-h, h)
    p_b = p_c + V.isum(dp * hb[:, None, :], axis=2)
    pos = (p_b.lo > 0) & (p_c.lo > 0)
    good = (qv.lo >= QGOOD) & (qv.lo >= KAPPA * qv.hi) & pos & (cv.lo > 0)
    # bad cells
    qlo = np.maximum(qv.lo, 0.0)
    plo = np.where(pos, p_b.lo, 1.0)
    phi_ = np.where(pos, p_b.hi, 1.0)
    crude = np.full((N, 18), -np.inf)
    for qq in (qlo, qv.hi):
        safe = qq > 0
        Lq = V.log(IV(np.where(safe, qq, 1.0)))
        for pp in (plo, phi_):
            val = np.where(safe, (IV(np.where(safe, qq, 1.0)) * (Lq - V.log(IV(pp)))).hi, 0.0)
            crude = np.maximum(crude, val)
    crude = np.where(pos, V.up(0.5 * crude), np.inf)
    bad_sum = V.isum(IV(np.where(good, 0.0, crude)), axis=1).hi
    full = np.all(good, axis=1)
    one = IV(np.where(full, 0.0, 1.0)[:, None] * np.ones((1, 18)))
    gm = good.astype(float)

    def mask(x, extra_dims):
        m = gm.reshape(gm.shape + (1,) * extra_dims)
        return IV(x.lo * m, x.hi * m)
    # centre: value, gradient, Hessian of the good-cell sum
    qc = IV(np.where(good, cv.lo, 1.0), np.where(good, cv.hi, 1.0))
    pc = IV(np.where(good, p_c.lo, 1.0), np.where(good, p_c.hi, 1.0))
    Lc = V.log(qc) - V.log(pc)
    pi_c = dp / pc[..., None]
    a_c = cg / qc[..., None] - pi_c
    f_c = qc * Lc * 0.5
    g_c = (cg * (Lc + one)[..., None] - qc[..., None] * pi_c) * 0.5
    H_c = (cH * (Lc + one)[..., None] + qc[..., None] * (a_c[..., TI] * a_c[..., TJ])) * 0.5
    F = V.isum(mask(f_c, 0), axis=1)
    G = V.isum(mask(g_c, 1), axis=1)
    Hs = V.isum(mask(H_c, 1), axis=1)
    # box: third derivatives
    qb = IV(np.where(good, qv.lo, 1.0), np.where(good, qv.hi, 1.0))
    pb = IV(np.where(good, p_b.lo, 1.0), np.where(good, p_b.hi, 1.0))
    Lb = V.log(qb) - V.log(pb)
    pi_b = dp / pb[..., None]
    ab = qg / qb[..., None] - pi_b
    q_ = qb[..., None]
    T3 = (qT * (Lb + one)[..., None]
          + qH[..., PIJ] * ab[..., K3] + qH[..., PIK] * ab[..., J3] + qH[..., PJK] * ab[..., I3]
          - q_ * (ab[..., I3] * ab[..., J3] * ab[..., K3] + ab[..., I3] * ab[..., J3] * pi_b[..., K3]
                  + ab[..., J3] * ab[..., K3] * pi_b[..., I3] + ab[..., I3] * ab[..., K3] * pi_b[..., J3])) * 0.5
    Ts = V.isum(mask(T3, 1), axis=1)
    hh = IV(h)
    w = (hh[:, I3] * hh[:, J3] * hh[:, K3]) * IV(MULT / 6.0)
    R3 = V.isum(IV(Ts.mag()) * w, axis=1).hi
    qm = qp_bound(G, Hs, h)
    ub = (IV(F.hi) + IV(qm) + IV(R3) + IV(bad_sum)).hi
    if return_parts:
        return ub, dict(F=F, G=G, H=Hs, T=Ts, R3=R3, qm=qm, bad=bad_sum, good=good.sum(axis=1), h=h)
    return ub


# ------------------------------------------------------------------------------------------- Gram-Schmidt (LU) chart
def apply_univariate(u, f0, f1, f2, f3):
    """jet of f(u) given enclosures f0..f3 of f, f', f'', f''' over the range of u.v (IV, same shape as u.v)."""
    v = f0
    g = f1[..., None] * u.g
    H = f2[..., None] * (u.g[..., TI] * u.g[..., TJ]) + f1[..., None] * u.H
    if u.T is None:
        return Jet3(v, g, H, None)
    T = (f3[..., None] * (u.g[..., I3] * u.g[..., J3] * u.g[..., K3])
         + f2[..., None] * (u.g[..., I3] * u.H[..., PJK] + u.g[..., J3] * u.H[..., PIK] + u.g[..., K3] * u.H[..., PIJ])
         + f1[..., None] * u.T)
    return Jet3(v, g, H, T)


def inv_sqrt_jet(u):
    """jet of u^(-1/2) for a jet u with u.v > 0."""
    s = V.isqrt(u.v)
    f0 = IV(1.0) / s
    f1 = (f0 / u.v) * (-0.5)
    f2 = (f1 / u.v) * (-1.5)
    f3 = (f2 / u.v) * (-2.5)
    return apply_univariate(u, f0, f1, f2, f3)


def cconj(z):
    return CJ(z.re, -z.im)


def _const_jet(val, N, order3):
    v = IV(np.full(N, float(val)))
    return Jet3(v, _z((N, NP)), _z((N, NH)), _z((N, NT)) if order3 else None)


def _var_jet(U, k, order3):
    """jet of the k-th coordinate over the boxes U (IV (N, 6))."""
    N = U.lo.shape[0]
    g = _z((N, NP))
    g[:, k] = IV(np.ones(N))
    return Jet3(U[:, k], g, _z((N, NH)), _z((N, NT)) if order3 else None)


def gs_jets(lo, hi, Btc, order3=True):
    """jets of Bt(z) = Btc Q(z), Q(z) the Gram-Schmidt unitary of I + Z (Z strictly lower: z10, z20, z21 complex),
    coordinates (Re z10, Im z10, Re z20, Im z20, Re z21, Im z21) over the boxes [lo, hi] (a point if lo == hi).
    Btc: (re IV (3,3), im IV (3,3)) exact enclosure of the copy's basis.  Returns a 3x3 list of CJ."""
    U = IV(lo, hi)
    N = lo.shape[0]
    zr = [_var_jet(U, k, order3) for k in range(6)]
    z10, z20, z21 = CJ(zr[0], zr[1]), CJ(zr[2], zr[3]), CJ(zr[4], zr[5])
    one = _const_jet(1.0, N, order3)
    zero = _const_jet(0.0, N, order3)
    c1 = CJ(one, zero)
    c0 = CJ(zero, zero)
    v0 = [c1, z10, z20]
    n0sq = one + z10.re.sqr() + z10.im.sqr() + z20.re.sqr() + z20.im.sqr()
    r0 = inv_sqrt_jet(n0sq)
    q0 = [CJ(t.re * r0, t.im * r0) for t in v0]
    v1 = [c0, c1, z21]
    ip = cconj(q0[0]) * v1[0] + cconj(q0[1]) * v1[1] + cconj(q0[2]) * v1[2]      # <q0, v1>
    w1 = [v1[k] - ip * q0[k] for k in range(3)]
    n1sq = w1[0].re.sqr() + w1[0].im.sqr() + w1[1].re.sqr() + w1[1].im.sqr() + w1[2].re.sqr() + w1[2].im.sqr()
    r1 = inv_sqrt_jet(n1sq)
    q1 = [CJ(t.re * r1, t.im * r1) for t in w1]
    q2 = [cconj(q0[1] * q1[2] - q0[2] * q1[1]), cconj(q0[2] * q1[0] - q0[0] * q1[2]), cconj(q0[0] * q1[1] - q0[1] * q1[0])]
    Q = [q0, q1, q2]          # Q[col][row]
    bre, bim = Btc
    out = [[None] * 3 for _ in range(3)]
    for r in range(3):
        for col in range(3):
            acc = None
            for k in range(3):
                t = Q[col][k]
                term = CJ(t.re.scale(bre[r, k]) - t.im.scale(bim[r, k]), t.re.scale(bim[r, k]) + t.im.scale(bre[r, k]))
                acc = term if acc is None else acc + term
            out[r][col] = acc
    return out


def bt_values(lo, hi):
    """interval enclosures (re, im) of the 9 entries of Bt over CKM boxes [lo, hi] (values only, no jets)."""
    sc = [V.sincos(IV(lo[:, k], hi[:, k])) for k in range(NP)]
    s12, c12 = sc[0]
    s13, c13 = sc[1]
    s23, c23 = sc[2]
    sd, cd = sc[3]
    s1, c1 = sc[4]
    s2, c2 = sc[5]
    ser, sei = s13 * cd, s13 * sd                         # s13 e^{i d}
    z = IV(np.zeros(lo.shape[0]))
    V0 = [(c12 * c13, z), (s12 * c13, z), (s13 * cd, -(s13 * sd))]
    V1 = [(-(c12 * s23 * ser) - s12 * c23, -(c12 * s23 * sei)), (c12 * c23 - s12 * s23 * ser, -(s12 * s23 * sei)),
          (s23 * c13, z)]
    V2 = [(s12 * s23 - c12 * c23 * ser, -(c12 * c23 * sei)), (-(c12 * s23) - s12 * c23 * ser, -(s12 * c23 * sei)),
          (c23 * c13, z)]

    def rot(e_re, e_im, v):
        return (v[0] * e_re - v[1] * e_im, v[0] * e_im + v[1] * e_re)
    return [V0, [rot(c1, s1, v) for v in V1], [rot(c2, s2, v) for v in V2]]


def z_of_box(lo, hi, Btc):
    """enclosure of the chart coordinates z(x) = L(Btc^H Bt(x)) - I over CKM boxes [lo, hi] (IV (N, 6)), and a flag
    that the LU pivots are bounded away from 0 (else the enclosure is invalid)."""
    B = bt_values(lo, hi)
    bre, bim = Btc
    N = lo.shape[0]
    W = [[None] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            re = None
            im = None
            for k in range(3):
                # conj(Btc[k, i]) * Bt[k, j]
                a_re, a_im = bre[k, i], -bim[k, i]
                b_re, b_im = B[k][j]
                tr = b_re * a_re - b_im * a_im
                ti = b_re * a_im + b_im * a_re
                re = tr if re is None else re + tr
                im = ti if im is None else im + ti
            W[i][j] = (re, im)

    def cdiv(a, b):
        den = b[0].sqr() + b[1].sqr()
        ok = den.lo > 0
        den = IV(np.where(ok, den.lo, 1.0), np.where(ok, den.hi, 1.0))
        re = (a[0] * b[0] + a[1] * b[1]) / den
        im = (a[1] * b[0] - a[0] * b[1]) / den
        return (re, im), ok

    def cmul(a, b):
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    def csub(a, b):
        return (a[0] - b[0], a[1] - b[1])
    l10, ok1 = cdiv(W[1][0], W[0][0])
    l20, ok2 = cdiv(W[2][0], W[0][0])
    u11 = csub(W[1][1], cmul(l10, W[0][1]))
    l21, ok3 = cdiv(csub(W[2][1], cmul(l20, W[0][1])), u11)
    Z = IV(np.stack([l10[0].lo, l10[1].lo, l20[0].lo, l20[1].lo, l21[0].lo, l21[1].lo], 1),
           np.stack([l10[0].hi, l10[1].hi, l20[0].hi, l20[1].hi, l21[0].hi, l21[1].hi], 1))
    return Z, ok1 & ok2 & ok3
