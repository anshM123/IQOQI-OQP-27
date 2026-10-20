"""Mixed third-order / amplitude box bound for  g = (1/2) sum_cells q log(q/p)  (Theorem N: Bob's best response to
DKZ_3's Alice in the KL d=3 Nash problem).

Per cell put  f~ = (1/2)(q log(q/p) - q).  Since sum_cells q = 2 identically, g = 1 + sum_cells f~ exactly, and the
cells can be expanded independently (no '+1' terms):
  route A (amplitude):  f~(c+t) = f~(c) + grad f~(c).t + (1/2) t^T H(xi) t,
                        H(xi) in the kl3amp box enclosure (valid even where q vanishes on the box);
  route T (third order, needs q > 0 on the box):
                        f~(c+t) = f~(c) + grad f~(c).t + (1/2) t^T H(c) t + (1/6) D3 f~(xi)[t, t, t].
Every cell takes the route with the smaller estimated excess.  All centre gradients are summed before the box QP, so
their cancellation is kept:
  max_box g <= sum f(c) + QPmax(sum grad, sum_T H(c) + sum_A H_box, h) + (1/6) sum_{ijk} |sum_T D3_ijk| h_i h_j h_k.
Third derivative of f~ (p linear in y, a = q'/q - pi, pi = p'/p, L = log(q/p)):
  2 D3_ijk = q_ijk L + q_ij a_k + q_ik a_j + q_jk a_i - q [a_i a_j a_k + a_i a_j pi_k + a_j a_k pi_i + a_i a_k pi_j].
All enclosures are rigorous (nash_iv outward rounding)."""
import sys, os
import numpy as np
from mpmath import iv
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import nash_iv as V
from nash_iv import IV
import nash_core as C
import nash_core3 as T3
from nash_core3 import Jet3, CJ, I3, J3, K3, PIJ, PIK, PJK, MULT
import kl3amp as A

THIRD = V.const(iv.mpf(1) / 3)
PAIR_MULT = np.where(C.TI == C.TJ, 1.0, 2.0)          # multiplicity of a packed pair in t^T H t


def z3(B, third=True):
    """stacked jets (Jet3, arrays (N, 18, ...)) of Re z and Im z, z = (1/3) sum_k om[x,a,k] Bt[k,b]  (q = |z|^2)."""
    re, im = [], []
    for x in range(2):
        for a in range(3):
            for b in range(3):
                z = None
                for k in range(3):
                    wr, wi = C.OM_RE[x, a, k], C.OM_IM[x, a, k]
                    t = CJ(B[k][b].re.scale(wr) - B[k][b].im.scale(wi), B[k][b].re.scale(wi) + B[k][b].im.scale(wr))
                    z = t if z is None else z + t
                re.append(z.re.scale(THIRD))
                im.append(z.im.scale(THIRD))

    def stack(js):
        def st(attr, axis):
            parts = [getattr(j, attr) for j in js]
            if parts[0] is None:
                return None
            return IV(np.stack([p.lo for p in parts], axis), np.stack([p.hi for p in parts], axis))
        return Jet3(st("v", -1), st("g", -2), st("H", -2), st("T", -2))
    return stack(re), stack(im)


def _safe(x, ok, fill=1.0):
    """IV with entries replaced by fill where ok is False (ok broadcast over trailing dims)."""
    okb = ok.reshape(ok.shape + (1,) * (x.lo.ndim - ok.ndim))
    return IV(np.where(okb, x.lo, fill), np.where(okb, x.hi, fill))


def _zero_where(x, keep):
    k = keep.reshape(keep.shape + (1,) * (x.lo.ndim - keep.ndim))
    return IV(np.where(k, x.lo, 0.0), np.where(k, x.hi, 0.0))


def amp_hessian2(zr, zi, qv, p_b, dp, Lp, eps=0.5):
    """two per-cell upper-dominating packed Hessians (N, 18, 21) of f~ over the box (each times 1/2 already):
      HC:  L Q1 + L_hi Q2 + alpha alpha^T,
      HD:  L Q1 + (L_hi + 2 (1 + eps)) Q2 + (1 + 1/eps) q pi pi^T,
    where 2 Hess f~ = L q'' + alpha alpha^T,  q'' = Q1 + Q2,  Q1 = 2 Re(conj z z''),  Q2 = 2 Re(z' z'^H) (PSD),
    alpha = u - s pi,  u = q'/s = 2 Re(conj zhat z'),  s = |z|.  Both use t^T (L Q2) t <= L_hi t^T Q2 t (Q2 PSD, any
    sign of L_hi); HD also uses (u.t)^2 <= 2 t^T Q2 t (Cauchy-Schwarz) and (a + b)^2 <= (1+eps) a^2 + (1+1/eps) b^2.
    At points where z = 0 the Hessian is -infinite in the Q2 directions; t -> f~(c + tau t) is C^1 with an integrable
    second derivative, so the integral Taylor remainder is still bounded by these forms."""
    zrv, zrg, zrH = zr
    ziv, zig, ziH = zi
    q = IV(np.maximum(qv.lo, 0.0), qv.hi)
    s = A.ssqrt(q)
    qpos = q.lo > 0
    Lq = V.log(IV(np.where(qpos, q.lo, 1.0), np.where(qpos, q.hi, 1.0)))
    L_hi = np.where(qpos, (Lq - Lp).hi, (V.log(IV(np.maximum(q.hi, 1e-300))) - Lp).hi)
    L_hi = np.where((q.hi > 0) & np.isfinite(L_hi), L_hi, 0.0)
    sL = A.slog_s2(s) - s * Lp
    zabs1 = A.ssqrt(zrg.sqr() + zig.sqr()).hi
    zabs2 = A.ssqrt(zrH.sqr() + ziH.sqr()).hi
    # L Q1
    Q1 = (zrv[..., None] * zrH + ziv[..., None] * ziH) * 2.0
    A_mag = V.up(2.0 * V.up(sL.mag()[..., None] * zabs2))
    TA = IV(-A_mag, A_mag)
    if np.any(qpos):
        Lfull = IV(np.where(qpos, (Lq - Lp).lo, -1.0), np.where(qpos, (Lq - Lp).hi, 1.0))
        A_dir = Lfull[..., None] * Q1
        lo_ = np.where(qpos[..., None], np.maximum(TA.lo, A_dir.lo), TA.lo)
        hi_ = np.where(qpos[..., None], np.minimum(TA.hi, A_dir.hi), TA.hi)
        TA = IV(np.minimum(lo_, hi_), np.maximum(lo_, hi_))
    Q2 = (zrg[..., C.TI] * zrg[..., C.TJ] + zig[..., C.TI] * zig[..., C.TJ]) * 2.0
    pi_b = dp / p_b[..., None]
    # variant C
    a_amp = IV(-2.0 * zabs1, 2.0 * zabs1) - s[..., None] * pi_b
    if np.any(qpos):
        qq = IV(np.where(qpos, q.lo, 1.0), np.where(qpos, q.hi, 1.0))
        qg = (zrv[..., None] * zrg + ziv[..., None] * zig) * 2.0
        a_dir = A.ssqrt(qq)[..., None] * (qg / qq[..., None] - pi_b)
        lo_ = np.where(qpos[..., None], np.maximum(a_amp.lo, a_dir.lo), a_amp.lo)
        hi_ = np.where(qpos[..., None], np.minimum(a_amp.hi, a_dir.hi), a_amp.hi)
        alpha = IV(np.minimum(lo_, hi_), np.maximum(lo_, hi_))
    else:
        alpha = a_amp
    HC = (TA + Q2 * IV(L_hi)[..., None] + alpha[..., C.TI] * alpha[..., C.TJ]) * 0.5
    # variant D
    cD = IV(L_hi) + IV(2.0 * (1.0 + eps))
    HD = (TA + Q2 * cD[..., None] + (q[..., None] * (pi_b[..., C.TI] * pi_b[..., C.TJ])) * (1.0 + 1.0 / eps)) * 0.5
    return HC, HD


def _phi3(v):
    """IV enclosure of phi3(v) = v^2 log(v)/2 - 3 v^2/4 at the float points v >= 0 (phi3(0) = 0)."""
    pos = v > 0
    vv = IV(np.where(pos, v, 1.0))
    val = vv.sqr() * (V.log(vv) * 0.5 - 0.75)
    return IV(np.where(pos, val.lo, 0.0), np.where(pos, val.hi, 0.0))


def secant_m(sc, shi, logpc, Lc, K=16):
    """upper bound m (float array) with  A(z) <= A(z_c) + grad A(z_c).(z - z_c) + (m/2)|z - z_c|^2  for all |z| <= shi,
    where A(z) = (1/2)(|z|^2 log(|z|^2/p_c) - |z|^2) on C = R^2 and |z_c| = sc.
    A is radial, A = a(|z|) with a''(s) = log(s^2/p_c) + 2 increasing in s.  For fixed |z| the secant ratio
    2 [A(z) - A(z_c) - grad A(z_c).(z - z_c)] / |z - z_c|^2 is monotone in the component of z along z_c, so its sup over
    the disc is attained on the line through 0 and z_c:  m = sup_{x in [-shi, shi]} ratio(x),
        ratio(x) = int_0^1 2 (1 - tau) a''(sc + tau (x - sc)) dtau = 2 - log p_c + 4 I(x) / (sc - x)^2,
        I(x) = int_x^sc (u - x) log|u| du = C0 + kappa x + phi3(|x|),  C0 = sc^2 log(sc)/2 - sc^2/4,
        kappa = sc (1 - log sc) > 0,  phi3(v) = v^2 log(v)/2 - 3 v^2/4 (decreasing on [0, e]).
    x in (sc, shi]: ratio increasing in x, so ratio(shi) (or the curvature a''(shi), whichever is smaller);
    x in [0, sc]: ratio <= a''(sc) = Lc + 2;  x in [-shi, 0]: K subintervals in interval arithmetic."""
    sc2 = sc.sqr()
    lsc = V.log(sc)
    C0 = sc2 * (lsc * 0.5 - 0.25)
    kap = sc * (IV(1.0) - lsc)
    base = IV(2.0) - logpc
    # outward
    xo = shi
    curv = (V.log(IV(np.maximum(xo, 1e-300))) * 2.0 + base).hi
    dgap = xo - sc.hi
    okd = dgap > 1e-12 * np.maximum(xo, 1e-300)
    xs = IV(np.where(okd, xo, 1.0))
    scs = IV(np.where(okd, sc.lo, 0.5), np.where(okd, sc.hi, 0.5))
    d = xs - scs
    d2 = IV(np.maximum(d.lo, 0.0) ** 2, d.hi ** 2)
    d2 = IV(V.dn(np.where(okd, d2.lo, 1.0)), V.up(np.where(okd, d2.hi, 1.0)))
    I_o = C0 + kap * xs + _phi3(np.where(okd, xo, 1.0))
    r_o = (base + (I_o * 4.0) / d2).hi
    m = np.where(okd, np.minimum(r_o, curv), curv)
    m = np.maximum(m, (Lc + 2.0).hi)
    # through zero
    for j in range(K):
        x1 = -V.up(shi * (1.0 - j / K))
        x2 = -V.dn(shi * (1.0 - (j + 1) / K))
        X = IV(x1, np.minimum(x2, 0.0))
        I_n = C0 + kap * X + IV(_phi3(-x1).lo, _phi3(-np.minimum(x2, 0.0)).hi)
        dn_ = IV(sc.lo, sc.hi) - X                        # >= sc.lo > 0
        dd2 = dn_.sqr()
        r_n = (base + (I_n * 4.0) / dd2).hi
        m = np.maximum(m, r_n)
    return m


def route_z(zr, zi, zrc, zic, qv, qg, qH, sc, shi, Lc, pcs, pbs, dp):
    """per-cell packed matrices H (N, 18, 21) with  f~(c+t) <= f~(c) + grad f~(c).t + (1/2) t^T H t  on the box
    (route Z; needs only q(c) > 0 and p > 0):  f~ = A_c(z) - (1/2) q l,  l = log(p/p_c),
      H = Lc (zr_c Zr'' + zi_c Zi'') + (m/2) Q2 - (1/2)(q'' l + q' pi^T + pi q'^T - q pi pi^T),
    with m = secant_m (A_c(z) <= A_c(z_c) + Lc z_c.dz + (m/2)|dz|^2 on the disc |z| <= shi), |dz|^2 <= t^T (Q2/2) t
    (mean value per component), zr(c+t) = zr_c + zr_c'.t + (1/2) t^T Zr''(xi) t, and the box enclosures of the rest."""
    zrv, zrg, zrH = zr
    ziv, zig, ziH = zi
    m = secant_m(sc, shi, V.log(pcs), Lc)
    Q2 = (zrg[..., C.TI] * zrg[..., C.TJ] + zig[..., C.TI] * zig[..., C.TJ]) * 2.0
    T1 = (zrc[..., None] * zrH + zic[..., None] * ziH) * Lc[..., None]
    T2 = Q2 * IV(m * 0.5)[..., None]
    ell = V.log(pbs) - V.log(pcs)
    pi_b = dp / pbs[..., None]
    T3_ = (qH * ell[..., None] + qg[..., C.TI] * pi_b[..., C.TJ] + pi_b[..., C.TI] * qg[..., C.TJ]
           - qv[..., None] * (pi_b[..., C.TI] * pi_b[..., C.TJ])) * 0.5
    return T1 + T2 - T3_, m


def gersh_proxy(Hm, h):
    """heuristic size of max_{|t| <= h} (1/2) t^T H t for interval packed H (..., 21): diagonal upper ends plus
    off-diagonal magnitudes."""
    hh = h[:, None, :] if Hm.lo.ndim == 3 else h
    diag = np.isin(np.arange(len(C.TI)), C.DIAG)
    up = np.where(diag, Hm.hi, np.maximum(np.abs(Hm.lo), np.abs(Hm.hi)) * 2.0)
    return 0.5 * np.sum(up * hh[..., C.TI] * hh[..., C.TJ], axis=-1)


def box_bound_mix(lo, hi, K, M, force=None, diag=False):
    """rigorous upper bound of g over the boxes [lo, hi] for the kernel model K + M (y - c).
    force: None (choose per cell), 'A' (all cells amplitude route) or 'T' (third order wherever q > 0 on the box).
    Returns (ub, info)."""
    N = lo.shape[0]
    c, h = C.box_geometry(lo, hi)
    hb = IV(-h, h)
    # amplitude jets: box (third order) and centre (second order), mean-value refined
    zr_b, zi_b = z3(T3.bt3(lo, hi, point=False, order3=True))
    zr_c, zi_c = z3(T3.bt3(c, c, point=True, order3=False))
    zrv, zrg, zrH = T3.refine(zr_c.v, zr_c.g, zr_c.H, zr_b.v, zr_b.g, zr_b.H, zr_b.T, h)
    ziv, zig, ziH = T3.refine(zi_c.v, zi_c.g, zi_c.H, zi_b.v, zi_b.g, zi_b.H, zi_b.T, h)
    zr = Jet3(zrv, zrg, zrH, zr_b.T)
    zi = Jet3(ziv, zig, ziH, zi_b.T)
    # q jets: box from the refined amplitudes, refined again from the centre jets of q
    qb = zr.sqr() + zi.sqr()
    qc = Jet3(zr_c.v, zr_c.g, zr_c.H, None).sqr() + Jet3(zi_c.v, zi_c.g, zi_c.H, None).sqr()
    qv, qg, qH = T3.refine(qc.v, qc.g, qc.H, qb.v, qb.g, qb.H, qb.T, h)
    qT = qb.T
    # kernel model
    p_c, dp = C.p_model(K, M)
    p_b = p_c + V.isum(dp * hb[:, None, :], axis=2)
    ok = np.all(p_b.lo > 0, axis=1) & np.all(qc.v.lo > 0, axis=1)
    ub = np.full(N, np.inf)
    if not np.any(ok):
        return ub, dict(ok=ok, h=h)
    okc = np.repeat(ok[:, None], 18, axis=1)
    pbs = _safe(p_b, okc)
    pcs = _safe(p_c, okc)
    qcs = _safe(qc.v, okc)
    # centre value, gradient, Hessian of f~ per cell (value reported as f = (1/2) q L; the sums agree)
    Lc = V.log(qcs) - V.log(pcs)
    pi_c = dp / pcs[..., None]
    a_c = qc.g / qcs[..., None] - pi_c
    f_c = (qcs * Lc) * 0.5
    g_c = (qc.g * Lc[..., None] - qcs[..., None] * pi_c) * 0.5
    H_c = (qc.H * Lc[..., None] + qcs[..., None] * (a_c[..., C.TI] * a_c[..., C.TJ])) * 0.5
    # route A: amplitude box Hessian per cell
    Lp = V.log(pbs)
    sc = A.ssqrt(qcs)
    shi = A.ssqrt(IV(np.maximum(qv.lo, 0.0), qv.hi)).hi
    H_A, mZ = route_z((zrv, zrg, zrH), (ziv, zig, ziH), _safe(zr_c.v, okc), _safe(zi_c.v, okc), IV(np.maximum(qv.lo, 0.0), qv.hi),
                      qg, qH, sc, shi, Lc, pcs, pbs, dp)
    pA = gersh_proxy(H_A, h)
    useD = np.zeros_like(okc)
    # route T: box third derivative per cell (only where q > 0 on the box)
    canT = okc & (qv.lo > 0)
    qbs = _safe(qv, canT)
    Lb = V.log(qbs) - Lp
    pi_b = dp / pbs[..., None]
    ab = _safe(qg, canT) / qbs[..., None] - pi_b
    qH_ = _safe(qH, canT)
    q_ = qbs[..., None]
    D3 = (_safe(qT, canT) * Lb[..., None]
          + qH_[..., PIJ] * ab[..., K3] + qH_[..., PIK] * ab[..., J3] + qH_[..., PJK] * ab[..., I3]
          - q_ * (ab[..., I3] * ab[..., J3] * ab[..., K3] + ab[..., I3] * ab[..., J3] * pi_b[..., K3]
                  + ab[..., J3] * ab[..., K3] * pi_b[..., I3] + ab[..., I3] * ab[..., K3] * pi_b[..., J3])) * 0.5
    hh = IV(h)
    w3 = V.up((hh[:, I3] * hh[:, J3] * hh[:, K3]).hi * (MULT / 6.0))                    # (N, 56)
    w2 = V.up((hh[:, C.TI] * hh[:, C.TJ]).hi * (PAIR_MULT * 0.5))                      # (N, 21)
    exT = np.einsum("ncm,nm->nc", D3.mag(), w3)                                         # (N, 18)
    exT = np.where(canT & np.isfinite(exT), exT, np.inf) + gersh_proxy(H_c, h)
    exA = np.where(np.isfinite(pA), pA, np.inf)
    if force == "A":
        useT = np.zeros_like(canT)
    elif force == "T":
        useT = canT & np.isfinite(exT)
    else:
        useT = canT & (exT < exA)
    useA = ~useT
    F = V.isum(f_c, axis=1)
    G = V.isum(g_c, axis=1)
    Hs = V.isum(_zero_where(H_c, useT), axis=1) + V.isum(_zero_where(H_A, useA), axis=1)
    Ts = V.isum(_zero_where(D3, useT), axis=1)
    R3 = V.isum(IV(Ts.mag()) * IV(w3), axis=1).hi
    qm = T3.qp_bound(G, Hs, h)
    tot = (IV(F.hi) + IV(qm) + IV(R3)).hi
    ub = np.where(ok, tot, np.inf)
    info = dict(ok=ok, g=G, H=Hs, F=F, R3=R3, qm=qm, nT=useT.sum(axis=1), nD=(useD & useA).sum(axis=1), h=h)
    if diag:
        info["qm_ideal"] = T3.qp_bound(G, V.isum(H_c, axis=1), h)
    return ub, info
