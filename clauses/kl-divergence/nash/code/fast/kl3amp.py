"""Amplitude-based box bound for  g = (1/2) sum_cells q log(q/p)  (Nash problem, Bob's best response to DKZ_3's Alice).

Same certificate structure as nash_core.taylor_bound (value and gradient at the box centre, a rigorous upper bound on the
quadratic form of the Hessian over the box, Gershgorin/Cholesky box QP), but the Hessian bound is built from the
amplitude z (q = |z|^2) instead of q itself, which removes the 1/q and log q blow-ups:

  Hess[q log(q/p)] = L q'' + alpha alpha^T,   L = log(q/p) (the '+1' cancels in the sum over all cells: sum q'' = 0),
  q'' = Q1 + Q2,  Q1 = 2 Re(conj z z''),  Q2 = 2 Re(z' z'^H)  (PSD),
  alpha = (q' - (q/p) p') / sqrt(q),  q'/sqrt(q) = 2 Re(zhat z')  in  [-2|z'|, 2|z'|],
  L Q1 = (|z| L) * 2 Re(zhat z''),  |z| L = s log s^2 - s log p  (bounded as s -> 0),
  t^T (L Q2) t <= max(L_hi, 0) t^T Q2 t   (Q2 PSD), so L Q2 is replaced by max(L_hi, 0) Q2.

Every cell is treated by this Taylor bound (no crude vertex bound), provided p > 0 on the box (kernel floor) and q > 0 at
the centre.  All enclosures are rigorous (nash_iv outward rounding)."""
import sys, os
import numpy as np
from mpmath import iv
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import nash_iv as V
from nash_iv import IV
import nash_core as C

THIRD = V.const(iv.mpf(1) / 3)
TWO_OVER_E = V.const(iv.mpf(2) / iv.e)          # max of -s log s^2 on [0,1] is 2/e at s = 1/e
INV_E = V.const(1 / iv.e)


def z_jets(B):
    """real and imaginary parts of z = (1/3) sum_k om[x,a,k] Bt[k,b] for the 18 cells: each a tuple (v, g, H) of IV
    arrays with shapes (N,18), (N,18,6), (N,18,21) (H None if B has no Hessians)."""
    hess = B[0][0].re.H is not None
    outs = {"re": ([], [], []), "im": ([], [], [])}
    for x in range(2):
        for a in range(3):
            for b in range(3):
                z = None
                for k in range(3):
                    w_re, w_im = C.OM_RE[x, a, k], C.OM_IM[x, a, k]
                    t = C.CJet(B[k][b].re.scale(w_re) - B[k][b].im.scale(w_im),
                               B[k][b].re.scale(w_im) + B[k][b].im.scale(w_re))
                    z = t if z is None else z + t
                for part, J in (("re", z.re.scale(THIRD)), ("im", z.im.scale(THIRD))):
                    outs[part][0].append(J.v)
                    outs[part][1].append(J.g)
                    outs[part][2].append(J.H)
    res = {}
    for part in ("re", "im"):
        vs, gs, Hs = outs[part]
        v = IV(np.stack([t.lo for t in vs], -1), np.stack([t.hi for t in vs], -1))
        g = IV(np.stack([t.lo for t in gs], -2), np.stack([t.hi for t in gs], -2))
        H = IV(np.stack([t.lo for t in Hs], -2), np.stack([t.hi for t in Hs], -2)) if hess else None
        res[part] = (v, g, H)
    return res


def ssqrt(a):
    """sqrt of a nonnegative quantity whose enclosure may dip below 0 by rounding."""
    return V.isqrt(IV(np.maximum(a.lo, 0.0), np.maximum(a.hi, 0.0)))


def _intersect(a, b):
    lo = np.maximum(a.lo, b.lo)
    hi = np.minimum(a.hi, b.hi)
    bad = lo > hi                      # cannot happen for valid enclosures; keep a valid one
    lo = np.where(bad, a.lo, lo)
    hi = np.where(bad, a.hi, hi)
    return IV(lo, hi)


def refine_z(zb, zc, h):
    """mean-value refinement of the box enclosures of z' and z from the centre values and the box second derivatives."""
    v, g, H = zb
    cv, cg = zc
    hb = IV(-h, h)[:, None, :]
    Hj = H[:, :, C.PIJF2]                                   # (N, 18, 6, 6)
    addg = V.isum(Hj * hb[:, :, None, :], axis=3)
    g2 = _intersect(g, cg + addg)
    addv = V.isum(g2 * hb, axis=2)
    v2 = _intersect(v, cv + addv)
    return (v2, g2, H)


def slog_s2(s):
    """enclosure of phi(s) = s log(s^2) for s in the IV s (0 <= s <= 1): phi decreases on [0, 1/e], increases after,
    phi(0) = 0, min phi = -2/e."""
    lo_s = np.maximum(s.lo, 0.0)
    hi_s = np.minimum(s.hi, 1.0)
    def phi_point(x):
        safe = x > 0
        xx = IV(np.where(safe, x, 1.0))
        val = xx * (V.log(xx) * 2.0)
        return IV(np.where(safe, val.lo, 0.0), np.where(safe, val.hi, 0.0))
    a = phi_point(lo_s)
    b = phi_point(hi_s)
    hi_ = np.maximum(a.hi, b.hi)
    lo_ = np.minimum(a.lo, b.lo)
    inner = (lo_s <= INV_E.hi) & (hi_s >= INV_E.lo)
    lo_ = np.where(inner, np.minimum(lo_, -TWO_OVER_E.hi), lo_)
    return IV(lo_, hi_)


def amp_hessian(zr, zi, qv, p_b, dp, Lp, per_cell=False):
    """upper-dominating packed matrix (N, 21) for the Hessian of (1/2) sum_cells q log(q/p) over the box (all cells).
    zr, zi: box jets (v, g, H) of Re z, Im z;  qv: IV (N,18) box enclosure of q;  p_b: IV (N,18) box enclosure of p
    (p_b.lo > 0 required);  dp: IV (N,18,6) slopes of p;  Lp: IV (N,18) enclosure of log p over the box."""
    zrv, zrg, zrH = zr
    ziv, zig, ziH = zi
    N = qv.lo.shape[0]
    q = IV(np.maximum(qv.lo, 0.0), qv.hi)
    s = ssqrt(q)
    # L = log q - log p over the box (may be -inf at q = 0: only used through L_hi and the safe products below)
    qpos = q.lo > 0
    Lq = V.log(IV(np.where(qpos, q.lo, 1.0), np.where(qpos, q.hi, 1.0)))
    L_hi = np.where(qpos, (Lq - Lp).hi, (V.log(IV(np.maximum(q.hi, 1e-300))) - Lp).hi)
    L_hi = np.where(q.hi > 0, L_hi, -np.inf)
    # |z| L enclosure:  s log s^2 - s log p
    sL = slog_s2(s) - s * Lp
    # magnitudes of z' (per coordinate) and z'' (per packed pair)
    zabs1 = ssqrt(zrg.sqr() + zig.sqr()).hi                         # (N,18,6) upper bounds of |z'_i|
    zabs2 = ssqrt(zrH.sqr() + ziH.sqr()).hi                         # (N,18,21) upper bounds of |z''_ij|
    # Term A: L Q1, two enclosures, intersected
    Q1 = (zrv[..., None] * zrH + ziv[..., None] * ziH) * 2.0
    A_amp_mag = V.up(2.0 * V.up(sL.mag()[..., None] * zabs2))
    A_amp = IV(-A_amp_mag, A_amp_mag)
    if np.any(qpos):
        Lfull = IV(np.where(qpos, (Lq - Lp).lo, -1.0), np.where(qpos, (Lq - Lp).hi, 1.0))
        A_dir = Lfull[..., None] * Q1
        A = IV(np.where(qpos[..., None], np.maximum(A_amp.lo, A_dir.lo), A_amp.lo),
               np.where(qpos[..., None], np.minimum(A_amp.hi, A_dir.hi), A_amp.hi))
        A = IV(np.minimum(A.lo, A.hi), np.maximum(A.lo, A.hi))
    else:
        A = A_amp
    # Term B: max(L_hi, 0) Q2, Q2 = 2 (zr'_i zr'_j + zi'_i zi'_j)
    Q2 = (zrg[..., C.TI] * zrg[..., C.TJ] + zig[..., C.TI] * zig[..., C.TJ]) * 2.0
    lpos = np.maximum(L_hi, 0.0)
    lpos = np.where(np.isfinite(lpos), lpos, 0.0)
    B = Q2 * IV(lpos)[..., None]
    # Term C: alpha_i alpha_j
    a_amp = IV(-2.0 * zabs1, 2.0 * zabs1) - (s[..., None] * dp) / p_b[..., None]
    if np.any(qpos):
        qq = IV(np.where(qpos, q.lo, 1.0), np.where(qpos, q.hi, 1.0))
        qg = (zrv[..., None] * zrg + ziv[..., None] * zig) * 2.0         # q' = 2 Re(conj z z')
        a_dir = ssqrt(qq)[..., None] * (qg / qq[..., None] - dp / p_b[..., None])
        alpha = IV(np.where(qpos[..., None], np.maximum(a_amp.lo, a_dir.lo), a_amp.lo),
                   np.where(qpos[..., None], np.minimum(a_amp.hi, a_dir.hi), a_amp.hi))
        alpha = IV(np.minimum(alpha.lo, alpha.hi), np.maximum(alpha.lo, alpha.hi))
    else:
        alpha = a_amp
    Cm = alpha[..., C.TI] * alpha[..., C.TJ]
    Hc = (A + B + Cm) * 0.5
    if per_cell:
        return Hc
    return V.isum(Hc, axis=1)


def box_bound_amp(lo, hi, K, M):
    """rigorous upper bound of g over the boxes for the kernel model K + M (y - c); all cells via the amplitude bound.
    Returns (ub, info)."""
    c, h = C.box_geometry(lo, hi)
    Bbox = C.bt_jets(lo, hi, point=False, hess=True)
    Bc = C.bt_jets(c, c, point=True, hess=False)
    zb = z_jets(Bbox)
    zc = z_jets(Bc)
    zr = refine_z(zb["re"], (zc["re"][0], zc["re"][1]), h)
    zi = refine_z(zb["im"], (zc["im"][0], zc["im"][1]), h)
    # q box enclosure from z (and from the q jets' refinement as a cross-check is not needed)
    qv = zr[0].sqr() + zi[0].sqr()
    # centre values: q and q' from the centre amplitudes (tight point enclosures)
    qcv = zc["re"][0].sqr() + zc["im"][0].sqr()
    qcg = (zc["re"][0][..., None] * zc["re"][1] + zc["im"][0][..., None] * zc["im"][1]) * 2.0
    p_c, dp = C.p_model(K, M)
    hb = IV(-h, h)
    p_b = p_c + V.isum(dp * hb[:, None, :], axis=2)
    ok = np.all(p_b.lo > 0, axis=1) & np.all(qcv.lo > 0, axis=1)
    N = lo.shape[0]
    ub = np.full(N, np.inf)
    if not np.any(ok):
        return ub, dict(ok=ok)
    pbs = IV(np.where(ok[:, None], p_b.lo, 1.0), np.where(ok[:, None], p_b.hi, 1.0))
    pcs = IV(np.where(ok[:, None], p_c.lo, 1.0), np.where(ok[:, None], p_c.hi, 1.0))
    qcs = IV(np.where(ok[:, None], qcv.lo, 1.0), np.where(ok[:, None], qcv.hi, 1.0))
    Lp = V.log(pbs)
    Lc = V.log(qcs) - V.log(pcs)
    f_c = (qcs * Lc) * 0.5
    grad_c = (qcg * Lc[..., None] - (qcs[..., None] * dp) / pcs[..., None]) * 0.5
    f_sum = V.isum(f_c, axis=1)
    g_sum = V.isum(grad_c, axis=2 - 1)
    H_sum = amp_hessian(zr, zi, qv, pbs, dp, Lp)
    qm = C._quadmax(g_sum, H_sum, h)
    tot = (IV(f_sum.hi) + IV(qm)).hi
    ub = np.where(ok, tot, np.inf)
    return ub, dict(ok=ok, g=g_sum, H=H_sum, f=f_sum, h=h)
