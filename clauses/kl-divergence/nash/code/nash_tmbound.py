"""Box bounds with Taylor models (nash_tm): CKM chart (global) and Gram-Schmidt chart (local, at a copy).

For a box x = c + h*s, the cell probabilities q (TM) give, for the good cells, the TM of
  G(s) = (1/2) sum_cells q (log q - log p),  p = p_c + sum_i dp_i h_i s_i  (kernel model, exact),
and  max over the box of G <= G0 + QPmax(g, H) + sum_{deg 3} |c| + K  (QP over |s_i| <= 1).
Bad cells (q not bounded away from 0 on the box) use the vertex bound of the jointly convex q log(q/p).
"""
import numpy as np

import nash_iv as V
from nash_iv import IV
import nash_core as C
import nash_core3 as T3
import nash_tm as T

NINTH = C.NINTH


def ckm_bt(c, h):
    """TMs (CTM 3x3) of Bt over boxes c +- h in CKM coordinates (c float (N,6) or IV)."""
    sc = [T.sincos_coord(k, c[:, k], h[:, k]) for k in range(6)]
    s12, c12 = sc[0]
    s13, c13 = sc[1]
    s23, c23 = sc[2]
    sd, cd = sc[3]
    s1, c1 = sc[4]
    s2, c2 = sc[5]
    N = h.shape[0]
    zero = T.const(IV(0.0), N)
    e1 = T.CTM(c1, s1)
    e2 = T.CTM(c2, s2)
    se = T.CTM(s13 * cd, s13 * sd)
    c12c23, s12s23, c12s23, s12c23 = c12 * c23, s12 * s23, c12 * s23, s12 * c23

    def R(t):
        return T.CTM(t, zero)
    V00 = R(c12 * c13)
    V01 = R(s12 * c13)
    V02 = T.CTM(s13 * cd, -(s13 * sd))
    V10 = -(se * c12s23 + s12c23)
    V11 = R(c12c23) - se * s12s23
    V12 = R(s23 * c13)
    V20 = R(s12s23) - se * c12c23
    V21 = -(se * s12c23 + c12s23)
    V22 = R(c23 * c13)
    return [[V00, V01, V02], [e1 * V10, e1 * V11, e1 * V12], [e2 * V20, e2 * V21, e2 * V22]]


def gs_bt(c, h, Btc):
    """TMs of Bt(z) = Btc Q(z) (Gram-Schmidt chart) over boxes z = c + h*s."""
    N = h.shape[0]
    zc = [T.coord(k, c[:, k], h[:, k]) for k in range(6)]
    z10, z20, z21 = T.CTM(zc[0], zc[1]), T.CTM(zc[2], zc[3]), T.CTM(zc[4], zc[5])
    one = T.const(IV(1.0), N)
    zero = T.const(IV(0.0), N)
    c1 = T.CTM(one, zero)
    c0 = T.CTM(zero, zero)
    v0 = [c1, z10, z20]
    n0sq = one + z10.abs2() + z20.abs2()
    r0 = T.inv_sqrt(n0sq)
    q0 = [T.CTM(t.re * r0, t.im * r0) for t in v0]
    v1 = [c0, c1, z21]
    ip = q0[0].conj() * v1[0] + q0[1].conj() * v1[1] + q0[2].conj() * v1[2]
    w1 = [v1[k] - ip * q0[k] for k in range(3)]
    n1sq = w1[0].abs2() + w1[1].abs2() + w1[2].abs2()
    r1 = T.inv_sqrt(n1sq)
    q1 = [T.CTM(t.re * r1, t.im * r1) for t in w1]
    q2 = [(q0[1] * q1[2] - q0[2] * q1[1]).conj(), (q0[2] * q1[0] - q0[0] * q1[2]).conj(),
          (q0[0] * q1[1] - q0[1] * q1[0]).conj()]
    Q = [q0, q1, q2]
    bre, bim = Btc
    out = [[None] * 3 for _ in range(3)]
    for r in range(3):
        for col in range(3):
            acc = None
            for k in range(3):
                term = Q[col][k].scale(bre[r, k], bim[r, k])
                acc = term if acc is None else acc + term
            out[r][col] = acc
    return out


def q_tms(B):
    """list of 18 TMs of q_x(a, b) = |sum_k om[x,a,k] Bt[k,b]|^2 / 9, cell index 9x + 3a + b."""
    out = []
    for x in range(2):
        for a in range(3):
            for b in range(3):
                z = None
                for k in range(3):
                    t = B[k][b].scale(C.OM_RE[x, a, k], C.OM_IM[x, a, k])
                    z = t if z is None else z + t
                out.append(z.abs2().scale(NINTH))
    return out


QGOOD = 1e-4


def _masked(tm, good, c0fill):
    m = good[:, None]
    out = T.TM(IV(np.where(m, tm.c.lo, 0.0), np.where(m, tm.c.hi, 0.0)), np.where(good, tm.K, 0.0))
    out.c[:, 0] = IV(np.where(good, tm.c[:, 0].lo, c0fill), np.where(good, tm.c[:, 0].hi, c0fill))
    return out


def g_bound(qs, p_c, dp, h, return_parts=False):
    """upper bound over the boxes for g = (1/2) sum q log(q/p); qs: 18 TMs; p_c IV (N, 18); dp IV (N, 18, 6) (slopes in
    the box coordinates); h (N, 6).  Returns ub (N,) [and parts: G0, g, H (s-units), cubic sum, K]."""
    N = h.shape[0]
    hb = IV(h)
    G = None
    bad_sum = np.zeros(N)
    good_all = np.ones(N, dtype=bool)
    for cell in range(18):
        q = qs[cell]
        qr = q.range()
        pc = IV(np.zeros((N, T.NM)))
        pc[:, 0] = p_c[:, cell]
        for i in range(6):
            pc[:, T.E1[i]] = dp[:, cell, i] * hb[:, i]
        ptm = T.TM(pc, np.zeros(N))
        pr = ptm.range()
        good = (qr.lo >= QGOOD) & (pr.lo > 0)
        qlo = np.maximum(qr.lo, 0.0)
        posp = pr.lo > 0
        plo = np.where(posp, pr.lo, 1.0)
        phi_ = np.where(posp, pr.hi, 1.0)
        crude = np.full(N, -np.inf)
        for qq in (qlo, qr.hi):
            safe = qq > 0
            Lq = V.log(IV(np.where(safe, qq, 1.0)))
            for pp in (plo, phi_):
                val = np.where(safe, (IV(np.where(safe, qq, 1.0)) * (Lq - V.log(IV(pp)))).hi, 0.0)
                crude = np.maximum(crude, val)
        crude = np.where(posp, V.up(0.5 * crude), np.inf)
        bad_sum = np.where(good, bad_sum, V.up(bad_sum + crude))
        good_all &= good
        if not np.any(good):
            continue
        qg = _masked(q, good, 1.0)
        pg = _masked(ptm, good, 1.0)
        L = T.log(qg) - T.log(pg)
        f = (qg * L).scale(IV(0.5))
        m = good.astype(float)
        f = T.TM(IV(f.c.lo * m[:, None], f.c.hi * m[:, None]), f.K * m)
        G = f if G is None else G + f
    if G is None:
        return (bad_sum, None) if return_parts else bad_sum
    G0 = G.c[:, 0]
    gl = G.c[:, T.E1]
    Hp = IV(np.zeros((N, T3.NH)))
    for k, (i, j) in enumerate(zip(T3.TI, T3.TJ)):
        if i == j:
            Hp[:, k] = G.c[:, T.MIDX[tuple(2 if t == i else 0 for t in range(6))]] * 2.0
        else:
            Hp[:, k] = G.c[:, T.MIDX[tuple(1 if t in (i, j) else 0 for t in range(6))]]
    qm = T3.qp_bound(gl, Hp, np.ones((N, 6)))
    cub = V.up(np.sum(G.c.mag() * T.DEGMASK[3], axis=1) * (1 + 1e-12))
    ub = (IV(G0.hi) + IV(qm) + IV(cub) + IV(G.K) + IV(bad_sum)).hi
    if return_parts:
        return ub, dict(G0=G0, g=gl, H=Hp, cub=cub, K=G.K, bad=bad_sum, allgood=good_all)
    return ub


KAPPA2 = 0.2


def g_bound2(qs, p_c, dp, h, return_parts=False):
    """improved split:  g = (1/2) sum_cells q log q  -  (1/2) sum_cells q log p.
    The second sum is smooth (p bounded away from 0 by the kernel floor) and goes into the Taylor model for EVERY cell.
    In the first sum, cells with q bounded away from 0 (q_lo >= max(QGOOD, KAPPA2 q_hi)) go into the Taylor model; for
    the others (1/2) q log q is bounded by its maximum over the q-range, attained at an endpoint (convexity), <= 0."""
    N = h.shape[0]
    hb = IV(h)
    G = None
    ent_bad = np.zeros(N)
    good_all = np.ones(N, dtype=bool)
    for cell in range(18):
        q = qs[cell]
        qr = q.range()
        pc = IV(np.zeros((N, T.NM)))
        pc[:, 0] = p_c[:, cell]
        for i in range(6):
            pc[:, T.E1[i]] = dp[:, cell, i] * hb[:, i]
        ptm = T.TM(pc, np.zeros(N))
        pr = ptm.range()
        if np.any(pr.lo <= 0):
            raise ValueError("kernel model with p not bounded away from 0")
        lin = -(q * T.log(ptm))                          # -q log p, all cells
        good = (qr.lo >= QGOOD) & (qr.lo >= KAPPA2 * qr.hi)
        good_all &= good
        f = lin
        if np.any(good):
            qg = _masked(q, good, 1.0)
            ent = qg * T.log(qg)
            m = good.astype(float)
            ent = T.TM(IV(ent.c.lo * m[:, None], ent.c.hi * m[:, None]), ent.K * m)
            f = f + ent
        # bad cells: sup of q log q over [max(q_lo, 0), q_hi]; q log q is convex with value 0 at 0
        qlo = np.maximum(qr.lo, 0.0)
        qhi = np.minimum(qr.hi, 1.0)
        vals = []
        for qq in (qlo, qhi):
            safe = qq > 0
            v = np.where(safe, (IV(np.where(safe, qq, 1.0)) * V.log(IV(np.where(safe, qq, 1.0)))).hi, 0.0)
            vals.append(v)
        ent_sup = np.maximum(vals[0], vals[1])
        ent_bad = np.where(good, ent_bad, V.up(ent_bad + ent_sup))
        G = f if G is None else G + f
    G = G.scale(IV(0.5))
    ent_bad = V.up(0.5 * ent_bad) if np.all(ent_bad >= 0) else np.where(ent_bad >= 0, V.up(0.5 * ent_bad),
                                                                         -V.dn(-0.5 * ent_bad))
    G0 = G.c[:, 0]
    gl = G.c[:, T.E1]
    Hp = IV(np.zeros((N, T3.NH)))
    for k, (i, j) in enumerate(zip(T3.TI, T3.TJ)):
        if i == j:
            Hp[:, k] = G.c[:, T.MIDX[tuple(2 if t == i else 0 for t in range(6))]] * 2.0
        else:
            Hp[:, k] = G.c[:, T.MIDX[tuple(1 if t in (i, j) else 0 for t in range(6))]]
    qm = T3.qp_bound(gl, Hp, np.ones((N, 6)))
    cub = V.up(np.sum(G.c.mag() * T.DEGMASK[3], axis=1) * (1 + 1e-12))
    ub = (IV(G0.hi) + IV(qm) + IV(cub) + IV(G.K) + IV(ent_bad)).hi
    if return_parts:
        return ub, dict(G0=G0, g=gl, H=Hp, cub=cub, K=G.K, entbad=ent_bad, allgood=good_all)
    return ub


KAPPA3 = 0.6          # q enters log-TMs only if q_lo >= KAPPA3 q_hi (relative variation <= ~25%)
PREL = 0.25           # log p enters TMs only if the relative variation of p over the box is <= PREL


def g_bound3(qs, p_c, dp, h, return_parts=False):
    """as g_bound2, with stricter cell classification:
      (1/2) q log q : Taylor model if q_lo >= max(QGOOD, KAPPA3 q_hi); else its maximum over the q-range (<= 0);
     -(1/2) q log p : Taylor model if the relative variation of p over the box is <= PREL; else
                      -(1/2) q log p <= -(1/2) q log p_lo (q >= 0, -log decreasing), a TM linear in q."""
    N = h.shape[0]
    hb = IV(h)
    G = None
    ent_bad = np.zeros(N)
    for cell in range(18):
        q = qs[cell]
        qr = q.range()
        pc = IV(np.zeros((N, T.NM)))
        pc[:, 0] = p_c[:, cell]
        for i in range(6):
            pc[:, T.E1[i]] = dp[:, cell, i] * hb[:, i]
        ptm = T.TM(pc, np.zeros(N))
        pr = ptm.range()
        if np.any(pr.lo <= 0):
            raise ValueError("kernel model with p not bounded away from 0")
        prel = (pr.hi - pr.lo) / pr.lo
        smooth_p = prel <= PREL
        # -q log p: TM where smooth, else -q log p_lo (constant)
        logp_tm = T.log(_masked(ptm, smooth_p, 1.0))
        logp_lo = V.log(IV(pr.lo))
        c0 = IV(np.where(smooth_p, 0.0, logp_lo.lo), np.where(smooth_p, 0.0, logp_lo.lo))
        # build log p as: TM (smooth rows) or the constant log p_lo (other rows), both valid lower... see below
        m = smooth_p.astype(float)
        lp = T.TM(IV(logp_tm.c.lo * m[:, None], logp_tm.c.hi * m[:, None]), logp_tm.K * m)
        lp.c[:, 0] = IV(np.where(smooth_p, lp.c[:, 0].lo, logp_lo.lo), np.where(smooth_p, lp.c[:, 0].hi, logp_lo.lo))
        # for non-smooth rows lp is the constant log(p_lo) <= log p, so -q lp >= -q log p (q >= 0): an upper bound
        f = -(q * lp)
        good = (qr.lo >= QGOOD) & (qr.lo >= KAPPA3 * qr.hi)
        if np.any(good):
            qg = _masked(q, good, 1.0)
            ent = qg * T.log(qg)
            mg = good.astype(float)
            ent = T.TM(IV(ent.c.lo * mg[:, None], ent.c.hi * mg[:, None]), ent.K * mg)
            f = f + ent
        qlo = np.maximum(qr.lo, 0.0)
        qhi = np.minimum(qr.hi, 1.0)
        vals = []
        for qq in (qlo, qhi):
            safe = qq > 0
            v = np.where(safe, (IV(np.where(safe, qq, 1.0)) * V.log(IV(np.where(safe, qq, 1.0)))).hi, 0.0)
            vals.append(v)
        ent_sup = np.maximum(vals[0], vals[1])
        ent_bad = np.where(good, ent_bad, (IV(ent_bad) + IV(ent_sup)).hi)
        G = f if G is None else G + f
    G = G.scale(IV(0.5))
    ent_bad = (IV(ent_bad) * 0.5).hi
    G0 = G.c[:, 0]
    gl = G.c[:, T.E1]
    Hp = IV(np.zeros((N, T3.NH)))
    for k, (i, j) in enumerate(zip(T3.TI, T3.TJ)):
        if i == j:
            Hp[:, k] = G.c[:, T.MIDX[tuple(2 if t == i else 0 for t in range(6))]] * 2.0
        else:
            Hp[:, k] = G.c[:, T.MIDX[tuple(1 if t in (i, j) else 0 for t in range(6))]]
    qm = T3.qp_bound(gl, Hp, np.ones((N, 6)))
    cub = V.up(np.sum(G.c.mag() * T.DEGMASK[3], axis=1) * (1 + 1e-12))
    ub = (IV(G0.hi) + IV(qm) + IV(cub) + IV(G.K) + IV(ent_bad)).hi
    if return_parts:
        return ub, dict(G0=G0, g=gl, H=Hp, cub=cub, K=G.K, entbad=ent_bad, qm=qm)
    return ub
