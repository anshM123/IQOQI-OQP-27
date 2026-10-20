"""numba port of the rigorous part of track.box_bound_track (the model K0, face, R is built in floats by track.py).

Same mathematics and the same choices as track.py (see TRACK_METHOD.md), with two differences:
  * validity is tested as K0_e >= move_e (exact float comparison of K0 with an upper bound of the motion), not as
    float(K0_e - move_e) >= 0, which could round a tiny negative difference up to 0;
  * squares of intervals use isqr (tighter for intervals containing 0; still rigorous).
Interval conventions as in nbjets.py."""
import os, sys
import numpy as np
import numba as nb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nbjets as NJ
from nbjets import up, dn, iadd, isub, imul, isqr, idiv_pos, log_point, OG, OH, NJ as NJET, TI, TJ, DIAG, PIJF
sys.path.insert(0, NJ.ROOT)
import track as TR
import nash_core as C

PLO = np.ascontiguousarray(TR._Plo)            # (18, 27) mu lower ends
PHI_ = np.ascontiguousarray(TR._Phi)           # (18, 27) mu upper ends
XA = np.ascontiguousarray(TR._XA.astype(np.int64))
XB = np.ascontiguousarray(TR._XB.astype(np.int64))
PMULT = np.where(C.TI == C.TJ, 1.0, 2.0)
S0LO = float(C.S0.lo)
INF = np.inf


@nb.njit
def mag(l, h):
    return max(abs(l), abs(h))


@nb.njit
def isum_add(sl, sh, xl, xh):
    return iadd(sl, sh, xl, xh)


@nb.njit
def dc_coeffs_vec(w, alpha, beta):
    """double centering coefficients of a float vector w (18): alpha (6) indexed x*3+a, beta (6) indexed x*3+b."""
    for x in range(2):
        g = 0.0
        for a in range(3):
            for b in range(3):
                g += w[9 * x + 3 * a + b]
        g /= 9.0
        for a in range(3):
            r = 0.0
            for b in range(3):
                r += w[9 * x + 3 * a + b]
            alpha[3 * x + a] = -r / 3.0 + g
        for b in range(3):
            cm = 0.0
            for a in range(3):
                cm += w[9 * x + 3 * a + b]
            beta[3 * x + b] = -cm / 3.0


@nb.njit
def lin_comb(wl, wh, Jl, Jh, off, n, outl, outh):
    """out[j] = sum_k w_k J[k, off + j] for j < n (intervals); J: (18, NJET) lo/hi."""
    for j in range(n):
        sl, sh = 0.0, 0.0
        for k in range(18):
            x, y = imul(wl[k], wh[k], Jl[k, off + j], Jh[k, off + j])
            sl, sh = iadd(sl, sh, x, y)
        outl[j] = sl
        outh[j] = sh


@nb.njit
def gersh_proxy(Hl, Hh, h):
    s = 0.0
    for p in range(21):
        i = TI[p]
        j = TJ[p]
        if i == j:
            u = Hh[p]
        else:
            u = max(abs(Hl[p]), abs(Hh[p])) * 2.0
        s += u * h[i] * h[j]
    return 0.5 * s


@nb.njit
def sep_bound(gm, gam, h):
    """sum_i max_{|t| <= h_i} (gm_i t + gam_i t^2/2), rigorous upper bound (nash_core._sep_bound)."""
    tot_l, tot_h = 0.0, 0.0
    for i in range(6):
        a_l, a_h = imul(gm[i], gm[i], h[i], h[i])
        hh_l, hh_h = isqr(h[i], h[i])
        b_l, b_h = imul(gam[i], gam[i], hh_l, hh_h)
        b_l, b_h = dn(0.5 * b_l), up(0.5 * b_h)
        e_l, e_h = iadd(a_l, a_h, b_l, b_h)
        v = e_h
        if gam[i] < 0 and gm[i] <= -gam[i] * h[i] * (1 - 1e-12):
            g2l, g2h = isqr(gm[i], gm[i])
            q_l, q_h = idiv_pos(g2l, g2h, -2.0 * gam[i], -2.0 * gam[i])
            v = max(v, q_h)
        tot_l, tot_h = iadd(tot_l, tot_h, v, v)
    return tot_h


@nb.njit
def chol_ok(Al, Ah):
    """interval Cholesky of the symmetric interval matrix A (6x6); returns (ok, Ll, Lh)."""
    n = 6
    Ll = np.zeros((n, n))
    Lh = np.zeros((n, n))
    for j in range(n):
        sl, sh = Al[j, j], Ah[j, j]
        for k in range(j):
            x, y = isqr(Ll[j, k], Lh[j, k])
            sl, sh = isub(sl, sh, x, y)
        if not (sl > 0):
            return False, Ll, Lh
        dl, dh = max(dn(np.sqrt(sl)), 0.0), up(np.sqrt(sh))
        Ll[j, j], Lh[j, j] = dl, dh
        for i in range(j + 1, n):
            vl, vh = Al[i, j], Ah[i, j]
            for k in range(j):
                x, y = imul(Ll[i, k], Lh[i, k], Ll[j, k], Lh[j, k])
                vl, vh = isub(vl, vh, x, y)
            Ll[i, j], Lh[i, j] = idiv_pos(vl, vh, dl, dh)
    return True, Ll, Lh


@nb.njit
def box_qp_float(g, H, h, sweeps=200):
    t = np.zeros(6)
    d = np.empty(6)
    for i in range(6):
        d[i] = min(H[i, i], -1e-300)
    for _ in range(sweeps):
        for i in range(6):
            r = g[i]
            for j in range(6):
                if j != i:
                    r += H[i, j] * t[j]
            t[i] = min(max(-r / d[i], -h[i]), h[i])
    lam = np.zeros(6)
    for i in range(6):
        gr = g[i]
        for j in range(6):
            gr += H[i, j] * t[j]
        act = abs(t[i]) >= h[i] * (1 - 1e-9)
        if act and h[i] > 0 and t[i] != 0:
            lam[i] = max(gr / t[i], 0.0)
    return lam


@nb.njit
def qp_bound(Gl, Gh, Hl, Hh, h):
    """rigorous upper bound of max_{|t_i| <= h_i} g.t + t^T H t / 2 over g in [Gl, Gh], H in [Hl, Hh] (packed);
    port of nash_core3.qp_bound (Gershgorin, certified isotropic eigenvalue, Lagrangian dual)."""
    gm = np.empty(6)
    for i in range(6):
        gm[i] = mag(Gl[i], Gh[i])
    Fl = np.empty((6, 6))
    Fh = np.empty((6, 6))
    for p in range(21):
        i = TI[p]
        j = TJ[p]
        Fl[i, j] = Hl[p]
        Fh[i, j] = Hh[p]
        Fl[j, i] = Hl[p]
        Fh[j, i] = Hh[p]
    # (1) scaled Gershgorin
    gam1 = np.empty(6)
    for i in range(6):
        s = 0.0
        for j in range(6):
            if j != i:
                s = up(s + max(abs(Fl[i, j]), abs(Fh[i, j])) * h[j])
        hs = max(h[i], 1e-300)
        gam1[i] = up(Fh[i, i] + up(up(s / hs) * (1 + 1e-12)))
    b1 = sep_bound(gm, gam1, h)
    # (2) isotropic certified eigenvalue
    Hm = np.empty((6, 6))
    for i in range(6):
        for j in range(6):
            Hm[i, j] = 0.5 * (Fl[i, j] + Fh[i, j])
    ev = np.linalg.eigvalsh(Hm)
    lmax = ev[5]
    rad = 0.0
    for i in range(6):
        s = 0.0
        for j in range(6):
            s += 0.5 * (Fh[i, j] - Fl[i, j])
        rad = max(rad, s)
    gam = lmax + rad + 1e-12 + 1e-7 * abs(lmax)
    Al = np.empty((6, 6))
    Ah = np.empty((6, 6))
    for i in range(6):
        for j in range(6):
            Al[i, j] = -Fh[i, j]
            Ah[i, j] = -Fl[i, j]
        Al[i, i] = dn(gam - Fh[i, i])
        Ah[i, i] = up(gam - Fl[i, i])
    ok, _, _ = chol_ok(Al, Ah)
    b2 = INF
    if ok:
        gv = np.empty(6)
        for i in range(6):
            gv[i] = gam
        b2 = sep_bound(gm, gv, h)
    # (3) Lagrangian dual where the mid matrix is negative definite
    b3 = INF
    if lmax < 0:
        gmid = np.empty(6)
        for i in range(6):
            gmid[i] = 0.5 * (Gl[i] + Gh[i])
        lam = box_qp_float(gmid, Hm, h)
        for i in range(6):
            lam[i] = lam[i] * (1 + 1e-9) + 1e-15
        for i in range(6):
            for j in range(6):
                Al[i, j] = -Fh[i, j]
                Ah[i, j] = -Fl[i, j]
            Al[i, i] = dn(lam[i] - Fh[i, i])
            Ah[i, i] = up(lam[i] - Fl[i, i])
        ok3, Ll, Lh = chol_ok(Al, Ah)
        if ok3:
            yl = np.empty(6)
            yh = np.empty(6)
            for i in range(6):
                al_, ah_ = Gl[i], Gh[i]
                for k in range(i):
                    x, y = imul(Ll[i, k], Lh[i, k], yl[k], yh[k])
                    al_, ah_ = isub(al_, ah_, x, y)
                yl[i], yh[i] = idiv_pos(al_, ah_, Ll[i, i], Lh[i, i])
            vl, vh = 0.0, 0.0
            for i in range(6):
                x, y = isqr(yl[i], yh[i])
                vl, vh = iadd(vl, vh, x, y)
            wl, wh = 0.0, 0.0
            for i in range(6):
                hh_l, hh_h = isqr(h[i], h[i])
                x, y = imul(lam[i], lam[i], hh_l, hh_h)
                wl, wh = iadd(wl, wh, x, y)
            tl, th = iadd(vl, vh, wl, wh)
            b3 = up(0.5 * th)
    return min(min(b1, b2), b3)


@nb.njit
def track_bound_one(h, QCl, QCh, QBl, QBh, K0, face, R, eta_min, score):
    """ub (or inf) and validity for one box; QC centre jets, QB refined box jets (18, NJET); K0 (27), face (27 bool),
    R (27, 18) exact floats."""
    w2 = np.empty(21)
    for p in range(21):
        w2[p] = up(up(h[TI[p]] * h[TJ[p]]) * PMULT[p] * 0.5)
    # ---------------- validity
    valid = True
    a6 = np.empty(6)
    b6 = np.empty(6)
    rrow = np.empty(18)
    for e in range(27):
        if face[e]:
            continue
        lin = 0.0
        for i in range(6):
            sl, sh = 0.0, 0.0
            for k in range(18):
                x, y = imul(R[e, k], R[e, k], QCl[k, OG + i], QCh[k, OG + i])
                sl, sh = iadd(sl, sh, x, y)
            lin = up(lin + up(mag(sl, sh) * h[i]))
        # second-order term, raw rows and rows shifted orthogonally to W
        for k in range(18):
            rrow[k] = R[e, k]
        dc_coeffs_vec(rrow, a6, b6)
        q1, q2 = 0.0, 0.0
        for p in range(21):
            sl, sh = 0.0, 0.0
            tl, th = 0.0, 0.0
            for k in range(18):
                x, y = imul(R[e, k], R[e, k], QBl[k, OH + p], QBh[k, OH + p])
                sl, sh = iadd(sl, sh, x, y)
                rl, rh = iadd(R[e, k], R[e, k], a6[XA[k]], a6[XA[k]])
                rl, rh = iadd(rl, rh, b6[XB[k]], b6[XB[k]])
                x, y = imul(rl, rh, QBl[k, OH + p], QBh[k, OH + p])
                tl, th = iadd(tl, th, x, y)
            q1 = up(q1 + up(mag(sl, sh) * w2[p]))
            q2 = up(q2 + up(mag(tl, th) * w2[p]))
        move = up(up(lin * (1 + 1e-12)) + up(min(q1, q2) * (1 + 1e-12)))
        if not (K0[e] >= move):
            valid = False
            break
    for i in range(6):
        score[i] = h[i]
    if not valid:
        return INF, False
    # ---------------- p0 = P K0 (mu intervals), Lam = P R
    p0l = np.empty(18)
    p0h = np.empty(18)
    for c in range(18):
        sl, sh = 0.0, 0.0
        for e in range(27):
            if PHI_[c, e] != 0.0:
                x, y = imul(PLO[c, e], PHI_[c, e], K0[e], K0[e])
                sl, sh = iadd(sl, sh, x, y)
        p0l[c], p0h[c] = sl, sh
        if not (p0l[c] > 0 and QCl[c, 0] > 0):
            return INF, True
    Laml = np.empty((18, 18))
    Lamh = np.empty((18, 18))
    for c in range(18):
        for d in range(18):
            sl, sh = 0.0, 0.0
            for e in range(27):
                if PHI_[c, e] != 0.0 and R[e, d] != 0.0:
                    x, y = imul(PLO[c, e], PHI_[c, e], R[e, d], R[e, d])
                    sl, sh = iadd(sl, sh, x, y)
            Laml[c, d], Lamh[c, d] = sl, sh
    # ---------------- r0, F, w
    r0l = np.empty(18)
    r0h = np.empty(18)
    Lrl = np.empty(18)
    Lrh = np.empty(18)
    Fl, Fh = 0.0, 0.0
    for c in range(18):
        r0l[c], r0h[c] = idiv_pos(QCl[c, 0], QCh[c, 0], p0l[c], p0h[c])
        a, _ = log_point(r0l[c])
        _, b = log_point(r0h[c])
        Lrl[c], Lrh[c] = a, b
        x, y = imul(QCl[c, 0], QCh[c, 0], a, b)
        Fl, Fh = iadd(Fl, Fh, x, y)
    Fh = up(0.5 * Fh)
    wl = np.empty(18)
    wh = np.empty(18)
    for k in range(18):
        sl, sh = 0.0, 0.0
        for c in range(18):
            x, y = imul(r0l[c], r0h[c], Laml[c, k], Lamh[c, k])
            sl, sh = iadd(sl, sh, x, y)
        tl, th = iadd(Lrl[k], Lrh[k], 1.0, 1.0)
        tl, th = isub(tl, th, sl, sh)
        wl[k], wh[k] = dn(0.5 * tl), up(0.5 * th)
    Grl = np.empty(6)
    Grh = np.empty(6)
    lin_comb(wl, wh, QCl, QCh, OG, 6, Grl, Grh)
    Hw0l = np.empty(21)
    Hw0h = np.empty(21)
    lin_comb(wl, wh, QBl, QBh, OH, 21, Hw0l, Hw0h)
    wmid = np.empty(18)
    for k in range(18):
        wmid[k] = 0.5 * (wl[k] + wh[k])
    dc_coeffs_vec(wmid, a6, b6)
    wsl = np.empty(18)
    wsh = np.empty(18)
    for k in range(18):
        x, y = iadd(wl[k], wh[k], a6[XA[k]], a6[XA[k]])
        wsl[k], wsh[k] = iadd(x, y, b6[XB[k]], b6[XB[k]])
    Hw1l = np.empty(21)
    Hw1h = np.empty(21)
    lin_comb(wsl, wsh, QBl, QBh, OH, 21, Hw1l, Hw1h)
    if gersh_proxy(Hw1l, Hw1h, h) < gersh_proxy(Hw0l, Hw0h, h):
        Hql = Hw1l.copy()
        Hqh = Hw1h.copy()
    else:
        Hql = Hw0l.copy()
        Hqh = Hw0h.copy()
    # ---------------- E = I - diag(r0) Lam; e = E q'(c); eps; p over the box; kappa
    El = np.empty(18)
    Eh = np.empty(18)
    emid = np.empty(18)
    el6 = np.empty(6)
    eh6 = np.empty(6)
    constv = 0.0
    for c in range(18):
        for k in range(18):
            x, y = imul(r0l[c], r0h[c], Laml[c, k], Lamh[c, k])
            one = 1.0 if k == c else 0.0
            El[k], Eh[k] = isub(one, one, x, y)
            emid[k] = 0.5 * (El[k] + Eh[k])
        lin_comb(El, Eh, QCl, QCh, OG, 6, el6, eh6)
        dc_coeffs_vec(emid, a6, b6)
        e1, e2 = 0.0, 0.0
        for p in range(21):
            sl, sh = 0.0, 0.0
            tl, th = 0.0, 0.0
            for k in range(18):
                x, y = imul(El[k], Eh[k], QBl[k, OH + p], QBh[k, OH + p])
                sl, sh = iadd(sl, sh, x, y)
                rl, rh = iadd(El[k], Eh[k], a6[XA[k]], a6[XA[k]])
                rl, rh = iadd(rl, rh, b6[XB[k]], b6[XB[k]])
                x, y = imul(rl, rh, QBl[k, OH + p], QBh[k, OH + p])
                tl, th = iadd(tl, th, x, y)
            e1 = up(e1 + up(mag(sl, sh) * w2[p]))
            e2 = up(e2 + up(mag(tl, th) * w2[p]))
        eps = up(min(e1, e2) * (1 + 1e-12))
        # p over the box: p0_c + sum_i (sum_k Lam_ck qg_box_k,i) [-h_i, h_i]
        pl, ph = p0l[c], p0h[c]
        for i in range(6):
            sl, sh = 0.0, 0.0
            for k in range(18):
                x, y = imul(Laml[c, k], Lamh[c, k], QBl[k, OG + i], QBh[k, OG + i])
                sl, sh = iadd(sl, sh, x, y)
            x, y = imul(sl, sh, -h[i], h[i])
            pl, ph = iadd(pl, ph, x, y)
        ml, _ = imul(r0l[c], r0h[c], pl, ph)
        if not (ml > 0):
            return INF, True
        qlo = QBl[c, 0]
        k1 = up(1.0 / ml)
        mn = min(qlo, ml)
        kappa = k1
        if mn > 0:
            kappa = min(k1, up(0.5 / mn))
        abar = 0.0
        for i in range(6):
            abar = up(abar + up(mag(el6[i], eh6[i]) * h[i]))
        eta = 1.0
        if abar > 0:
            eta = eps / abar
        eta = max(eta, eta_min)
        coefq = up(up(kappa * up(1.0 + eta)) * (1 + 1e-12))
        for p in range(21):
            if TI[p] == TJ[p]:
                x, y = isqr(el6[TI[p]], eh6[TI[p]])
            else:
                x, y = imul(el6[TI[p]], eh6[TI[p]], el6[TJ[p]], eh6[TJ[p]])
            x, y = imul(x, y, coefq, coefq)
            Hql[p], Hqh[p] = iadd(Hql[p], Hqh[p], x, y)
        kc = up(kappa * up(1.0 + up(1.0 / eta)))
        e2l, e2h = isqr(eps, eps)
        constv = up(constv + up(kc * e2h))
    constv = up(0.5 * constv)
    # finiteness guards (audit 2): any non-finite ingredient -> no certificate
    for p in range(21):
        if not (np.isfinite(Hql[p]) and np.isfinite(Hqh[p])):
            return INF, True
    for i in range(6):
        if not (np.isfinite(Grl[i]) and np.isfinite(Grh[i])):
            return INF, True
    if not (np.isfinite(Fh) and np.isfinite(constv)):
        return INF, True
    # split score: h_i (|G_i| + sum_j |H_ij| h_j) (float heuristic only)
    for i in range(6):
        sc = mag(Grl[i], Grh[i])
        for j in range(6):
            if i <= j:
                p = PIJF[i, j]
            else:
                p = PIJF[j, i]
            sc += mag(Hql[p], Hqh[p]) * h[j]
        score[i] = h[i] * sc
    qm = qp_bound(Grl, Grh, Hql, Hqh, h)
    ub = up(up(Fh + qm) + constv)
    if not (ub == ub):
        return INF, True
    return ub, True


@nb.njit(parallel=True)
def track_bound_batch(H, QCl, QCh, QBl, QBh, K0, face, R, eta_min):
    N = H.shape[0]
    ub = np.empty(N)
    valid = np.empty(N, dtype=np.bool_)
    score = np.empty((N, 6))
    for n in nb.prange(N):
        u, v = track_bound_one(H[n], QCl[n], QCh[n], QBl[n], QBh[n], K0[n], face[n], R[n], eta_min, score[n])
        ub[n] = u
        valid[n] = v
    return ub, valid, score


def build_model(qcf, beta0=1.0, qcg=None, h=None, freeze_fac=2.0):
    """float model (K0, face, R) from the centre distributions qcf (N, 18): EM on the face, exact kernel, weighted
    least-squares tracking with Fisher regularisation beta0 / K0 (one solve), as track.box_bound_track(rounds=1)."""
    N = qcf.shape[0]
    K = TR.em_face(qcf, iters=400)
    face = TR.safe_face(K, K < 1e-3)
    K = TR.em_face(qcf, K=K, face=face, iters=400)
    K0, ref = TR.exact_kernel(K, face)
    wK = beta0 / np.maximum(K0.reshape(N, 27), 1e-300)
    freeze = None
    if qcg is not None and h is not None:
        # a cell is frozen when its first-order variation over the box can reach its centre value
        freeze = qcf < freeze_fac * np.einsum("nci,ni->nc", np.abs(qcg), h)
    R = TR.tracking_matrix(qcf, K0, face, ref, wK=wK, freeze=freeze)
    return K0.reshape(N, 27), face.reshape(N, 27), R


def box_bound(lo, hi, beta0=1.0, eta_min=1e-3):
    """rigorous upper bound of Phi over each box (inf where the bound does not apply)."""
    c, h, QCl, QCh, QBl, QBh = NJ.q_jets_batch(np.ascontiguousarray(lo), np.ascontiguousarray(hi))
    qcf = 0.5 * (QCl[:, :, 0] + QCh[:, :, 0])
    qcg = 0.5 * (QCl[:, :, 1:7] + QCh[:, :, 1:7])
    K0, face, R = build_model(qcf, beta0, qcg, h)
    ub, valid, score = track_bound_batch(h, QCl, QCh, QBl, QBh, np.ascontiguousarray(K0), np.ascontiguousarray(face),
                                         np.ascontiguousarray(R), eta_min)
    return ub, valid, score
