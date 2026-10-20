"""Tracking bound for  Phi(A*, B(y); mu*) <= g_K(y) = (1/2) sum_cells q log(q/p)  on CKM boxes (Theorem N).

Kernel model K(y) = K0 + R (q(y) - q_c):  K0 an exact stochastic kernel with exact zeros on a face Z;  R exact floats
with zero rows on Z and exact zero b-sums (so every K(y) has row sums exactly 1).  Then p(y) = P K(y) = p0 + Lam dq(y)
with Lam = P R, i.e. p is affine in q(y), and g_K(y) = G(q(y)) for the convex function G(q) = (1/2) sum q log(q/p(q)).
Exact identity (Bregman divergence of G; per cell the Bregman divergence of q log(q/p) is d(q, r0 p)):
    g_K(y) = F + w.dq(y) + (1/2) sum_c d(q_c(y), r0_c p_c(y)),      d(a, b) = a log(a/b) - a + b >= 0,
F = g_K(c), r0 = q_c/p0, w = grad G(q_c):  w_k = (1/2)(log r0_k + 1) - (1/2) sum_c r0_c Lam_ck,
and q_c(y) - r0_c p_c(y) = (E dq)_c with E = I - diag(r0) Lam.  Bounds used:
    w.dq(y) = Gr.t + (1/2) t^T (sum_k w_k q_k''(xi_k)) t,   Gr = sum_k w_k q_k'(c)                       (Taylor),
    d(a, b) <= kappa (a - b)^2,   kappa = min(1/b_lo, 1/(2 min(a_lo, b_lo)))       (h(u) = u log u - u + 1 <= ...),
    (E dq)_c = e_c.t + eps_c,  e_c = (E q'(c))_c,  |eps_c| <= (1/2) sum_ij |(E q''(box))_c,ij| h_i h_j,
    (e.t + eps)^2 <= (1 + eta)(e.t)^2 + (1 + 1/eta) eps^2.
So  max_box g_K <= F + QPmax(Gr, sum_k w_k q_k''(box) + sum_c kappa_c (1 + eta_c) e_c e_c^T, h)
                    + (1/2) sum_c kappa_c (1 + 1/eta_c) eps_c^2.
Valid on a box when K(y) >= 0 there (then K(y) is a local model and Phi <= g_K): checked entrywise by
    K0_e - sum_i |(R q'(c))_e,i| h_i - (1/2) sum_ij |(R q''(box))_e,ij| h_i h_j >= 0.
The face, K0 and R only affect tightness; they are built in floats (EM on the face, weighted least squares)."""
import sys, os
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import nash_iv as V
from nash_iv import IV
import nash_core as C
import nash_core3 as T3
import kl3mix as X

NP = 6
PAIR_MULT = np.where(C.TI == C.TJ, 1.0, 2.0)

# P: K (27, index a0*9 + a1*3 + b) -> p (18, index x*9 + a*3 + b);  float and interval versions
P_F = np.zeros((18, 27))
_Plo = np.zeros((18, 27))
_Phi = np.zeros((18, 27))
for _a0 in range(3):
    for _a1 in range(3):
        for _b in range(3):
            _k = _a0 * 9 + _a1 * 3 + _b
            for _c in (_a0 * 3 + _b, 9 + _a1 * 3 + _b):
                P_F[_c, _k] += C.MU_F[_a0, _a1]
                _Plo[_c, _k] += C.MU.lo[_a0, _a1]
                _Phi[_c, _k] += C.MU.hi[_a0, _a1]
P_IV = IV(_Plo, _Phi)          # each entry is a single mu (one term), so no rounding in the sum
# projector onto W = {dq : zero row and column sums for each x}
_Wb = []
for _x in range(2):
    for _i in range(2):
        for _j in range(2):
            v = np.zeros((2, 3, 3))
            v[_x, _i, _j] = 1; v[_x, _i, 2] = -1; v[_x, 2, _j] = -1; v[_x, 2, 2] = 1
            _Wb.append(v.reshape(18))
_Wq, _ = np.linalg.qr(np.array(_Wb).T)
PI_W = _Wq @ _Wq.T


# shifts by vectors orthogonal to W: dq(y) has zero row and column sums in each x-block, so for any reals alpha
# (indexed by (x, a)) and beta (indexed by (x, b)), sum_k (w_k + alpha_{x(k),a(k)} + beta_{x(k),b(k)}) dq_k = w.dq exactly.
_XA = np.array([x * 3 + a for x in range(2) for a in range(3) for b in range(3)])
_XB = np.array([x * 3 + b for x in range(2) for a in range(3) for b in range(3)])


def dc_coeffs(wmid):
    """double-centering coefficients (alpha, beta), each (..., 6), for float weights wmid (..., 18)."""
    w = wmid.reshape(wmid.shape[:-1] + (2, 3, 3))
    r = w.mean(axis=-1)
    cm = w.mean(axis=-2)
    g = w.mean(axis=(-1, -2))
    alpha = -r + g[..., None]
    beta = -cm
    sh = wmid.shape[:-1] + (6,)
    return alpha.reshape(sh), beta.reshape(sh)


def shifted(wiv, last_axis_cells=True):
    """IV weights (..., 18) shifted by their (float) double centering; the shift is exact in the sense above."""
    a, b = dc_coeffs(wiv.mid())
    return wiv + IV(a[..., _XA]) + IV(b[..., _XB])


def safe_face(K, face):
    """un-face, for every cell (x, a, b) whose three feeding kernel entries are all on the face, the largest of them,
    so that p0 = P K0 > 0 in every cell (otherwise the bound is infinite; audit 2026-10-19, item 4)."""
    face = face.copy()
    N = K.shape[0]
    r = np.arange(N)
    for x in range(2):
        for a in range(3):
            for b in range(3):
                if x == 0:
                    ent = K[:, a, :, b]                  # a0 = a, a1 = 0..2
                    fe = face[:, a, :, b]
                else:
                    ent = K[:, :, a, b]                  # a1 = a, a0 = 0..2
                    fe = face[:, :, a, b]
                allf = np.all(fe, axis=1)
                if np.any(allf):
                    j = np.argmax(ent, axis=1)
                    idx = np.nonzero(allf)[0]
                    if x == 0:
                        face[idx, a, j[idx], b] = False
                    else:
                        face[idx, j[idx], a, b] = False
    return face


def em_face(q, K=None, face=None, iters=400):
    """EM for the kernel on the face (entries in face stay 0).  q (N, 18) floats."""
    N = q.shape[0]
    q4 = q.reshape(N, 2, 3, 3)
    if K is None:
        K = np.full((N, 3, 3, 3), 1.0 / 3)
    if face is not None:
        K = np.where(face, 0.0, K)
        K = K / K.sum(axis=3, keepdims=True)
    return C.em_kernel(q4, iters=iters, K=K)


def exact_kernel(K, face):
    """dyadic kernel (grid 2^-52) with exact zeros on face, every other entry >= KFLOOR, b-sums exactly 1."""
    Kc = np.where(face, 0.0, np.maximum(np.round(K / C.DY) * C.DY, C.KFLOOR))
    ref = np.argmax(Kc, axis=-1)
    others = Kc.sum(axis=-1) - np.take_along_axis(Kc, ref[..., None], -1)[..., 0]
    np.put_along_axis(Kc, ref[..., None], (1.0 - others)[..., None], -1)
    assert np.all(Kc.sum(axis=-1) == 1.0) and np.all(Kc[face] == 0.0) and np.all(Kc >= 0)
    return Kc, ref


AGRID = 2.0 ** -30


def tracking_matrix(qc, K0, face, ref, wfloor=1e-6, beta=1e-3, wK=None, freeze=None, rho=1e6):
    """R (N, 27, 18) exact floats: zero rows on the face and at nothing else forced; zero b-sums exactly.
    Directions: +1 at (row, b), -1 at (row, ref_row) for free b != ref; coefficients A = weighted least squares
    argmin sum_c (1/q_c) ((I - P D A) delta)_c^2 on W, rounded to the grid 2^-30."""
    N = qc.shape[0]
    D = np.zeros((N, 27, 18))
    mask = np.zeros((N, 18), dtype=bool)
    rows = np.arange(9)
    for r in range(9):
        a0, a1 = divmod(r, 3)
        for k in range(2):
            # the k-th non-reference b of row r
            bsel = np.where(ref[:, a0, a1] <= k, k + 1, k)            # b values != ref in increasing order
            free = ~face[np.arange(N), a0, a1, bsel]
            j = r * 2 + k
            mask[:, j] = free
            D[np.arange(N), r * 3 + bsel, j] = np.where(free, 1.0, 0.0)
            D[np.arange(N), r * 3 + ref[:, a0, a1], j] = np.where(free, -1.0, 0.0)
    PD = np.einsum("ck,nkj->ncj", P_F, D)
    w = 1.0 / np.maximum(qc, wfloor)
    if freeze is not None:
        # cells whose q may vanish on the box are not tracked: their p is held (penalty rho on its motion)
        w = np.where(freeze, 0.0, w)
    M = np.einsum("ncj,nc,nck->njk", PD, w, PD)
    if freeze is not None:
        M = M + rho * np.einsum("ncj,nc,nck->njk", PD, freeze.astype(float), PD)
    # Fisher-type regularisation of the kernel motion: beta sum_e (D A delta)_e^2 / K0_e
    if wK is None:
        wK = beta / np.maximum(K0.reshape(N, 27), 1e-300)
    M = M + np.einsum("nej,ne,nek->njk", D, np.minimum(wK, 1e300), D)
    rhs = np.einsum("ncj,nc,cd->njd", PD, w, PI_W)
    A = np.einsum("njk,nkd->njd", np.linalg.pinv(M, rcond=1e-12, hermitian=True), rhs)
    A = np.where(mask[:, :, None], A, 0.0)
    A = np.clip(np.round(A / AGRID) * AGRID, -2.0 ** 20, 2.0 ** 20)
    R = np.einsum("nej,njd->ned", D, A)                                # sums of <= 2 grid numbers: exact
    return R


def _matvec_iv(Mf, x):
    """float matrices Mf (N, a, b) times IV x (N, b, ...) -> IV (N, a, ...), rigorous (float entries exact)."""
    extra = x.lo.ndim - 2
    Mpos = np.maximum(Mf, 0.0)
    Mneg = np.minimum(Mf, 0.0)
    sub = "nab,nb...->na..."
    lo = np.einsum(sub, Mpos, x.lo) + np.einsum(sub, Mneg, x.hi)
    hi = np.einsum(sub, Mpos, x.hi) + np.einsum(sub, Mneg, x.lo)
    # rounding of the sums: bound by gamma_n * sum |M| |x| (n = b terms)
    n = Mf.shape[2]
    ax = np.maximum(np.abs(x.lo), np.abs(x.hi))
    err = np.einsum(sub, np.abs(Mf), ax) * (n * 2.0 ** -52) * 1.01 + 1e-300
    return IV(V.dn(lo - err), V.up(hi + err))


def jets(lo, hi, order3=True):
    """centre q value/gradient (tight), box q value/gradient/Hessian (refined)."""
    c, h = C.box_geometry(lo, hi)
    zr_b, zi_b = X.z3(T3.bt3(lo, hi, point=False, order3=order3))
    zr_c, zi_c = X.z3(T3.bt3(c, c, point=True, order3=False))
    zrv, zrg, zrH = T3.refine(zr_c.v, zr_c.g, zr_c.H, zr_b.v, zr_b.g, zr_b.H, zr_b.T, h)
    ziv, zig, ziH = T3.refine(zi_c.v, zi_c.g, zi_c.H, zi_b.v, zi_b.g, zi_b.H, zi_b.T, h)
    qb = T3.Jet3(zrv, zrg, zrH, zr_b.T).sqr() + T3.Jet3(ziv, zig, ziH, zi_b.T).sqr()
    qc = T3.Jet3(zr_c.v, zr_c.g, zr_c.H, None).sqr() + T3.Jet3(zi_c.v, zi_c.g, zi_c.H, None).sqr()
    qv, qg, qH = T3.refine(qc.v, qc.g, qc.H, qb.v, qb.g, qb.H, qb.T, h)
    return c, h, qc, (qv, qg, qH)


def build_model(qcf, face_tol=1e-3, rounds=2, em_iters=400):
    """float construction of the face, K0 and R for the centre distributions qcf (N, 18)."""
    N = qcf.shape[0]
    K = em_face(qcf, iters=em_iters)
    face = K < face_tol
    K = em_face(qcf, K=K, face=face, iters=em_iters)
    K0, ref = exact_kernel(K, face)
    R = tracking_matrix(qcf, K0, face, ref)
    return K0, face, ref, R


def kernel_low(R, K0, qcg, qH, h):
    """rigorous lower bounds (N, 27) of K(y) = K0 + R (q(y) - q_c) over the boxes, and the motion sizes."""
    N = R.shape[0]
    Rq1 = _matvec_iv(R, qcg)                                        # (N, 27, 6)
    Rq2 = _matvec_iv(R, qH)                                         # (N, 27, 21)
    ra, rb = dc_coeffs(R)                                            # shifts of the rows of R orthogonal to W
    Rsh = IV(R) + IV(ra[..., _XA]) + IV(rb[..., _XB])                # IV (N, 27, 18)
    Rq2s = V.isum(Rsh[:, :, :, None] * qH[:, None, :, :], axis=2)   # (N, 27, 21)
    w2 = V.up(h[:, C.TI] * h[:, C.TJ] * PAIR_MULT * 0.5)
    lin = np.einsum("nei,ni->ne", Rq1.mag(), h)
    quad = np.minimum(np.einsum("nep,np->ne", Rq2.mag(), w2), np.einsum("nep,np->ne", Rq2s.mag(), w2))
    move = V.up(V.up(lin * (1 + 1e-12)) + quad * (1 + 1e-12))
    return K0.reshape(N, 27) - move, move


def box_bound_track(lo, hi, model=None, eta_min=1e-3, order3=True, return_info=False, beta0=1e-3, rounds=6):
    N = lo.shape[0]
    c, h, qc, (qv, qg, qH) = jets(lo, hi, order3=order3)
    qcf = qc.v.mid()
    if model is None:
        K = em_face(qcf, iters=400)
        face = safe_face(K, K < 1e-3)
        K = em_face(qcf, K=K, face=face, iters=400)
        K0, ref = exact_kernel(K, face)
        wK = beta0 / np.maximum(K0.reshape(N, 27), 1e-300)
        fr = face.reshape(N, 27)
        for it in range(rounds):
            R = tracking_matrix(qcf, K0, face, ref, wK=wK)
            Klow, move = kernel_low(R, K0, qc.g, qH, h)
            viol = (Klow < 0) & ~fr
            if not np.any(viol):
                break
            ratio = move / np.maximum(K0.reshape(N, 27), 1e-300)
            wK = np.where(viol, wK * np.maximum(4.0, 2.0 * ratio ** 2), wK)
        model = (K0, face, ref, R)
    K0, face, ref, R = model
    # ---- validity: K(y) >= 0 on the box
    Klow, _ = kernel_low(R, K0, qc.g, qH, h)
    w2 = V.up(h[:, C.TI] * h[:, C.TJ] * PAIR_MULT * 0.5)
    valid = np.all((Klow >= 0) | face.reshape(N, 27), axis=1)
    # ---- the bound
    K0f = K0.reshape(N, 27)
    tiny = 1e-300
    p0 = IV(V.dn(np.einsum("ck,nk->nc", _Plo, K0f) * (1 - 64 * 2.0 ** -52) - tiny),
            V.up(np.einsum("ck,nk->nc", _Phi, K0f) * (1 + 64 * 2.0 ** -52) + tiny))     # K0 >= 0, mu > 0
    okp = np.all(p0.lo > 0, axis=1) & np.all(qc.v.lo > 0, axis=1)
    okc = np.repeat(okp[:, None], 18, axis=1)
    p0s = X._safe(p0, okc)
    qcs = X._safe(qc.v, okc)
    # Lam = P R with mu intervals: P entries are single mu values (lo/hi), R exact floats
    Lam_lo = np.einsum("ck,nkd->ncd", _Plo, np.maximum(R, 0)) + np.einsum("ck,nkd->ncd", _Phi, np.minimum(R, 0))
    Lam_hi = np.einsum("ck,nkd->ncd", _Phi, np.maximum(R, 0)) + np.einsum("ck,nkd->ncd", _Plo, np.minimum(R, 0))
    errL = np.einsum("ck,nkd->ncd", _Phi, np.abs(R)) * (27 * 2.0 ** -52) * 1.01 + 1e-300
    Lam = IV(V.dn(Lam_lo - errL), V.up(Lam_hi + errL))
    r0 = qcs / p0s
    Lr0 = V.log(r0)
    F = V.isum(qcs * Lr0, axis=1) * 0.5
    # w_k = (1/2)(log r0_k + 1) - (1/2) sum_c r0_c Lam_ck
    sLam = V.isum(r0[:, :, None] * Lam, axis=1)                      # (N, 18) over c
    wv = (Lr0 + 1.0 - sLam) * 0.5
    Gr = V.isum(wv[:, :, None] * qc.g, axis=1)                        # (N, 6)
    Hw0 = V.isum(wv[:, :, None] * qH, axis=1)                         # (N, 21)
    wvs = shifted(wv)
    Hw1 = V.isum(wvs[:, :, None] * qH, axis=1)
    pick = X.gersh_proxy(Hw1, h) < X.gersh_proxy(Hw0, h)
    Hw = IV(np.where(pick[:, None], Hw1.lo, Hw0.lo), np.where(pick[:, None], Hw1.hi, Hw0.hi))
    # E = I - diag(r0) Lam
    E = -(r0[:, :, None] * Lam)
    eye = np.eye(18)[None]
    E = E + IV(np.broadcast_to(eye, E.lo.shape).copy())          # outward-rounded (audit item 2)
    e = V.isum(E[:, :, :, None] * qc.g[:, None, :, :], axis=2)        # (N, 18, 6)
    Eq2 = V.isum(E[:, :, :, None] * qH[:, None, :, :], axis=2)        # (N, 18, 21)
    Es = shifted(E)
    Eq2s = V.isum(Es[:, :, :, None] * qH[:, None, :, :], axis=2)
    eps = np.minimum(np.einsum("ncp,np->nc", Eq2.mag(), w2), np.einsum("ncp,np->nc", Eq2s.mag(), w2)) * (1 + 1e-12)
    # p over the box and kappa
    dp_box = V.isum(Lam[:, :, :, None] * qg[:, None, :, :], axis=2)  # (N, 18, 6): Lam q'(xi)
    p_box = p0s + V.isum(dp_box * IV(-h, h)[:, None, :], axis=2)
    m_lo = (r0 * p_box).lo
    q_lo = qv.lo
    good_m = m_lo > 0
    mlo_s = np.where(good_m, m_lo, 1.0)
    k1 = V.up(1.0 / mlo_s)
    mn = np.minimum(q_lo, mlo_s)
    k2 = np.where(mn > 0, V.up(0.5 / np.where(mn > 0, mn, 1.0)), np.inf)
    kappa = np.where(good_m, np.minimum(k1, k2), np.inf)
    abar = np.einsum("nci,ni->nc", e.mag(), h)
    eta = np.maximum(np.where(abar > 0, eps / np.where(abar > 0, abar, 1.0), 1.0), eta_min)
    coefq = V.up(kappa * (1.0 + eta) * (1 + 1e-12))
    ee = e[..., C.TI] * e[..., C.TJ]                                   # (N, 18, 21)
    finite = np.all(np.isfinite(coefq), axis=1) & okp
    coefq = np.where(np.isfinite(coefq), coefq, 0.0)
    Hq = Hw + V.isum(ee * IV(coefq)[..., None], axis=1)
    kc = np.where(np.isfinite(kappa), kappa * (1.0 + 1.0 / eta), 0.0)
    const = V.isum(IV(V.up(kc)) * IV(eps).sqr(), axis=1) * 0.5
    qm = T3.qp_bound(Gr, Hq, h)
    ub = (IV(F.hi) + IV(qm) + IV(np.where(np.isfinite(const.hi), const.hi, np.inf))).hi
    ub = np.where(valid & finite, ub, np.inf)
    if return_info:
        return ub, dict(valid=valid, F=F, qm=qm, const=const.hi, Klow=Klow, face=face, h=h, Gr=Gr, Hq=Hq, finite=finite)
    return ub
