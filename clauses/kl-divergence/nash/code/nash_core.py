"""Core of the rigorous branch-and-bound for  max_B Phi(A*, B; mu*) <= S0  (Bob's best response to DKZ_3's Alice).

Phi(A, B; mu) = min over kernels K(b | a0, a1) of (1/2) sum_x D(q_x || p_x),  q_x(a, b) = |<a_x | Bt e_b>|^2 / 3,
p_x(a, b) = sum over (a0, a1) with a_x = a of mu(a0, a1) K(b | a0, a1)   (Lemma R, fourier-family/THEOREM.md).
Any substochastic K gives an upper bound (complete it to a stochastic kernel: p only increases, D only decreases).

Coordinates (PDG / CKM): Bt = diag(1, e^{i f1}, e^{i f2}) V(t12, t13, t23, d), x = (t12, t13, t23, d, f1, f2).
Column phases of Bt do not change q, so this covers all bases.
Box bound: on a box with centre c and half-widths h, a kernel model K(y) = Kc + M (y - c) (M = 0 allowed), checked
>= 0 with exactly zero b-sums, gives g(y) = (1/2) sum_cells q log(q/p(y)) >= Phi(y), and
  g(c + t) <= g(c) + grad g(c).t + (1/2) t^T H t,  H in the interval enclosure of the Hessian of g over the box,
for the 'good' cells (q bounded away from 0 on the box); every other cell is bounded by the maximum of the jointly
convex function q log(q/p) over the vertices of its (q, p) rectangle.
All quantities are interval enclosures (nash_iv); the kernel model itself is exact (dyadic floats).
"""
import itertools
import numpy as np
from mpmath import iv

import nash_iv as V
from nash_iv import IV

NP = 6
TI, TJ = np.triu_indices(NP)                 # packed upper triangle, 21 entries
NH = len(TI)
PIDX = {(int(i), int(j)): k for k, (i, j) in enumerate(zip(TI, TJ))}
for (_i, _j), _k in list(PIDX.items()):
    PIDX[(_j, _i)] = _k
DIAG = np.array([PIDX[(i, i)] for i in range(NP)])

# ------------------------------------------------------------------------------------------- exact constants
iv.prec = 200
_s3 = iv.sqrt(3)
BETA_I = ((16 + 24 * _s3) - iv.sqrt(3280 - 960 * _s3)) / 54
QL_I = [2 * (2 + _s3) / 9, 2 * (2 - _s3) / 9, iv.mpf(1) / 9]
RL_I = [1 + BETA_I * (iv.mpf(1) / 2 - k) for k in range(3)]
S0_I = sum(QL_I[k] * iv.log(RL_I[k]) for k in range(3))
S0 = V.const(S0_I)                              # IV enclosure of S(DKZ_3) in nats
PSTAR_I = [QL_I[k] / RL_I[k] for k in range(3)]


def _levels():
    g = np.zeros((2, 2, 3, 3), dtype=int)
    for a in range(3):
        for b in range(3):
            g[0, 0, a, b] = (a - b) % 3
            g[1, 1, a, b] = (a - b) % 3
            g[1, 0, a, b] = (b - a) % 3
            g[0, 1, a, b] = (b - a - 1) % 3
    return g


GLEV = _levels()


def facet_weights():
    """the 30 facet strategies lam = (a0, a1, b0, b1) and their weights (mpmath intervals), Prop K3 (iv)."""
    out = {}
    for lam in itertools.product(range(3), repeat=4):
        lv = [GLEV[x, y, lam[x], lam[2 + y]] for x in range(2) for y in range(2)]   # order 00, 01, 10, 11
        if sum(lv) != 2:
            continue
        if 2 in lv:
            out[lam] = 4 * PSTAR_I[2] / 12
        else:
            ones = {i for i in range(4) if lv[i] == 1}
            adj = [{0, 1}, {1, 3}, {3, 2}, {2, 0}]
            out[lam] = PSTAR_I[1] / 12 if ones in adj else PSTAR_I[1] / 6
    return out


FACETS = facet_weights()
MU_I = [[iv.mpf(0)] * 3 for _ in range(3)]
for _lam, _w in FACETS.items():
    MU_I[_lam[0]][_lam[1]] += _w
MU = IV(np.array([[V._arb_iv(MU_I[i][j])[0] for j in range(3)] for i in range(3)]),
        np.array([[V._arb_iv(MU_I[i][j])[1] for j in range(3)] for i in range(3)]))
MU_F = MU.mid()

# Alice's DKZ vectors: <a_x | v> = 3^{-1/2} sum_k e^{-2 pi i k (a + alpha_x)/3} v_k, alpha = (1/2, 0).
# q = |<a_x|Bt e_b>|^2/3 = |sum_k om[x,a,k] Bt[k,b]|^2 / 9.
ALPHA = (iv.mpf(1) / 2, iv.mpf(0))
OM_RE = IV(np.zeros((2, 3, 3)))
OM_IM = IV(np.zeros((2, 3, 3)))
for _x in range(2):
    for _a in range(3):
        for _k in range(3):
            ang = -2 * iv.pi * _k * (_a + ALPHA[_x]) / 3
            OM_RE[_x, _a, _k] = V.const(iv.cos(ang))
            OM_IM[_x, _a, _k] = V.const(iv.sin(ang))
OM_F = OM_RE.mid() + 1j * OM_IM.mid()
NINTH = V.const(iv.mpf(1) / 9)


# ------------------------------------------------------------------------------------------- jets
class Jet:
    """value v (IV, shape S), gradient g (IV, S + (6,)), packed Hessian H (IV, S + (21,)) or None."""
    __slots__ = ("v", "g", "H")

    def __init__(self, v, g, H):
        self.v, self.g, self.H = v, g, H

    def __add__(self, o):
        return Jet(self.v + o.v, self.g + o.g, None if self.H is None else self.H + o.H)

    def __sub__(self, o):
        return Jet(self.v - o.v, self.g - o.g, None if self.H is None else self.H - o.H)

    def __neg__(self):
        return Jet(-self.v, -self.g, None if self.H is None else -self.H)

    def __mul__(self, o):
        v = self.v * o.v
        g = self.g * o.v[..., None] + self.v[..., None] * o.g
        if self.H is None:
            return Jet(v, g, None)
        H = (self.H * o.v[..., None] + self.v[..., None] * o.H
             + self.g[..., TI] * o.g[..., TJ] + self.g[..., TJ] * o.g[..., TI])
        return Jet(v, g, H)

    def scale(self, c):
        """multiply by an IV constant c (broadcastable to v)."""
        c = V.as_iv(c)
        return Jet(self.v * c, self.g * c[..., None] if c.lo.ndim else self.g * c,
                   None if self.H is None else (self.H * c[..., None] if c.lo.ndim else self.H * c))

    def sqr(self):
        v = self.v.sqr()
        g = (self.v[..., None] * self.g) * 2.0
        if self.H is None:
            return Jet(v, g, None)
        H = (self.v[..., None] * self.H) * 2.0 + (self.g[..., TI] * self.g[..., TJ]) * 2.0
        return Jet(v, g, H)


def _zeros(shape, hess):
    z = IV(np.zeros(shape))
    return z, IV(np.zeros(shape + (NP,))), (IV(np.zeros(shape + (NH,))) if hess else None)


def param_jets(k, s, c, hess):
    """jets of sin and cos of parameter k, given enclosures s, c (IV, shape (N,))."""
    N = s.lo.shape[0]
    _, gs, Hs = _zeros((N,), hess)
    _, gc, Hc = _zeros((N,), hess)
    gs[:, k] = c
    gc[:, k] = -s
    if hess:
        Hs[:, DIAG[k]] = -s
        Hc[:, DIAG[k]] = -c
    return Jet(s, gs, Hs), Jet(c, gc, Hc)


def param_jets_affine(Tk, s, c, hess):
    """jets in u of sin and cos of x_k = x0_k + T_k . u (T_k: exact float row, shape (6,))."""
    N = s.lo.shape[0]
    Tk = np.asarray(Tk, dtype=np.float64)
    gs = c[:, None] * IV(np.broadcast_to(Tk, (N, NP)).copy())
    gc = (-s)[:, None] * IV(np.broadcast_to(Tk, (N, NP)).copy())
    if hess:
        TT = IV(Tk[TI]) * IV(Tk[TJ])
        TT = IV(np.broadcast_to(TT.lo, (N, NH)).copy(), np.broadcast_to(TT.hi, (N, NH)).copy())
        Hs = (-s)[:, None] * TT
        Hc = (-c)[:, None] * TT
    else:
        Hs = Hc = None
    return Jet(s, gs, Hs), Jet(c, gc, Hc)


class CJet:
    __slots__ = ("re", "im")

    def __init__(self, re, im):
        self.re, self.im = re, im

    def __mul__(self, o):
        if isinstance(o, Jet):
            return CJet(self.re * o, self.im * o)
        return CJet(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def __add__(self, o):
        if isinstance(o, Jet):
            return CJet(self.re + o, self.im)
        return CJet(self.re + o.re, self.im + o.im)

    def __sub__(self, o):
        if isinstance(o, Jet):
            return CJet(self.re - o, self.im)
        return CJet(self.re - o.re, self.im - o.im)

    def __neg__(self):
        return CJet(-self.re, -self.im)


def _rjet_as_c(j):
    z = Jet(IV(np.zeros(j.v.shape)), IV(np.zeros(j.g.shape)), None if j.H is None else IV(np.zeros(j.H.shape)))
    return CJet(j, z)


def bt_jets(lo, hi, point=False, hess=True, T=None, x0=None):
    """jets of the 9 entries of Bt over the boxes [lo, hi] (N x 6 floats), or at the points lo if point=True.
    With T (6 x 6 exact floats) and x0 (IV, shape (6,)), the box is in u-coordinates and x = x0 + T u (jets in u).
    Returns a 3x3 list of CJet."""
    if T is None:
        if point:
            sc = [V.sincos_point(lo[:, k]) for k in range(NP)]
        else:
            sc = [V.sincos(IV(lo[:, k], hi[:, k])) for k in range(NP)]
        J = [param_jets(k, sc[k][0], sc[k][1], hess) for k in range(NP)]
    else:
        U = IV(lo, hi)
        J = []
        for k in range(NP):
            xk = V.isum(U * IV(np.broadcast_to(T[k], lo.shape).copy()), axis=1) + x0[k]
            s_, c_ = V.sincos(xk)
            J.append(param_jets_affine(T[k], s_, c_, hess))
    s12, c12 = J[0]
    s13, c13 = J[1]
    s23, c23 = J[2]
    sd, cd = J[3]
    s1, c1 = J[4]
    s2, c2 = J[5]
    ed = CJet(cd, sd)
    e1 = CJet(c1, s1)
    e2 = CJet(c2, s2)
    se = CJet(s13 * cd, s13 * sd)                       # s13 e^{i d}
    c12c23, s12s23, c12s23, s12c23 = c12 * c23, s12 * s23, c12 * s23, s12 * c23
    V00 = _rjet_as_c(c12 * c13)
    V01 = _rjet_as_c(s12 * c13)
    V02 = CJet(s13 * cd, -(s13 * sd))
    V10 = (se * c12s23 + s12c23).__neg__()
    V11 = _rjet_as_c(c12c23) - se * s12s23
    V12 = _rjet_as_c(s23 * c13)
    V20 = _rjet_as_c(s12s23) - se * c12c23
    V21 = (se * s12c23 + c12s23).__neg__()
    V22 = _rjet_as_c(c23 * c13)
    _ = ed
    return [[V00, V01, V02], [e1 * V10, e1 * V11, e1 * V12], [e2 * V20, e2 * V21, e2 * V22]]


def q_jets(B):
    """jets of q_x(a, b) = |sum_k om[x,a,k] Bt[k,b]|^2 / 9 for the 18 cells, stacked on a new last axis
    (shape (N, 18) for the value; cell index = 9 x + 3 a + b)."""
    vs, gs, Hs = [], [], []
    hess = B[0][0].re.H is not None
    for x in range(2):
        for a in range(3):
            for b in range(3):
                z = None
                for k in range(3):
                    w_re, w_im = OM_RE[x, a, k], OM_IM[x, a, k]
                    t = CJet(B[k][b].re.scale(w_re) - B[k][b].im.scale(w_im),
                             B[k][b].re.scale(w_im) + B[k][b].im.scale(w_re))
                    z = t if z is None else z + t
                q = z.re.sqr() + z.im.sqr()
                q = q.scale(NINTH)
                vs.append(q.v)
                gs.append(q.g)
                Hs.append(q.H)
    v = IV(np.stack([t.lo for t in vs], -1), np.stack([t.hi for t in vs], -1))
    g = IV(np.stack([t.lo for t in gs], -2), np.stack([t.hi for t in gs], -2))
    H = IV(np.stack([t.lo for t in Hs], -2), np.stack([t.hi for t in Hs], -2)) if hess else None
    return v, g, H


# ------------------------------------------------------------------------------------------- floats
def ckm_float(x):
    """Bt for float parameter arrays x (N, 6)."""
    t12, t13, t23, d, f1, f2 = [x[:, k] for k in range(NP)]
    s12, c12, s13, c13, s23, c23 = np.sin(t12), np.cos(t12), np.sin(t13), np.cos(t13), np.sin(t23), np.cos(t23)
    e = np.exp(1j * d)
    Vm = np.empty((x.shape[0], 3, 3), complex)
    Vm[:, 0, 0] = c12 * c13
    Vm[:, 0, 1] = s12 * c13
    Vm[:, 0, 2] = s13 / e
    Vm[:, 1, 0] = -s12 * c23 - c12 * s23 * s13 * e
    Vm[:, 1, 1] = c12 * c23 - s12 * s23 * s13 * e
    Vm[:, 1, 2] = s23 * c13
    Vm[:, 2, 0] = s12 * s23 - c12 * c23 * s13 * e
    Vm[:, 2, 1] = -c12 * s23 - s12 * c23 * s13 * e
    Vm[:, 2, 2] = c23 * c13
    Vm[:, 1, :] *= np.exp(1j * f1)[:, None]
    Vm[:, 2, :] *= np.exp(1j * f2)[:, None]
    return Vm


def q_float(Bt):
    """q (N, 2, 3, 3) for steered bases Bt (N, 3, 3)."""
    z = np.einsum("xak,nkb->nxab", OM_F, Bt)
    return np.abs(z) ** 2 / 9.0


def em_kernel(q, iters=300, K=None):
    """EM for the optimal kernel; q (N, 2, 3, 3). Returns K (N, 3, 3, 3) indexed [a0, a1, b]."""
    N = q.shape[0]
    mu = MU_F
    if K is None:
        K = np.full((N, 3, 3, 3), 1.0 / 3)
    for _ in range(iters):
        P = mu[None, :, :, None] * K
        p0 = P.sum(axis=2)                       # [n, a0, b]
        p1 = P.sum(axis=1)                       # [n, a1, b]
        r0 = q[:, 0] / np.maximum(p0, 1e-300)
        r1 = q[:, 1] / np.maximum(p1, 1e-300)
        num = K * (r0[:, :, None, :] + r1[:, None, :, :])
        K = num / np.maximum(num.sum(axis=3, keepdims=True), 1e-300)
    return K


def g_float(q, K):
    """(1/2) sum_x D(q_x || p_x(K)) in floats."""
    P = MU_F[None, :, :, None] * K
    p = np.stack([P.sum(axis=2), P.sum(axis=1)], axis=1)
    m = q > 0
    t = np.where(m, q * np.log(np.where(m, q, 1.0) / np.maximum(p, 1e-300)), 0.0)
    return 0.5 * t.reshape(q.shape[0], -1).sum(axis=1)


# ------------------------------------------------------------------------------------------- kernel models
DY = 2.0 ** -52
KFLOOR = 2.0 ** -40


def clean_kernel(K):
    """dyadic kernel with every entry >= KFLOOR and every b-sum exactly 1."""
    K = np.maximum(np.round(K / DY) * DY, KFLOOR)
    ref = np.argmax(K, axis=-1)
    others = K.sum(axis=-1) - np.take_along_axis(K, ref[..., None], -1)[..., 0]
    # recompute the reference entry exactly: all entries are multiples of 2^-52 below 1, so sums are exact
    K2 = K.copy()
    np.put_along_axis(K2, ref[..., None], (1.0 - others)[..., None], -1)
    assert np.all(K2 >= KFLOOR) and np.all(K2.sum(axis=-1) == 1.0)
    return K2


def _A_matrix(mu):
    """linear map dK (27, index 9 a0 + 3 a1 + b) -> dp (18, index 9 x + 3 a + b)."""
    A = np.zeros((18, 27))
    for a0 in range(3):
        for a1 in range(3):
            for b in range(3):
                j = 9 * a0 + 3 * a1 + b
                A[0 * 9 + 3 * a0 + b, j] += mu[a0, a1]
                A[1 * 9 + 3 * a1 + b, j] += mu[a0, a1]
    return A


A27 = _A_matrix(MU_F)


def kernel_slope(q, dq, K, supp_tol=1e-7):
    """first-order response M (N, 27, 6) of the optimal kernel: weighted least squares on the face given by the
    support of K (entries > supp_tol), zero b-sums.  q (N, 18), dq (N, 18, 6) at the centre, K (N, 3, 3, 3)."""
    N = q.shape[0]
    Kf = K.reshape(N, 27)
    supp = Kf > supp_tol
    # projection onto {sum_b = 0 within each (a0, a1) block, zero off the support}
    P0 = np.zeros((N, 27, 27))
    for blk in range(9):
        idx = np.arange(3 * blk, 3 * blk + 3)
        s = supp[:, idx].astype(float)                      # (N, 3)
        cnt = np.maximum(s.sum(axis=1), 1.0)
        blkP = np.einsum("ni,ij->nij", s, np.eye(3)) - np.einsum("ni,nj->nij", s, s) / cnt[:, None, None]
        P0[:, idx[:, None], idx[None, :]] = blkP
    p = np.einsum("ij,nj->ni", A27, Kf)
    W = q / (2 * np.maximum(p, 1e-300) ** 2)
    Bv = 0.5 * dq / np.maximum(p, 1e-300)[:, :, None]       # (N, 18, 6)
    Ap = np.einsum("ij,njk->nik", A27, P0)                 # (N, 18, 27)
    G = np.einsum("nik,ni,nil->nkl", Ap, W, Ap)
    lam = 1e-10 * np.maximum(np.einsum("nkk->n", G), 1e-300)
    G = G + lam[:, None, None] * np.eye(27)
    rhs = np.einsum("nik,nij->nkj", Ap, Bv)
    u = np.linalg.solve(G, rhs)
    M = np.einsum("nkl,nlj->nkj", P0, u)
    return M


def clean_slope(M, K, h):
    """dyadic M (N, 27, 6) with exactly zero b-sums, and K + M t >= 0 for |t_i| <= h_i (else that block is zeroed)."""
    N = M.shape[0]
    Mq = np.round(M / 2.0 ** -40) * 2.0 ** -40
    Mq = Mq.reshape(N, 9, 3, NP)
    Kb = K.reshape(N, 9, 3)
    ref = np.argmax(Kb, axis=2)                           # reference entry per block: the largest kernel entry
    tot = Mq.sum(axis=2) - np.take_along_axis(Mq, ref[:, :, None, None], 2)[:, :, 0, :]
    np.put_along_axis(Mq, ref[:, :, None, None], -tot[:, :, None, :], 2)
    assert np.all(Mq.sum(axis=2) == 0.0)
    # nonnegativity over the box: scale each block's slope by t = min(1, min_c K/slack) (a power of 2, so the zero
    # b-sums stay exact), then check rigorously; blocks that still fail are zeroed
    slack = V.up(np.einsum("nbci,ni->nbc", np.abs(Mq), h) * (1 + 1e-12))
    ratio = np.min(np.where(slack > 0, Kb / np.maximum(slack, 1e-300), np.inf), axis=2)      # (N, 9)
    t = np.where(ratio >= 1, 1.0, 2.0 ** np.floor(np.log2(np.maximum(ratio, 1e-300))))
    t = np.where(ratio >= 1, 1.0, np.where(t > 0, t, 0.0))
    Mq = Mq * t[:, :, None, None]                          # exact: multiplication by a power of 2
    slack = V.up(np.einsum("nbci,ni->nbc", np.abs(Mq), h) * (1 + 1e-12))
    bad = np.any(Kb < slack, axis=2)                      # (N, 9), exact comparison
    Mq[bad] = 0.0
    assert np.all(Mq.sum(axis=2) == 0.0)
    return Mq.reshape(N, 27, NP)


def p_model(K, M):
    """interval p (N, 18) for the kernel K (float array (N,3,3,3) or IV) and slopes dp (N, 18, 6) for M (N, 27, 6)
    (or None), with mu = mu* as an interval (the true model)."""
    K = V.as_iv(K)
    N = K.lo.shape[0]
    Kf = K.reshape(N, 27)
    cols = []
    for x in range(2):
        for a in range(3):
            for b in range(3):
                acc = None
                for o in range(3):
                    a0, a1 = (a, o) if x == 0 else (o, a)
                    t = Kf[:, 9 * a0 + 3 * a1 + b] * MU[a0, a1]
                    acc = t if acc is None else acc + t
                cols.append(acc)
    p = IV(np.stack([c.lo for c in cols], -1), np.stack([c.hi for c in cols], -1))
    if M is None:
        return p, IV(np.zeros((N, 18, NP)))
    dcols = []
    for x in range(2):
        for a in range(3):
            for b in range(3):
                acc = None
                for o in range(3):
                    a0, a1 = (a, o) if x == 0 else (o, a)
                    t = IV(M[:, 9 * a0 + 3 * a1 + b, :]) * MU[a0, a1]
                    acc = t if acc is None else acc + t
                dcols.append(acc)
    dp = IV(np.stack([c.lo for c in dcols], -2), np.stack([c.hi for c in dcols], -2))
    return p, dp


# ------------------------------------------------------------------------------------------- the bound
QMIN = 1e-7
KAPPA = 0.25


def _quadmax(g, H, h):
    """rigorous upper bound of max over |t_i| <= h_i of g.t + (1/2) t^T H t for all H in the packed interval H.
    g: IV (N, 6); H: IV (N, 21); h: (N, 6).  Two bounds, the smaller is returned:
      (i)  scaled Gershgorin: t^T H t <= sum_i gam_i t_i^2, gam_i = Hii^+ + sum_{j != i} |Hij| h_j / h_i;
      (ii) isotropic: gam I - [H] positive definite (interval Cholesky) for gam slightly above the float eigenvalue."""
    N = h.shape[0]
    gm = g.mag()
    Hm = H.mag()
    full_mag = np.zeros((N, NP, NP))
    full_mag[:, TI, TJ] = Hm
    full_mag[:, TJ, TI] = Hm
    hi_diag = H.hi[:, DIAG]
    off = full_mag.copy()
    off[:, np.arange(NP), np.arange(NP)] = 0.0
    hs = np.maximum(h, 1e-300)
    gam1 = V.up(hi_diag + V.up(np.einsum("nij,nj->ni", off, h) / hs) * (1 + 1e-12))
    b1 = _sep_bound(gm, gam1, h)
    # isotropic certified eigenvalue bound
    Hmid = np.zeros((N, NP, NP))
    Hmid[:, TI, TJ] = H.mid()
    Hmid[:, TJ, TI] = H.mid()
    lam = np.linalg.eigvalsh(Hmid)[:, -1]
    radsum = np.max(np.sum(_rad_full(H), axis=2), axis=1)
    gam = lam + radsum + 1e-9 + 1e-6 * np.abs(lam)          # a candidate; the Cholesky below certifies it
    Afull_lo = np.zeros((N, NP, NP))
    Afull_hi = np.zeros((N, NP, NP))
    # gam I - H
    Afull_lo[:, TI, TJ] = -H.hi
    Afull_hi[:, TI, TJ] = -H.lo
    Afull_lo[:, TJ, TI] = -H.hi
    Afull_hi[:, TJ, TI] = -H.lo
    dd = np.arange(NP)
    Afull_lo[:, dd, dd] = V.dn(gam[:, None] - H.hi[:, DIAG])
    Afull_hi[:, dd, dd] = V.up(gam[:, None] - H.lo[:, DIAG])
    ok = V.chol_pd(IV(Afull_lo, Afull_hi))
    b2 = np.where(ok, _sep_bound(gm, np.repeat(gam[:, None], NP, axis=1), h), np.inf)
    return np.minimum(b1, b2)


def _rad_full(H):
    N = H.lo.shape[0]
    r = np.zeros((N, NP, NP))
    rad = H.rad()
    r[:, TI, TJ] = rad
    r[:, TJ, TI] = rad
    return r


def _sep_bound(gm, gam, h):
    """sum_i max over |t| <= h_i of (gm_i t + gam_i t^2 / 2) (gm_i >= 0), as a rigorous upper bound.
    The maximum is at t = h_i unless gam_i < 0 and the vertex gm_i / (-gam_i) lies inside, where it is gm_i^2/(-2 gam_i)."""
    G = IV(gm)
    Gam = IV(gam)
    Hh = IV(h)
    end = (G * Hh + (Gam * Hh.sqr()) * 0.5).hi
    neg = gam < 0
    vert = (G.sqr() / IV(np.where(neg, -2.0 * gam, 1.0))).hi        # -2 gam is exact
    inside = neg & (gm <= -gam * h * (1 - 1e-12))
    v = np.where(inside, np.maximum(vert, end), end)
    return V.isum(IV(v), axis=1).hi


def box_geometry(lo, hi):
    c = 0.5 * (lo + hi)
    h = V.up(np.maximum(V.up(hi - c), V.up(c - lo)))
    return c, h


def box_jets(lo, hi, centre=True, T=None, x0=None):
    """q jets over the boxes (value, gradient, Hessian) and, if centre, at the box centres (value, gradient)."""
    c, h = box_geometry(lo, hi)
    qv, qg, qH = q_jets(bt_jets(lo, hi, point=False, hess=True, T=T, x0=x0))
    if not centre:
        return (qv, qg, qH), None, c, h
    qcv, qcg, _ = q_jets(bt_jets(c, c, point=(T is None), hess=False, T=T, x0=x0))
    return (qv, qg, qH), (qcv, qcg), c, h


def hessian_enclosure(qb, p_b, dp, mask):
    """enclosure of the Hessian (packed, (N, 21)) of g_mask = (1/2) sum_{cells in mask} q log(q/p) over the box.
    If mask is all-true for a row, the identity sum_cells d2q = 0 lets the (log + 1) factor drop the '+1'."""
    qv, qg, qH = qb
    N = qv.lo.shape[0]
    qq = IV(np.where(mask, qv.lo, 1.0), np.where(mask, qv.hi, 1.0))
    pp = IV(np.where(mask, p_b.lo, 1.0), np.where(mask, p_b.hi, 1.0))
    L = V.log(qq) - V.log(pp)
    full = np.all(mask, axis=1)
    Lp1 = L + IV(np.where(full, 0.0, 1.0)[:, None] * np.ones((1, 18)))
    av = qg / qq[..., None] - dp / pp[..., None]
    Hc = (qH * Lp1[..., None] + qq[..., None] * (av[..., TI] * av[..., TJ])) * 0.5
    m = mask.astype(float)[..., None]
    return V.isum(IV(Hc.lo * m, Hc.hi * m), axis=1)


def taylor_bound(qb, qc, p_c, dp, h, extra_mask=None):
    """rigorous upper bound of g = (1/2) sum_cells q log(q/p) over the boxes, p = p_c + dp.(y - c) linear.
    qb: box jets; qc: centre (value, grad); p_c: IV (N, 18) at the centre; dp: IV (N, 18, 6)."""
    qv, qg, qH = qb
    qcv, qcg = qc
    N = qv.lo.shape[0]
    hb = IV(-h, h)
    p_b = p_c + V.isum(dp * hb[:, None, :], axis=2)
    pos = (p_b.lo > 0) & (p_c.lo > 0)
    good = (qv.lo >= QMIN) & (qv.lo >= KAPPA * qv.hi) & pos & (qcv.lo > 0)
    if extra_mask is not None:
        good &= extra_mask
    # bad cells: maximum of the jointly convex (1/2) q log(q/p) over the vertices of the (q, p) rectangle
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
    # good cells: value and gradient at the centre, Hessian over the box
    qc_ = IV(np.where(good, qcv.lo, 1.0), np.where(good, qcv.hi, 1.0))
    pc_ = IV(np.where(good, p_c.lo, 1.0), np.where(good, p_c.hi, 1.0))
    Lc = V.log(qc_) - V.log(pc_)
    full = np.all(good, axis=1)
    Lc1 = Lc + IV(np.where(full, 0.0, 1.0)[:, None] * np.ones((1, 18)))
    f_c = (qc_ * Lc) * 0.5
    grad_c = (qcg * Lc1[..., None] - (qc_[..., None] * dp) / pc_[..., None]) * 0.5
    gm = good.astype(float)
    f_sum = V.isum(IV(f_c.lo * gm, f_c.hi * gm), axis=1)
    g_sum = V.isum(IV(grad_c.lo * gm[..., None], grad_c.hi * gm[..., None]), axis=1)
    H_sum = hessian_enclosure(qb, p_b, dp, good)
    qm = _quadmax(g_sum, H_sum, h)
    ub = (IV(f_sum.hi) + IV(qm) + IV(bad_sum)).hi
    return ub, dict(good=good.sum(axis=1), H=H_sum, g=g_sum, f=f_sum)


def refine2(qb, qc, h):
    """mean-value refinement of the box enclosures of q and its gradient from the centre values and the box Hessian:
       g_box <- g(c) + sum_j H_box[., j] [-h_j, h_j],  v_box <- v(c) + sum_i g_box[i] [-h_i, h_i]  (intersected)."""
    qv, qg, qH = qb
    cv, cg = qc
    hb = IV(-h, h)[:, None, :]
    Hj = qH[:, :, PIJF2]
    addg = V.isum(Hj * hb[:, :, None, :], axis=3)
    qg = IV(np.maximum(qg.lo, (cg + addg).lo), np.minimum(qg.hi, (cg + addg).hi))
    addv = V.isum(qg * hb, axis=2)
    qv = IV(np.maximum(qv.lo, (cv + addv).lo), np.minimum(qv.hi, (cv + addv).hi))
    return (qv, qg, qH)


PIJF2 = np.array([[PIDX[(i, j)] for j in range(NP)] for i in range(NP)])


def box_bound(lo, hi, K, M):
    """upper bound over the boxes [lo, hi] for the kernel model K + M (y - c) (K exact floats, M exact or None)."""
    qb, qc, c, h = box_jets(lo, hi)
    qb = refine2(qb, qc, h)
    p_c, dp = p_model(K, M)
    ub, info = taylor_bound(qb, qc, p_c, dp, h)
    info["h"] = h
    return ub, info


def outside_R(lo, hi):
    """True where the box lies entirely outside R = {|Bt00| >= |Bt01| >= |Bt02|} (rigorous).  Every orbit of the column
    permutations meets R, and column permutations relabel b, which leaves Phi unchanged."""
    import nash_core3 as _T3
    B = _T3.bt_values(lo, hi)
    m = [(B[0][j][0].sqr() + B[0][j][1].sqr()) for j in range(3)]
    return (m[1].lo > m[0].hi) | (m[2].lo > m[1].hi)
