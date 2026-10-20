"""numba port of the rigorous q-jets used by track.py (run with the repo .venv python, which has numba).

Same mathematics as track.jets: nash_core3.bt3 (CKM jets), kl3mix.z3 (z = (1/3) sum_k om[x,a,k] Bt[k,b]),
nash_core3.refine (mean-value refinement) and Jet3.sqr (q = (Re z)^2 + (Im z)^2), for a batch of boxes:
  centre: q value, gradient, Hessian (point evaluation at c = (lo + hi)/2);
  box:    q value, gradient, Hessian over [lo, hi], refined from the centre jets and the box third derivatives.

Interval arithmetic: an interval is a pair (lo, hi) of floats; every operation computes the float result(s) with
round-to-nearest and then rounds outward with
    up(x) = x + (|x| 2^-51 + 2^-1073),   dn(x) = x - (|x| 2^-51 + 2^-1073)      (up(-inf) = -inf, dn(inf) = inf).
Rigour of up: if x = fl(r) then r <= x + ulp(x)/2 <= x + 2^-53 |x| (normal x) or r <= x + 2^-1075 (subnormal);
the computed increment is >= |x| 2^-51 - 2^-1075 + 2^-1073 (the product |x| 2^-51 is exact unless it underflows,
in which case its error is <= 2^-1075), and fl(x + incr) >= x + incr - ulp(x + incr)/2 >= x + |x| 2^-52 + 2^-1074
for every finite x, which exceeds x + ulp(x)/2.  dn is symmetric.
Transcendentals: log and sin/cos are not taken from the C library; they are the series of nash_iv.log_point /
nash_iv.sincos_point (argument reduction with an interval pi/2, Taylor polynomials with Lagrange remainders), with
the same interval constants."""
import os, sys, math
import numpy as np
import numba as nb

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, ROOT)
import nash_core as C
import nash_core3 as T3
import nash_iv as V

# ---------------------------------------------------------------- tables (compile-time constants)
TI = np.ascontiguousarray(C.TI.astype(np.int64))
TJ = np.ascontiguousarray(C.TJ.astype(np.int64))
DIAG = np.ascontiguousarray(C.DIAG.astype(np.int64))
I3 = np.ascontiguousarray(T3.I3.astype(np.int64))
J3 = np.ascontiguousarray(T3.J3.astype(np.int64))
K3 = np.ascontiguousarray(T3.K3.astype(np.int64))
PIJ = np.ascontiguousarray(T3.PIJ.astype(np.int64))
PIK = np.ascontiguousarray(T3.PIK.astype(np.int64))
PJK = np.ascontiguousarray(T3.PJK.astype(np.int64))
PK3 = np.ascontiguousarray(T3.PK3.astype(np.int64))         # (21, 6) triple index of (pair p, k)
PIJF = np.ascontiguousarray(T3.PIJF.astype(np.int64))       # (6, 6) pair index
DIAG3 = np.ascontiguousarray(T3.DIAG3.astype(np.int64))
NJ = 84                                                       # 1 + 6 + 21 + 56
OG, OH, OT = 1, 7, 28

PIH_LO, PIH_HI = float(V.PI_HALF.lo), float(V.PI_HALF.hi)
LN2_LO, LN2_HI = float(V.LN2.lo), float(V.LN2.hi)
IF_LO = np.array([float(x.lo) for x in V._INV_FACT])
IF_HI = np.array([float(x.hi) for x in V._INV_FACT])
IO_LO = np.array([float(x.lo) for x in V._INV_ODD])
IO_HI = np.array([float(x.hi) for x in V._INV_ODD])
OMR_LO = np.ascontiguousarray(C.OM_RE.lo)
OMR_HI = np.ascontiguousarray(C.OM_RE.hi)
OMI_LO = np.ascontiguousarray(C.OM_IM.lo)
OMI_HI = np.ascontiguousarray(C.OM_IM.hi)
# om[x,a,k] = exp(i pi n / 3) with the integer n = -k(2a+1) (x = 0, alpha = 1/2) or n = -2ka (x = 1, alpha = 0):
# real part COS6[n mod 6] in {1, 1/2, -1/2, -1} (exact floats), imaginary part SIN6[n mod 6] * sqrt(3)/2
_COS6 = np.array([1.0, 0.5, -0.5, -1.0, -0.5, 0.5])
_SIN6 = np.array([0, 1, 1, 0, -1, -1], dtype=np.int64)
OMC = np.zeros((2, 3, 3))
OMS = np.zeros((2, 3, 3), dtype=np.int64)
for _x in range(2):
    for _a in range(3):
        for _k in range(3):
            _n = -_k * (2 * _a + 1) if _x == 0 else -2 * _k * _a
            OMC[_x, _a, _k] = _COS6[_n % 6]
            OMS[_x, _a, _k] = _SIN6[_n % 6]
_s3h = V.const(V.iv.sqrt(3) / 2)
S3H_LO, S3H_HI = float(_s3h.lo), float(_s3h.hi)
assert np.allclose(OMC, C.OM_RE.mid(), atol=1e-15) and np.allclose(OMS * 0.8660254037844386, C.OM_IM.mid(), atol=1e-15)
_th = V.const(V.iv.mpf(1) / 3)
TH_LO, TH_HI = float(_th.lo), float(_th.hi)

# multi-index bookkeeping: entry t <-> sorted tuple of coordinates (len 0..3)
_TRI = [tuple(t) for t in T3.TRI]
_MI = [()] + [(i,) for i in range(6)] + [(int(i), int(j)) for i, j in zip(C.TI, C.TJ)] + _TRI
assert len(_MI) == 84


def _index_of(tup):
    tup = tuple(sorted(tup))
    return _MI.index(tup)


def disjoint_maps(mask_f, mask_g):
    """for jets f, g depending only on the coordinate sets mask_f, mask_g (disjoint): (fg)_alpha =
    f_{alpha|mask_f} g_{alpha|mask_g} when alpha is supported in mask_f | mask_g, else 0 (Leibniz: the only
    nonzero term has beta = alpha|mask_f, binomial 1).  Returns int arrays (84,) idx_f, idx_g (-1 for zero)."""
    assert not (set(mask_f) & set(mask_g))
    fi = -np.ones(84, dtype=np.int64)
    gi = -np.ones(84, dtype=np.int64)
    for t, tup in enumerate(_MI):
        if all((c in mask_f) or (c in mask_g) for c in tup):
            fi[t] = _index_of([c for c in tup if c in mask_f])
            gi[t] = _index_of([c for c in tup if c in mask_g])
    return fi, gi


_PAIRS = {"0_2": ((0,), (2,)), "1_3": ((1,), (3,)), "0_1": ((0,), (1,)), "2_1": ((2,), (1,)),
          "13_02": ((1, 3), (0, 2)), "4_0123": ((4,), (0, 1, 2, 3)), "5_0123": ((5,), (0, 1, 2, 3))}
DMAP = {k: disjoint_maps(*v) for k, v in _PAIRS.items()}
DF_02, DG_02 = DMAP["0_2"]
DF_13, DG_13 = DMAP["1_3"]
DF_01, DG_01 = DMAP["0_1"]
DF_21, DG_21 = DMAP["2_1"]
DF_1302, DG_1302 = DMAP["13_02"]
DF_4, DG_4 = DMAP["4_0123"]
DF_5, DG_5 = DMAP["5_0123"]

C1 = 2.0 ** -51
C2 = 2.0 ** -1073
INF = np.inf


@nb.njit(inline="always")
def up(x):
    if x == -INF:
        return x
    return x + (abs(x) * C1 + C2)


@nb.njit(inline="always")
def dn(x):
    if x == INF:
        return x
    return x - (abs(x) * C1 + C2)


@nb.njit(inline="always")
def iadd(al, ah, bl, bh):
    return dn(al + bl), up(ah + bh)


@nb.njit(inline="always")
def isub(al, ah, bl, bh):
    return dn(al - bh), up(ah - bl)


@nb.njit(inline="always")
def imul(al, ah, bl, bh):
    p1 = al * bl
    p2 = al * bh
    p3 = ah * bl
    p4 = ah * bh
    if p1 != p1 or p2 != p2 or p3 != p3 or p4 != p4:      # NaN (0 * inf): return the whole line
        return -INF, INF
    return dn(min(min(p1, p2), min(p3, p4))), up(max(max(p1, p2), max(p3, p4)))


@nb.njit(inline="always")
def isqr(al, ah):
    if al >= 0.0:
        return max(dn(al * al), 0.0), up(ah * ah)
    if ah <= 0.0:
        return max(dn(ah * ah), 0.0), up(al * al)
    return 0.0, up(max(al * al, ah * ah))


@nb.njit(inline="always")
def idiv_pos(al, ah, bl, bh):
    """a / b for b > 0."""
    p1 = al / bl
    p2 = al / bh
    p3 = ah / bl
    p4 = ah / bh
    return dn(min(min(p1, p2), min(p3, p4))), up(max(max(p1, p2), max(p3, p4)))


@nb.njit
def horner(tl, th, cl, ch, n):
    """sum_{k<n} c_k t^k with interval coefficients (cl, ch)."""
    al, ah = cl[n - 1], ch[n - 1]
    for k in range(n - 2, -1, -1):
        al, ah = imul(al, ah, tl, th)
        al, ah = iadd(al, ah, cl[k], ch[k])
    return al, ah


@nb.njit
def log_point(x):
    """rigorous enclosure of log(x), x > 0 a float (port of nash_iv.log_point)."""
    m, e = math.frexp(x)
    if m < 0.7071067811865476:
        m = 2.0 * m
        e = e - 1
    num = m - 1.0                                    # exact (Sterbenz)
    sl, sh = idiv_pos(num, num, dn(m + 1.0), up(m + 1.0))
    tl, th = isqr(sl, sh)
    pl, ph = horner(tl, th, IO_LO, IO_HI, 11)
    vl, vh = imul(sl, sh, pl, ph)
    vl, vh = dn(2.0 * vl), up(2.0 * vh)
    sm = max(abs(sl), abs(sh))
    rem = up(1.01 * up(up(2.0 * up(sm ** 23)) / up(23.0 * dn(1.0 - up(sm * sm)))))
    vl, vh = dn(vl - rem), up(vh + rem)
    el, eh = imul(float(e), float(e), LN2_LO, LN2_HI)
    return iadd(el, eh, vl, vh)


@nb.njit
def sincos_point(x):
    """rigorous enclosures of sin(x), cos(x) for a float x, |x| <= 1e3 (port of nash_iv.sincos_point)."""
    k = np.rint(x / 1.5707963267948966)
    kl, kh = imul(k, k, PIH_LO, PIH_HI)
    rl, rh = isub(x, x, kl, kh)
    tl, th = isqr(rl, rh)
    # sin(r)/r and cos(r) polynomials in t = r^2 with alternating inverse factorial coefficients
    scl = np.empty(11)
    sch = np.empty(11)
    for j in range(11):
        if j % 2 == 0:
            scl[j] = IF_LO[2 * j + 1]
            sch[j] = IF_HI[2 * j + 1]
        else:
            scl[j] = -IF_HI[2 * j + 1]
            sch[j] = -IF_LO[2 * j + 1]
    ccl = np.empty(12)
    cch = np.empty(12)
    for j in range(12):
        if j % 2 == 0:
            ccl[j] = IF_LO[2 * j]
            cch[j] = IF_HI[2 * j]
        else:
            ccl[j] = -IF_HI[2 * j]
            cch[j] = -IF_LO[2 * j]
    pl, ph = horner(tl, th, scl, sch, 11)
    sl, sh = imul(rl, rh, pl, ph)
    cl, ch = horner(tl, th, ccl, cch, 12)
    rm = max(abs(rl), abs(rh))
    rem_s = up(1.01 * up(up(rm ** 23) * IF_HI[23]))
    rem_c = up(1.01 * up(up(rm ** 24) * IF_HI[24]))
    sl, sh = dn(sl - rem_s), up(sh + rem_s)
    cl, ch = dn(cl - rem_c), up(ch + rem_c)
    q = int(k) % 4
    if q == 0:
        s0l, s0h, c0l, c0h = sl, sh, cl, ch
    elif q == 1:
        s0l, s0h, c0l, c0h = cl, ch, -sh, -sl
    elif q == 2:
        s0l, s0h, c0l, c0h = -sh, -sl, -ch, -cl
    else:
        s0l, s0h, c0l, c0h = -ch, -cl, sl, sh
    return max(s0l, -1.0), min(s0h, 1.0), max(c0l, -1.0), min(c0h, 1.0)


@nb.njit
def sincos_iv(lo, hi):
    """enclosures of sin, cos over [lo, hi] (port of nash_iv.sincos: Taylor about the midpoint, remainder r^2/2)."""
    m = 0.5 * (lo + hi)
    r = up(max(up(hi - m), up(m - lo)))              # rigorous radius about the rounded midpoint (audit 2)
    sl, sh, cl, ch = sincos_point(m)
    q = up(0.5 * up(r * r))
    al, ah = imul(cl, ch, -r, r)
    s2l, s2h = iadd(sl, sh, al, ah)
    s2l, s2h = iadd(s2l, s2h, -q, q)
    bl, bh = imul(sl, sh, -r, r)
    c2l, c2h = isub(cl, ch, bl, bh)
    c2l, c2h = iadd(c2l, c2h, -q, q)
    return max(s2l, -1.0), min(s2h, 1.0), max(c2l, -1.0), min(c2h, 1.0)


# ---------------------------------------------------------------- jets: arrays (NJ,) lo, hi
@nb.njit
def jzero(l, h):
    for t in range(NJ):
        l[t] = 0.0
        h[t] = 0.0


@nb.njit
def jmul(al, ah, bl, bh, ol, oh, order3):
    """o = a b (product rule up to order 2 or 3); o must not alias a or b."""
    ol[0], oh[0] = imul(al[0], ah[0], bl[0], bh[0])
    for i in range(6):
        x1, y1 = imul(al[OG + i], ah[OG + i], bl[0], bh[0])
        x2, y2 = imul(al[0], ah[0], bl[OG + i], bh[OG + i])
        ol[OG + i], oh[OG + i] = iadd(x1, y1, x2, y2)
    for p in range(21):
        i = TI[p]
        j = TJ[p]
        sl, sh = imul(al[OH + p], ah[OH + p], bl[0], bh[0])
        x, y = imul(al[0], ah[0], bl[OH + p], bh[OH + p])
        sl, sh = iadd(sl, sh, x, y)
        x, y = imul(al[OG + i], ah[OG + i], bl[OG + j], bh[OG + j])
        sl, sh = iadd(sl, sh, x, y)
        x, y = imul(al[OG + j], ah[OG + j], bl[OG + i], bh[OG + i])
        sl, sh = iadd(sl, sh, x, y)
        ol[OH + p] = sl
        oh[OH + p] = sh
    if order3:
        for t in range(56):
            i = I3[t]
            j = J3[t]
            k = K3[t]
            sl, sh = imul(al[0], ah[0], bl[OT + t], bh[OT + t])
            x, y = imul(al[OT + t], ah[OT + t], bl[0], bh[0])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OG + i], ah[OG + i], bl[OH + PJK[t]], bh[OH + PJK[t]])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OG + j], ah[OG + j], bl[OH + PIK[t]], bh[OH + PIK[t]])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OG + k], ah[OG + k], bl[OH + PIJ[t]], bh[OH + PIJ[t]])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OH + PIJ[t]], ah[OH + PIJ[t]], bl[OG + k], bh[OG + k])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OH + PIK[t]], ah[OH + PIK[t]], bl[OG + j], bh[OG + j])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OH + PJK[t]], ah[OH + PJK[t]], bl[OG + i], bh[OG + i])
            sl, sh = iadd(sl, sh, x, y)
            ol[OT + t] = sl
            oh[OT + t] = sh
    else:
        for t in range(56):
            ol[OT + t] = 0.0
            oh[OT + t] = 0.0


@nb.njit
def jmul_d(al, ah, bl, bh, ol, oh, fi, gi, nent):
    """o = a b for jets with disjoint coordinate supports (maps from disjoint_maps); entries t >= nent set to 0."""
    for t in range(nent):
        if fi[t] < 0:
            ol[t] = 0.0
            oh[t] = 0.0
        else:
            ol[t], oh[t] = imul(al[fi[t]], ah[fi[t]], bl[gi[t]], bh[gi[t]])
    for t in range(nent, NJ):
        ol[t] = 0.0
        oh[t] = 0.0


@nb.njit
def jadd(al, ah, bl, bh, ol, oh, sgn):
    """o = a + sgn b (sgn = +1 or -1); o may alias a."""
    for t in range(NJ):
        if sgn > 0:
            ol[t], oh[t] = iadd(al[t], ah[t], bl[t], bh[t])
        else:
            ol[t], oh[t] = isub(al[t], ah[t], bl[t], bh[t])


@nb.njit
def jscale(al, ah, sl, sh, ol, oh):
    for t in range(NJ):
        ol[t], oh[t] = imul(al[t], ah[t], sl, sh)


@nb.njit
def jneg(al, ah, ol, oh):
    for t in range(NJ):
        x = -ah[t]
        y = -al[t]
        ol[t] = x
        oh[t] = y


@nb.njit
def jsqr(al, ah, ol, oh, order3):
    """o = a^2 (Jet3.sqr): v^2, 2 v g, 2 (v H + g_i g_j), 2 (v T + g_i H_jk + g_j H_ik + g_k H_ij)."""
    ol[0], oh[0] = isqr(al[0], ah[0])
    for i in range(6):
        x, y = imul(al[0], ah[0], al[OG + i], ah[OG + i])
        ol[OG + i] = dn(2.0 * x)
        oh[OG + i] = up(2.0 * y)
    for p in range(21):
        i = TI[p]
        j = TJ[p]
        sl, sh = imul(al[0], ah[0], al[OH + p], ah[OH + p])
        if i == j:
            x, y = isqr(al[OG + i], ah[OG + i])
        else:
            x, y = imul(al[OG + i], ah[OG + i], al[OG + j], ah[OG + j])
        sl, sh = iadd(sl, sh, x, y)
        ol[OH + p] = dn(2.0 * sl)
        oh[OH + p] = up(2.0 * sh)
    if order3:
        for t in range(56):
            i = I3[t]
            j = J3[t]
            k = K3[t]
            sl, sh = imul(al[0], ah[0], al[OT + t], ah[OT + t])
            x, y = imul(al[OG + i], ah[OG + i], al[OH + PJK[t]], ah[OH + PJK[t]])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OG + j], ah[OG + j], al[OH + PIK[t]], ah[OH + PIK[t]])
            sl, sh = iadd(sl, sh, x, y)
            x, y = imul(al[OG + k], ah[OG + k], al[OH + PIJ[t]], ah[OH + PIJ[t]])
            sl, sh = iadd(sl, sh, x, y)
            ol[OT + t] = dn(2.0 * sl)
            oh[OT + t] = up(2.0 * sh)
    else:
        for t in range(56):
            ol[OT + t] = 0.0
            oh[OT + t] = 0.0


@nb.njit
def coord_jets(sl, sh, cl, ch, k, Sl, Sh, Cl, Ch, order3):
    """jets of sin and cos of coordinate k with value enclosures s, c (nash_core3.pjets)."""
    jzero(Sl, Sh)
    jzero(Cl, Ch)
    Sl[0], Sh[0] = sl, sh
    Cl[0], Ch[0] = cl, ch
    Sl[OG + k], Sh[OG + k] = cl, ch
    Cl[OG + k], Ch[OG + k] = -sh, -sl
    Sl[OH + DIAG[k]], Sh[OH + DIAG[k]] = -sh, -sl
    Cl[OH + DIAG[k]], Ch[OH + DIAG[k]] = -ch, -cl
    if order3:
        Sl[OT + DIAG3[k]], Sh[OT + DIAG3[k]] = -ch, -cl
        Cl[OT + DIAG3[k]], Ch[OT + DIAG3[k]] = sl, sh


@nb.njit
def bt_jets(lo, hi, point, order3, Bl, Bh):
    """jets of the steered basis Bt over the box [lo, hi] (point=False) or at the point lo (point=True).
    Output Bl, Bh: (3, 3, 2, NJ) with [k, b, re/im, jet]; same algebra as nash_core3.bt3."""
    ne = NJ if order3 else OT
    S = np.empty((6, 2, NJ))       # [coord, lo/hi, jet] for sin
    Cc = np.empty((6, 2, NJ))
    for k in range(6):
        if point:
            sl, sh, cl, ch = sincos_point(lo[k])
        else:
            sl, sh, cl, ch = sincos_iv(lo[k], hi[k])
        coord_jets(sl, sh, cl, ch, k, S[k, 0], S[k, 1], Cc[k, 0], Cc[k, 1], order3)
    s12l, s12h, c12l, c12h = S[0, 0], S[0, 1], Cc[0, 0], Cc[0, 1]
    s13l, s13h, c13l, c13h = S[1, 0], S[1, 1], Cc[1, 0], Cc[1, 1]
    s23l, s23h, c23l, c23h = S[2, 0], S[2, 1], Cc[2, 0], Cc[2, 1]
    sdl, sdh, cdl, cdh = S[3, 0], S[3, 1], Cc[3, 0], Cc[3, 1]
    s1l, s1h, c1l, c1h = S[4, 0], S[4, 1], Cc[4, 0], Cc[4, 1]
    s2l, s2h, c2l, c2h = S[5, 0], S[5, 1], Cc[5, 0], Cc[5, 1]
    W = np.empty((16, 2, NJ))
    # 0 c12c23, 1 s12s23, 2 c12s23, 3 s12c23, 4 s13cd (se.re), 5 s13sd (se.im), 6 tmp, 7 tmp, 8 tmp
    jmul_d(c12l, c12h, c23l, c23h, W[0, 0], W[0, 1], DF_02, DG_02, ne)
    jmul_d(s12l, s12h, s23l, s23h, W[1, 0], W[1, 1], DF_02, DG_02, ne)
    jmul_d(c12l, c12h, s23l, s23h, W[2, 0], W[2, 1], DF_02, DG_02, ne)
    jmul_d(s12l, s12h, c23l, c23h, W[3, 0], W[3, 1], DF_02, DG_02, ne)
    jmul_d(s13l, s13h, cdl, cdh, W[4, 0], W[4, 1], DF_13, DG_13, ne)
    jmul_d(s13l, s13h, sdl, sdh, W[5, 0], W[5, 1], DF_13, DG_13, ne)
    V = np.empty((3, 3, 2, 2, NJ))   # [k, b, re/im, lo/hi, jet] before the row phases
    # row 0
    jmul_d(c12l, c12h, c13l, c13h, V[0, 0, 0, 0], V[0, 0, 0, 1], DF_01, DG_01, ne)
    jzero(V[0, 0, 1, 0], V[0, 0, 1, 1])
    jmul_d(s12l, s12h, c13l, c13h, V[0, 1, 0, 0], V[0, 1, 0, 1], DF_01, DG_01, ne)
    jzero(V[0, 1, 1, 0], V[0, 1, 1, 1])
    V[0, 2, 0, 0, :] = W[4, 0]
    V[0, 2, 0, 1, :] = W[4, 1]
    jneg(W[5, 0], W[5, 1], V[0, 2, 1, 0], V[0, 2, 1, 1])
    # V10 = -(se c12s23 + s12c23)
    jmul_d(W[4, 0], W[4, 1], W[2, 0], W[2, 1], W[6, 0], W[6, 1], DF_1302, DG_1302, ne)
    jadd(W[6, 0], W[6, 1], W[3, 0], W[3, 1], W[6, 0], W[6, 1], 1)
    jneg(W[6, 0], W[6, 1], V[1, 0, 0, 0], V[1, 0, 0, 1])
    jmul_d(W[5, 0], W[5, 1], W[2, 0], W[2, 1], W[7, 0], W[7, 1], DF_1302, DG_1302, ne)
    jneg(W[7, 0], W[7, 1], V[1, 0, 1, 0], V[1, 0, 1, 1])
    # V11 = c12c23 - se s12s23
    jmul_d(W[4, 0], W[4, 1], W[1, 0], W[1, 1], W[6, 0], W[6, 1], DF_1302, DG_1302, ne)
    jadd(W[0, 0], W[0, 1], W[6, 0], W[6, 1], V[1, 1, 0, 0], V[1, 1, 0, 1], -1)
    jmul_d(W[5, 0], W[5, 1], W[1, 0], W[1, 1], W[7, 0], W[7, 1], DF_1302, DG_1302, ne)
    jneg(W[7, 0], W[7, 1], V[1, 1, 1, 0], V[1, 1, 1, 1])
    # V12 = s23 c13
    jmul_d(s23l, s23h, c13l, c13h, V[1, 2, 0, 0], V[1, 2, 0, 1], DF_21, DG_21, ne)
    jzero(V[1, 2, 1, 0], V[1, 2, 1, 1])
    # V20 = s12s23 - se c12c23
    jmul_d(W[4, 0], W[4, 1], W[0, 0], W[0, 1], W[6, 0], W[6, 1], DF_1302, DG_1302, ne)
    jadd(W[1, 0], W[1, 1], W[6, 0], W[6, 1], V[2, 0, 0, 0], V[2, 0, 0, 1], -1)
    jmul_d(W[5, 0], W[5, 1], W[0, 0], W[0, 1], W[7, 0], W[7, 1], DF_1302, DG_1302, ne)
    jneg(W[7, 0], W[7, 1], V[2, 0, 1, 0], V[2, 0, 1, 1])
    # V21 = -(se s12c23 + c12s23)
    jmul_d(W[4, 0], W[4, 1], W[3, 0], W[3, 1], W[6, 0], W[6, 1], DF_1302, DG_1302, ne)
    jadd(W[6, 0], W[6, 1], W[2, 0], W[2, 1], W[6, 0], W[6, 1], 1)
    jneg(W[6, 0], W[6, 1], V[2, 1, 0, 0], V[2, 1, 0, 1])
    jmul_d(W[5, 0], W[5, 1], W[3, 0], W[3, 1], W[7, 0], W[7, 1], DF_1302, DG_1302, ne)
    jneg(W[7, 0], W[7, 1], V[2, 1, 1, 0], V[2, 1, 1, 1])
    # V22 = c23 c13
    jmul_d(c23l, c23h, c13l, c13h, V[2, 2, 0, 0], V[2, 2, 0, 1], DF_21, DG_21, ne)
    jzero(V[2, 2, 1, 0], V[2, 2, 1, 1])
    # row phases: Bt[0] = V0, Bt[1] = e1 V1, Bt[2] = e2 V2, e = c + i s
    for b in range(3):
        Bl[0, b, 0, :] = V[0, b, 0, 0]
        Bh[0, b, 0, :] = V[0, b, 0, 1]
        Bl[0, b, 1, :] = V[0, b, 1, 0]
        Bh[0, b, 1, :] = V[0, b, 1, 1]
    for r in range(1, 3):
        if r == 1:
            el, eh, fl, fh = c1l, c1h, s1l, s1h
            mf, mg = DF_4, DG_4
        else:
            el, eh, fl, fh = c2l, c2h, s2l, s2h
            mf, mg = DF_5, DG_5
        for b in range(3):
            # (e + i f)(vr + i vi) = (e vr - f vi) + i (e vi + f vr)
            jmul_d(el, eh, V[r, b, 0, 0], V[r, b, 0, 1], W[8, 0], W[8, 1], mf, mg, ne)
            jmul_d(fl, fh, V[r, b, 1, 0], V[r, b, 1, 1], W[9, 0], W[9, 1], mf, mg, ne)
            jadd(W[8, 0], W[8, 1], W[9, 0], W[9, 1], Bl[r, b, 0], Bh[r, b, 0], -1)
            jmul_d(el, eh, V[r, b, 1, 0], V[r, b, 1, 1], W[10, 0], W[10, 1], mf, mg, ne)
            jmul_d(fl, fh, V[r, b, 0, 0], V[r, b, 0, 1], W[11, 0], W[11, 1], mf, mg, ne)
            jadd(W[10, 0], W[10, 1], W[11, 0], W[11, 1], Bl[r, b, 1], Bh[r, b, 1], 1)


@nb.njit
def z_jets(Bl, Bh, Zl, Zh, nent):
    """z_x(a, b) = (1/3) sum_k om[x,a,k] Bt[k,b] (kl3mix.z3) on the first nent jet entries;
    Z: (18, 2 re/im, NJ), cell = 9 x + 3 a + b.  om = cr + i ss sqrt(3)/2 with cr in {1, 1/2, -1/2, -1} exact."""
    for x in range(2):
        for a in range(3):
            for b in range(3):
                cell = 9 * x + 3 * a + b
                for t in range(nent):
                    rl, rh, il, ih = 0.0, 0.0, 0.0, 0.0
                    for k in range(3):
                        cr = OMC[x, a, k]
                        ss = OMS[x, a, k]
                        brl, brh = Bl[k, b, 0, t], Bh[k, b, 0, t]
                        bil, bih = Bl[k, b, 1, t], Bh[k, b, 1, t]
                        # cr * Br and cr * Bi (exact up to the final outward rounding)
                        if cr > 0:
                            xl, xh = dn(cr * brl), up(cr * brh)
                            yl, yh = dn(cr * bil), up(cr * bih)
                        else:
                            xl, xh = dn(cr * brh), up(cr * brl)
                            yl, yh = dn(cr * bih), up(cr * bil)
                        rl, rh = iadd(rl, rh, xl, xh)
                        il, ih = iadd(il, ih, yl, yh)
                        if ss != 0:
                            ul, uh = imul(brl, brh, S3H_LO, S3H_HI)     # s Br
                            vl, vh = imul(bil, bih, S3H_LO, S3H_HI)     # s Bi
                            if ss > 0:
                                rl, rh = isub(rl, rh, vl, vh)            # re -= s Bi
                                il, ih = iadd(il, ih, ul, uh)            # im += s Br
                            else:
                                rl, rh = iadd(rl, rh, vl, vh)
                                il, ih = isub(il, ih, ul, uh)
                    Zl[cell, 0, t], Zh[cell, 0, t] = imul(rl, rh, TH_LO, TH_HI)
                    Zl[cell, 1, t], Zh[cell, 1, t] = imul(il, ih, TH_LO, TH_HI)
                for t in range(nent, NJ):
                    Zl[cell, 0, t] = 0.0
                    Zh[cell, 0, t] = 0.0
                    Zl[cell, 1, t] = 0.0
                    Zh[cell, 1, t] = 0.0


@nb.njit
def meet(al, ah, bl, bh):
    return max(al, bl), min(ah, bh)


@nb.njit
def refine(cl, ch, Jl, Jh, h, use_T):
    """nash_core3.refine for one jet: centre jet (cl, ch) (value, gradient, Hessian used), box jet (Jl, Jh) refined
    in place: H <- meet(H, H(c) + sum_k T[pk] [-h_k, h_k]), g <- meet(g, g(c) + sum_j H[ij] [-h_j, h_j]),
    v <- meet(v, v(c) + sum_i g_i [-h_i, h_i])."""
    if use_T:
        for p in range(21):
            sl, sh = cl[OH + p], ch[OH + p]
            for k in range(6):
                x, y = imul(Jl[OT + PK3[p, k]], Jh[OT + PK3[p, k]], -h[k], h[k])
                sl, sh = iadd(sl, sh, x, y)
            Jl[OH + p], Jh[OH + p] = meet(Jl[OH + p], Jh[OH + p], sl, sh)
    for i in range(6):
        sl, sh = cl[OG + i], ch[OG + i]
        for j in range(6):
            p = PIJF[i, j]
            x, y = imul(Jl[OH + p], Jh[OH + p], -h[j], h[j])
            sl, sh = iadd(sl, sh, x, y)
        Jl[OG + i], Jh[OG + i] = meet(Jl[OG + i], Jh[OG + i], sl, sh)
    sl, sh = cl[0], ch[0]
    for i in range(6):
        x, y = imul(Jl[OG + i], Jh[OG + i], -h[i], h[i])
        sl, sh = iadd(sl, sh, x, y)
    Jl[0], Jh[0] = meet(Jl[0], Jh[0], sl, sh)


@nb.njit
def box_geometry(lo, hi, c, h):
    for k in range(6):
        c[k] = 0.5 * (lo[k] + hi[k])
        h[k] = up(max(up(hi[k] - c[k]), up(c[k] - lo[k])))


@nb.njit
def q_jets_one(lo, hi, c, h, QCl, QCh, QBl, QBh):
    """centre q jets QC (18, NJ; order 2) and refined box q jets QB (18, NJ; order 3) for one box (track.jets)."""
    box_geometry(lo, hi, c, h)
    Bb_l = np.empty((3, 3, 2, NJ))
    Bb_h = np.empty((3, 3, 2, NJ))
    Bc_l = np.empty((3, 3, 2, NJ))
    Bc_h = np.empty((3, 3, 2, NJ))
    bt_jets(lo, hi, False, True, Bb_l, Bb_h)
    bt_jets(c, c, True, False, Bc_l, Bc_h)
    Zb_l = np.empty((18, 2, NJ))
    Zb_h = np.empty((18, 2, NJ))
    Zc_l = np.empty((18, 2, NJ))
    Zc_h = np.empty((18, 2, NJ))
    z_jets(Bb_l, Bb_h, Zb_l, Zb_h, NJ)
    z_jets(Bc_l, Bc_h, Zc_l, Zc_h, OT)
    A = np.empty((2, NJ))
    Bq = np.empty((2, NJ))
    for cell in range(18):
        for part in range(2):
            refine(Zc_l[cell, part], Zc_h[cell, part], Zb_l[cell, part], Zb_h[cell, part], h, True)
        # box q = zr^2 + zi^2 (refined v, g, H; box T)
        jsqr(Zb_l[cell, 0], Zb_h[cell, 0], A[0], A[1], True)
        jsqr(Zb_l[cell, 1], Zb_h[cell, 1], Bq[0], Bq[1], True)
        jadd(A[0], A[1], Bq[0], Bq[1], QBl[cell], QBh[cell], 1)
        # centre q (order 2)
        jsqr(Zc_l[cell, 0], Zc_h[cell, 0], A[0], A[1], False)
        jsqr(Zc_l[cell, 1], Zc_h[cell, 1], Bq[0], Bq[1], False)
        jadd(A[0], A[1], Bq[0], Bq[1], QCl[cell], QCh[cell], 1)
        refine(QCl[cell], QCh[cell], QBl[cell], QBh[cell], h, True)


@nb.njit(parallel=True)
def q_jets_batch(LO, HI):
    N = LO.shape[0]
    Cc = np.empty((N, 6))
    H = np.empty((N, 6))
    QCl = np.empty((N, 18, NJ))
    QCh = np.empty((N, 18, NJ))
    QBl = np.empty((N, 18, NJ))
    QBh = np.empty((N, 18, NJ))
    for n in nb.prange(N):
        q_jets_one(LO[n], HI[n], Cc[n], H[n], QCl[n], QCh[n], QBl[n], QBh[n])
    return Cc, H, QCl, QCh, QBl, QBh
