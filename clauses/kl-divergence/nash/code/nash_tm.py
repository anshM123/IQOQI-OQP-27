"""Taylor models of degree 3 in 6 variables with a homogeneous quartic remainder (vectorised over boxes).

On a box x = c + h*s, s in [-1, 1]^6, a Taylor model (TM) of a function F is a polynomial P(s) of degree <= 3 with
interval coefficients (tight enclosures of the Taylor coefficients at s = 0, up to rounding) and a number K >= 0 with
      F(c + h*s) - P(s) in [-K |s|_inf^4, K |s|_inf^4]   for all |s|_inf <= 1.
Operations (all rigorous, outward rounding):
  sum, scalar product;
  product: the terms of degree <= 3 are kept; the dropped terms of degree 4..6 are bounded by
      sum_{d1 + d2 >= 4} B_d1(P) B_d2(Q) |s|^4,  B_d = sum of |coefficients| of degree d,
    and the remainder terms by K_P |Q| + K_Q |P| + K_P K_Q (|P| <= sum of all |coefficients|);
  univariate f(u): f(u0 + d) = sum_{k<=3} f^(k)(u0) d^k / k! + f''''(xi) d^4 / 24, with |d(s)| <= B |s|_inf.
Because coefficients are computed at the centre, there is no interval dependency at orders <= 3.
"""
import itertools
import math
import numpy as np

import nash_iv as V
from nash_iv import IV

NV = 6
MONO = [m for d in range(4) for m in sorted(set(
    tuple(sum(1 for v in c if v == k) for k in range(NV)) for c in itertools.combinations_with_replacement(range(NV), d)),
    reverse=True)]
NM = len(MONO)                                   # 84
DEG = np.array([sum(m) for m in MONO])
MIDX = {m: i for i, m in enumerate(MONO)}
E1 = [MIDX[tuple(1 if k == i else 0 for k in range(NV))] for i in range(NV)]


def _pairs():
    pa, pb, pt = [], [], []
    for a, ma in enumerate(MONO):
        for b, mb in enumerate(MONO):
            if DEG[a] + DEG[b] <= 3:
                pa.append(a)
                pb.append(b)
                pt.append(MIDX[tuple(x + y for x, y in zip(ma, mb))])
    return np.array(pa), np.array(pb), np.array(pt)


PA, PB, PT = _pairs()
# gather layout: for each target monomial, the list of pair indices (padded with a dummy pair index pointing to 0)
_lists = [np.nonzero(PT == t)[0] for t in range(NM)]
_L = max(len(l) for l in _lists)
GATHER = np.full((NM, _L), len(PA), dtype=int)
for t, l in enumerate(_lists):
    GATHER[t, :len(l)] = l
DEGMASK = [(DEG == d).astype(float) for d in range(4)]


class TM:
    __slots__ = ("c", "K")

    def __init__(self, c, K):
        self.c = c                      # IV (N, NM)
        self.K = np.asarray(K, float)   # (N,)

    def __add__(self, o):
        if isinstance(o, TM):
            return TM(self.c + o.c, V.up(self.K + o.K))
        o = V.as_iv(o)
        c = self.c.copy()
        c[:, 0] = c[:, 0] + o
        return TM(c, self.K)

    __radd__ = __add__

    def __neg__(self):
        return TM(-self.c, self.K)

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def scale(self, a):
        """multiply by an IV scalar (shape () or (N,))."""
        a = V.as_iv(a)
        aa = a if a.lo.ndim == 0 else a[:, None]
        return TM(self.c * aa, V.up(self.K * a.mag()))

    def degsums(self):
        m = self.c.mag()
        return [V.up(np.sum(m * DEGMASK[d], axis=1) * (1 + 1e-12)) for d in range(4)]

    def pbound(self):
        """sup over the unit box of |P(s)| (upper bound, polynomial part only)."""
        return V.up(np.sum(self.c.mag(), axis=1) * (1 + 1e-12))

    def bound(self):
        """sup over the unit box of |P(s)| + K (upper bound)."""
        return V.up(self.pbound() + self.K)

    def __mul__(self, o):
        if not isinstance(o, TM):
            return self.scale(o)
        N = self.c.lo.shape[0]
        pr = self.c[:, PA] * o.c[:, PB]                            # (N, npairs)
        prl = np.concatenate([pr.lo, np.zeros((N, 1))], axis=1)
        prh = np.concatenate([pr.hi, np.zeros((N, 1))], axis=1)
        c = V.isum(IV(prl[:, GATHER], prh[:, GATHER]), axis=2)    # (N, NM)
        bp, bq = self.degsums(), o.degsums()
        drop = np.zeros(N)
        for d1 in range(4):
            for d2 in range(4):
                if d1 + d2 >= 4:
                    drop = drop + V.up(bp[d1] * bq[d2])
        BP = self.pbound()
        BQ = o.pbound()
        K = V.up(V.up(drop * (1 + 1e-12)) + V.up(self.K * BQ) + V.up(o.K * BP) + V.up(self.K * o.K))
        return TM(c, V.up(K * (1 + 1e-12)))

    def range(self):
        """interval enclosure over the unit box."""
        r = V.up(np.sum(self.c.mag()[:, 1:], axis=1) * (1 + 1e-12) + self.K)
        return self.c[:, 0] + IV(-r, r)


def const(v, N):
    v = V.as_iv(v)
    c = IV(np.zeros((N, NM)))
    c[:, 0] = v if v.lo.ndim else IV(np.full(N, float(v.lo)), np.full(N, float(v.hi)))
    return TM(c, np.zeros(N))


def coord(k, centre, h):
    """the TM of x_k = c_k + h_k s_k (centre may be an IV)."""
    N = h.shape[0]
    c = IV(np.zeros((N, NM)))
    c[:, 0] = V.as_iv(centre)
    c[:, E1[k]] = IV(h)
    return TM(c, np.zeros(N))


def univariate(u, derivs):
    """f(u) for a TM u; derivs(lo_iv_of_u0, range_iv) -> (f0, f1, f2, f3 at u0 (IV (N,)), sup|f4| over range (N,))."""
    N = u.c.lo.shape[0]
    u0 = u.c[:, 0]
    d = TM(u.c.copy(), u.K)
    d.c[:, 0] = IV(np.zeros(N))
    B = d.bound()                                                   # |d(s)| <= B |s|_inf
    rng = u0 + IV(-B, B)
    f0, f1, f2, f3, f4sup = derivs(u0, rng)
    d2 = d * d
    d3 = d2 * d
    out = const(f0, N) + d.scale(f1) + d2.scale(f2 * 0.5) + d3.scale(f3 * _SIXTH)
    rem = V.up(f4sup * V.up(B ** 4) / 24.0 * (1 + 1e-9))
    return TM(out.c, V.up(out.K + rem))


_SIXTH = V.const(V.iv.mpf(1) / 6)


def _inv_sqrt_derivs(u0, rng):
    if np.any(rng.lo <= 0):
        raise ValueError("inv_sqrt of a non-positive range")
    s0 = V.isqrt(u0)
    f0 = IV(1.0) / s0
    f1 = (f0 / u0) * (-0.5)
    f2 = (f1 / u0) * (-1.5)
    f3 = (f2 / u0) * (-2.5)
    lo = rng.lo
    f4 = V.up((105.0 / 16.0) * V.up(1.0 / V.dn(np.sqrt(lo) * lo ** 4)) * (1 + 1e-9))   # sup |f4| = (105/16) lo^(-9/2)
    return f0, f1, f2, f3, f4


def _log_derivs(u0, rng):
    if np.any(rng.lo <= 0):
        raise ValueError("log of a non-positive range")
    f0 = V.log(u0)
    r = IV(1.0) / u0
    f1 = r
    f2 = -(r * r)
    f3 = (r * r * r) * 2.0
    f4 = V.up(6.0 / V.dn(rng.lo ** 4) * (1 + 1e-9))
    return f0, f1, f2, f3, f4


def inv_sqrt(u):
    return univariate(u, _inv_sqrt_derivs)


def log(u):
    return univariate(u, _log_derivs)


def sincos_coord(k, centre, h):
    """TMs of sin(x_k), cos(x_k) for x_k = c_k + h_k s_k (exact Taylor polynomials, remainder h^4/24)."""
    N = h.shape[0]
    s, c = V.sincos_point(centre) if not isinstance(centre, IV) else V.sincos(centre)
    hh = IV(h)
    cs = IV(np.zeros((N, NM)))
    cc = IV(np.zeros((N, NM)))
    i1 = E1[k]
    i2 = MIDX[tuple(2 if j == k else 0 for j in range(NV))]
    i3 = MIDX[tuple(3 if j == k else 0 for j in range(NV))]
    h2 = hh.sqr()
    h3 = h2 * hh
    cs[:, 0] = s
    cs[:, i1] = c * hh
    cs[:, i2] = -(s * h2) * 0.5
    cs[:, i3] = -(c * h3) * _SIXTH
    cc[:, 0] = c
    cc[:, i1] = -(s * hh)
    cc[:, i2] = -(c * h2) * 0.5
    cc[:, i3] = (s * h3) * _SIXTH
    rem = V.up(V.up(h ** 4) / 24.0 * (1 + 1e-9))
    return TM(cs, rem), TM(cc, rem.copy())


class CTM:
    __slots__ = ("re", "im")

    def __init__(self, re, im):
        self.re, self.im = re, im

    def __add__(self, o):
        if isinstance(o, TM):
            return CTM(self.re + o, self.im)
        return CTM(self.re + o.re, self.im + o.im)

    def __sub__(self, o):
        if isinstance(o, TM):
            return CTM(self.re - o, self.im)
        return CTM(self.re - o.re, self.im - o.im)

    def __neg__(self):
        return CTM(-self.re, -self.im)

    def __mul__(self, o):
        if isinstance(o, TM):
            return CTM(self.re * o, self.im * o)
        return CTM(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def scale(self, a_re, a_im):
        """multiply by the complex constant a_re + i a_im (IV scalars)."""
        return CTM(self.re.scale(a_re) - self.im.scale(a_im), self.re.scale(a_im) + self.im.scale(a_re))

    def conj(self):
        return CTM(self.re, -self.im)

    def abs2(self):
        return self.re * self.re + self.im * self.im
