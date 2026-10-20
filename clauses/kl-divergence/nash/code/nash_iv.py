"""Vectorised rigorous interval arithmetic on numpy float64 arrays (for nash_core.py).

An IV holds arrays lo <= hi.  Every operation rounds outward by one ulp with np.nextafter.  This is rigorous because
IEEE 754 binary64 +, -, *, / and sqrt are correctly rounded (round to nearest), so the exact result lies within half
an ulp of the computed one.  Transcendental functions are never taken from the C library:
  - log x: x = m 2^e (np.frexp, exact), m in [1/sqrt2, sqrt2), log m = 2 atanh(s), s = (m-1)/(m+1), |s| <= 0.1716,
    atanh series to s^21 plus the remainder bound |s|^23 / (23 (1 - s^2));
  - sin, cos of a float m: reduction m = k pi/2 + r with an interval enclosure of pi/2 (from python-flint arb), and
    Taylor series in r (|r| <= pi/4 + 1e-15) to degree 21 / 22 plus the Lagrange remainder |r|^23/23!.
Constants that are not floats (pi/2, log 2, sqrt 3, ...) enter as intervals computed once with mpmath's interval
arithmetic (mpmath.iv, directed rounding at 200 bits).
"""
import math
import numpy as np
from mpmath import iv, mp

iv.prec = 200
mp.prec = 200
_INF = np.inf


def dn(x):
    return np.nextafter(x, -_INF)


def up(x):
    return np.nextafter(x, _INF)


def _arb_iv(a):
    """float enclosure [lo, hi] of an mpmath interval (float() rounds to nearest, so step one ulp outward)."""
    a = iv.mpf(a)
    return dn(np.float64(float(a.a))), up(np.float64(float(a.b)))


class IV:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = np.asarray(lo, dtype=np.float64)
        self.hi = self.lo.copy() if hi is None else np.asarray(hi, dtype=np.float64)   # never alias lo and hi

    # ---------------------------------------------------------------- structure
    @property
    def shape(self):
        return self.lo.shape

    def __getitem__(self, k):
        return IV(self.lo[k], self.hi[k])

    def __setitem__(self, k, v):
        v = as_iv(v)
        self.lo[k] = v.lo
        self.hi[k] = v.hi

    def copy(self):
        return IV(self.lo.copy(), self.hi.copy())

    def reshape(self, *s):
        return IV(self.lo.reshape(*s), self.hi.reshape(*s))

    def mid(self):
        return 0.5 * (self.lo + self.hi)

    def rad(self):
        """upper bound for the radius about mid()."""
        m = self.mid()
        return up(np.maximum(up(self.hi - m), up(m - self.lo)))

    def mag(self):
        return np.maximum(np.abs(self.lo), np.abs(self.hi))

    # ---------------------------------------------------------------- arithmetic
    def __add__(self, o):
        o = as_iv(o)
        return IV(dn(self.lo + o.lo), up(self.hi + o.hi))

    __radd__ = __add__

    def __sub__(self, o):
        o = as_iv(o)
        return IV(dn(self.lo - o.hi), up(self.hi - o.lo))

    def __rsub__(self, o):
        return as_iv(o) - self

    def __neg__(self):
        return IV(-self.hi, -self.lo)

    def __mul__(self, o):
        o = as_iv(o)
        p1 = self.lo * o.lo
        p2 = self.lo * o.hi
        p3 = self.hi * o.lo
        p4 = self.hi * o.hi
        lo = np.minimum(np.minimum(p1, p2), np.minimum(p3, p4))
        hi = np.maximum(np.maximum(p1, p2), np.maximum(p3, p4))
        return IV(dn(lo), up(hi))

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = as_iv(o)
        if np.any(o.lo <= 0):
            raise ValueError("division by an interval that is not positive")
        p1 = self.lo / o.lo
        p2 = self.lo / o.hi
        p3 = self.hi / o.lo
        p4 = self.hi / o.hi
        lo = np.minimum(np.minimum(p1, p2), np.minimum(p3, p4))
        hi = np.maximum(np.maximum(p1, p2), np.maximum(p3, p4))
        return IV(dn(lo), up(hi))

    def sqr(self):
        l2 = self.lo * self.lo
        h2 = self.hi * self.hi
        pos = self.lo >= 0
        neg = self.hi <= 0
        lo = np.where(pos, l2, np.where(neg, h2, 0.0))
        hi = np.where(pos, h2, np.where(neg, l2, np.maximum(l2, h2)))
        return IV(np.maximum(dn(lo), 0.0), up(hi))

    def __repr__(self):
        return f"IV(lo={self.lo!r}, hi={self.hi!r})"


def as_iv(x):
    return x if isinstance(x, IV) else IV(x)


def hull(a, b):
    return IV(np.minimum(a.lo, b.lo), np.maximum(a.hi, b.hi))


def isum(a, axis):
    """rigorous sum along an axis: float sum plus the a-priori bound gamma_{n} sum|x| on its rounding error."""
    n = a.lo.shape[axis]
    g = (n + 2) * 2.0 ** -52
    slo = np.sum(a.lo, axis=axis)
    shi = np.sum(a.hi, axis=axis)
    elo = up(g * up(np.sum(np.abs(a.lo), axis=axis)) * 1.0001)
    ehi = up(g * up(np.sum(np.abs(a.hi), axis=axis)) * 1.0001)
    return IV(dn(slo - elo), up(shi + ehi))


def isqrt(a):
    if np.any(a.lo < 0):
        raise ValueError("sqrt of a negative interval")
    return IV(np.maximum(dn(np.sqrt(a.lo)), 0.0), up(np.sqrt(a.hi)))


def imax0(a):
    return IV(np.maximum(a.lo, 0.0), np.maximum(a.hi, 0.0))


# -------------------------------------------------------------------- constants (arb)
PI_HALF = IV(*_arb_iv(iv.pi / 2))
PI = IV(*_arb_iv(iv.pi))
LN2 = IV(*_arb_iv(iv.log(2)))
SQRT3 = IV(*_arb_iv(iv.sqrt(3)))


def const(a):
    """IV from an mpmath interval (or anything iv.mpf accepts)."""
    return IV(*_arb_iv(a))


def _inv_int(n):
    """interval enclosure of 1/n for a positive integer n (n may be huge)."""
    x = 1.0 / float(n) if n < 2 ** 1000 else 0.0
    return IV(dn(np.float64(x)), up(np.float64(x)))


_INV_FACT = [_inv_int(math.factorial(k)) for k in range(30)]
_INV_ODD = [_inv_int(2 * k + 1) for k in range(30)]


def _horner(t, coeffs):
    """sum_k coeffs[k] t^k (coeffs IV scalars), t an IV."""
    acc = coeffs[-1]
    for c in reversed(coeffs[:-1]):
        acc = acc * t + c
    return acc


# -------------------------------------------------------------------- log
_SQ2I = np.float64(0.7071067811865476)


def log_point(x):
    """rigorous enclosure of log(x) for a float array x > 0."""
    x = np.asarray(x, dtype=np.float64)
    if np.any(x <= 0):
        raise ValueError("log of a non-positive number")
    m, e = np.frexp(x)                        # x = m 2^e, m in [0.5, 1)
    small = m < _SQ2I
    m = np.where(small, 2.0 * m, m)           # exact
    e = np.where(small, e - 1, e).astype(np.float64)
    num = IV(m - 1.0)                         # exact (Sterbenz: m in [0.70, 1.42))
    den = IV(dn(m + 1.0), up(m + 1.0))
    s = num / den
    t = s.sqr()
    poly = _horner(t, _INV_ODD[:11])          # sum_{k<=10} t^k/(2k+1)
    val = 2.0 * (s * poly)
    sm = s.mag()
    rem = up(1.01 * up(up(2.0 * up(sm ** 23)) / up(23.0 * dn(1.0 - up(sm * sm)))))
    val = IV(dn(val.lo - rem), up(val.hi + rem))
    return IV(e) * LN2 + val


def log(a):
    """rigorous log of an interval with a.lo > 0 (log is increasing)."""
    a = as_iv(a)
    return IV(log_point(a.lo).lo, log_point(a.hi).hi)


# -------------------------------------------------------------------- sin / cos
_SIN_C = [(_INV_FACT[2 * k + 1] if k % 2 == 0 else -_INV_FACT[2 * k + 1]) for k in range(11)]   # sin(r)/r in r^2
_COS_C = [(_INV_FACT[2 * k] if k % 2 == 0 else -_INV_FACT[2 * k]) for k in range(12)]           # cos(r) in r^2


def sincos_point(x):
    """rigorous enclosures of sin(x), cos(x) for a float array x with |x| <= 1e3."""
    x = np.asarray(x, dtype=np.float64)
    k = np.rint(x / 1.5707963267948966)
    r = IV(x) - IV(k) * PI_HALF               # |r| <= pi/4 + tiny
    t = r.sqr()
    sr = r * _horner(t, _SIN_C)
    cr = _horner(t, _COS_C)
    rm = r.mag()
    rem_s = up(1.01 * up(up(rm ** 23) * _INV_FACT[23].hi))
    rem_c = up(1.01 * up(up(rm ** 24) * _INV_FACT[24].hi))
    sr = IV(dn(sr.lo - rem_s), up(sr.hi + rem_s))
    cr = IV(dn(cr.lo - rem_c), up(cr.hi + rem_c))
    q = np.mod(k, 4).astype(np.int64)
    # sin(x) = sin(r + q pi/2), cos(x) = cos(r + q pi/2)
    s_lo = np.select([q == 0, q == 1, q == 2, q == 3], [sr.lo, cr.lo, -sr.hi, -cr.hi])
    s_hi = np.select([q == 0, q == 1, q == 2, q == 3], [sr.hi, cr.hi, -sr.lo, -cr.lo])
    c_lo = np.select([q == 0, q == 1, q == 2, q == 3], [cr.lo, -sr.hi, -cr.hi, sr.lo])
    c_hi = np.select([q == 0, q == 1, q == 2, q == 3], [cr.hi, -sr.lo, -cr.lo, sr.hi])
    return (IV(np.maximum(s_lo, -1.0), np.minimum(s_hi, 1.0)),
            IV(np.maximum(c_lo, -1.0), np.minimum(c_hi, 1.0)))


def sincos(a):
    """rigorous enclosures of sin and cos over the interval a (Taylor about the midpoint, remainder r^2/2)."""
    a = as_iv(a)
    m = a.mid()
    r = a.rad()
    s, c = sincos_point(m)
    R = IV(-r, r)
    q = up(0.5 * up(r * r))
    Q = IV(-q, q)
    s2 = s + c * R + Q
    c2 = c - s * R + Q
    return (IV(np.maximum(s2.lo, -1.0), np.minimum(s2.hi, 1.0)),
            IV(np.maximum(c2.lo, -1.0), np.minimum(c2.hi, 1.0)))


# -------------------------------------------------------------------- symmetric matrices
def chol_pd(A):
    """A: IV of shape (N, n, n) (symmetric).  Returns a boolean array: True where the interval Cholesky succeeds,
    which proves that every symmetric matrix in A is positive definite."""
    N, n, _ = A.lo.shape
    L = IV(np.zeros((N, n, n)))
    ok = np.ones(N, dtype=bool)
    for j in range(n):
        s = A[:, j, j]
        for k in range(j):
            s = s - L[:, j, k].sqr()
        ok &= s.lo > 0
        s = IV(np.where(ok, s.lo, 1.0), np.where(ok, s.hi, 1.0))
        d = isqrt(s)
        L[:, j, j] = d
        for i in range(j + 1, n):
            v = A[:, i, j]
            for k in range(j):
                v = v - L[:, i, k] * L[:, j, k]
            L[:, i, j] = v / d
    return ok
