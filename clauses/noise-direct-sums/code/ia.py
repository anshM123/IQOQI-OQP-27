"""ia.py -- minimal rigorous interval arithmetic on numpy float64 arrays (outward rounding by one ulp after every
correctly rounded IEEE operation; sums with the standard a-priori bound |fl(sum) - sum| <= gamma_{m} sum|x_i|).

Every IA object holds arrays lo <= hi with the guarantee that the exact real value lies in [lo, hi].
Only +, -, *, / (correctly rounded in IEEE 754 binary64) and comparisons are used; no libm functions.
"""
import numpy as np
from fractions import Fraction

U = 2.0 ** -53
NINF, PINF = -np.inf, np.inf


def dn(x):
    return np.nextafter(x, NINF)


def up(x):
    return np.nextafter(x, PINF)


class IA:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        lo = np.asarray(lo, dtype=np.float64)
        hi = lo if hi is None else np.asarray(hi, dtype=np.float64)
        self.lo, self.hi = lo, hi

    @staticmethod
    def exact(x):
        """x exactly representable (e.g. small integers)."""
        x = np.asarray(x, dtype=np.float64)
        return IA(x, x)

    @staticmethod
    def frac(fr):
        """enclosure of a rational number (Fraction or int)."""
        f = float(Fraction(fr))
        return IA(dn(f), up(f))

    def __getitem__(self, k):
        return IA(self.lo[k], self.hi[k])

    def __len__(self):
        return len(self.lo)

    def _c(self, o):
        if isinstance(o, IA):
            return o
        if isinstance(o, (int, np.integer)) or (isinstance(o, float) and float(o).is_integer() and abs(o) < 2 ** 52):
            return IA.exact(float(o))
        if isinstance(o, Fraction):
            return IA.frac(o)
        raise TypeError("pass non-integer constants as Fraction or IA")

    def __add__(self, o):
        o = self._c(o); return IA(dn(self.lo + o.lo), up(self.hi + o.hi))
    __radd__ = __add__

    def __neg__(self):
        return IA(-self.hi, -self.lo)

    def __sub__(self, o):
        o = self._c(o); return IA(dn(self.lo - o.hi), up(self.hi - o.lo))

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        p = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return IA(dn(np.minimum.reduce(p)), up(np.maximum.reduce(p)))
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._c(o)
        assert np.all((o.lo > 0) | (o.hi < 0)), "division by interval containing 0"
        p = [self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi]
        return IA(dn(np.minimum.reduce(p)), up(np.maximum.reduce(p)))

    def __rtruediv__(self, o):
        return self._c(o) / self

    def sq(self):
        a, b = np.abs(self.lo), np.abs(self.hi)
        M = np.maximum(a, b); m = np.minimum(a, b)
        mx = M * M
        mn = np.where((self.lo <= 0) & (self.hi >= 0), 0.0, m * m)
        return IA(dn(mn), up(mx))

    def cumsum(self):
        m = len(self.lo)
        k = np.arange(1, m + 1, dtype=np.float64)
        g = 2.0 * k * U                               # >= gamma_{k-1} (1 + gamma), valid for k*U << 1
        alo = up(np.cumsum(np.abs(self.lo))); ahi = up(np.cumsum(np.abs(self.hi)))
        tlo = up(up(g * alo) * (1 + 4 * U)); thi = up(up(g * ahi) * (1 + 4 * U))
        lo = dn(np.cumsum(self.lo) - tlo)
        hi = up(np.cumsum(self.hi) + thi)
        return IA(lo, hi)

    def sum(self):
        c = self.cumsum()
        return IA(c.lo[-1], c.hi[-1])

    def rcumsum(self):
        """reverse cumulative sums: out[i] = sum_{j >= i} x_j."""
        r = IA(self.lo[::-1].copy(), self.hi[::-1].copy()).cumsum()
        return IA(r.lo[::-1].copy(), r.hi[::-1].copy())

    def hull(self, o):
        return IA(np.minimum(self.lo, o.lo), np.maximum(self.hi, o.hi))

    def meet(self, o):
        lo, hi = np.maximum(self.lo, o.lo), np.minimum(self.hi, o.hi)
        assert np.all(lo <= hi), "empty intersection (bug)"
        return IA(lo, hi)


def concat(xs):
    return IA(np.concatenate([x.lo for x in xs]), np.concatenate([x.hi for x in xs]))


PI = IA(np.float64(3.141592653589793), up(np.float64(3.141592653589793)))   # fl(pi) < pi < next float


def sin_ia(th, J=12):
    """enclosure of sin(theta) for theta in [0, 2] given as IA (Taylor with alternating remainder bound)."""
    assert np.all(th.lo >= 0) and np.all(th.hi <= 2.0)
    x = th.sq()
    coef = [IA.frac(Fraction((-1) ** j, int(np.prod(np.arange(1, 2 * j + 2, dtype=object))))) for j in range(J + 1)]
    p = coef[J]
    for j in range(J - 1, -1, -1):
        p = coef[j] + x * p
    s = th * p
    # remainder |R| <= theta^(2J+3)/(2J+3)! (alternating series with decreasing terms since theta <= 2)
    fact = Fraction(1, int(np.prod(np.arange(1, 2 * J + 4, dtype=object))))
    t = IA(th.hi, th.hi); pw = t
    for _ in range(2 * J + 2):
        pw = pw * t                       # rigorous upper bound of theta_hi^(2J+3)
    R = (pw * IA(dn(float(fact)), up(float(fact)))).hi
    return IA(dn(s.lo - R), up(s.hi + R))
