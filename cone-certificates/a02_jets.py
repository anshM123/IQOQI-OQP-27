"""a02: interval Taylor jets in one or two variables (mpmath.iv), used by the all-d proof (CONE_ALLD_PROOF.md).
A jet J over a box encloses the normalized derivatives  J[i,j] ~ d^i/dx^i d^j/dy^j f / (i! j!)  at EVERY point of the box
(interval AD in the mean-value sense).  Every operation below maps enclosures to enclosures because the corresponding formula
(Leibniz, Faa di Bruno) holds pointwise.  Index set: i <= n0, j <= n1, i + j <= T."""
import math
from fractions import Fraction
import mpmath
from mpmath import iv

iv.prec = 120
Z = iv.mpf(0)
ONE = iv.mpf(1)
_FZ = Z._mpi_[0]


# ---------------------------------------------------------------- exact integers / rationals -> outward-rounded intervals (G6)
# iv.mpf(int) rounds the two endpoints outward (floor / ceiling at iv.prec), so it always CONTAINS the integer; an integer
# must never pass through an mpmath.mpf (53 bits by default) first.  test_exact.py checks every helper below.
def ivq(q):
    """interval containing the exact rational q (int, Fraction, or a decimal string such as '8.38')."""
    if isinstance(q, bool):
        raise TypeError(q)
    if isinstance(q, int):
        return iv.mpf(q)
    if isinstance(q, str):
        q = Fraction(q)
    if isinstance(q, Fraction):
        if q.denominator == 1:
            return iv.mpf(q.numerator)
        return iv.mpf(q.numerator) / iv.mpf(q.denominator)
    raise TypeError(f"ivq: exact int/Fraction/str expected, got {type(q)}")


def ivfact(n):
    return iv.mpf(math.factorial(n))


def ivbinom(n, k):
    return iv.mpf(math.comb(n, k))


def ivff(n, k):
    """falling factorial n (n-1) ... (n-k+1) = n!/(n-k)!  (k <= n), exact."""
    return iv.mpf(math.perm(n, k))


def lah(c, i):
    """unsigned Lah number L(c, i) = C(c-1, i-1) c!/i!  (exact integer)."""
    return math.comb(c - 1, i - 1) * math.factorial(c) // math.factorial(i)


def _raw_to_fraction(t):
    sign, man, exp, bc = t
    if man == 0:
        if t == mpmath.libmp.fzero:
            return Fraction(0)
        raise ValueError("non-finite interval endpoint")
    v = Fraction(int(man)) * (Fraction(2) ** exp)
    return -v if sign else v


def lo_frac(v):
    """exact lower endpoint of an interval (or a number) as a Fraction."""
    v = iv.mpf(v) if not hasattr(v, '_mpi_') else v
    return _raw_to_fraction(v._mpi_[0])


def hi_frac(v):
    v = iv.mpf(v) if not hasattr(v, '_mpi_') else v
    return _raw_to_fraction(v._mpi_[1])


def lo_str(v):
    """exact lower endpoint as a string 'p/q' (for JSON; read back with fractions.Fraction)."""
    return str(lo_frac(v))


def hi_str(v):
    return str(hi_frac(v))


def grid_boxes(lo, hi, nb):
    """nb boxes covering the exact rational interval [lo, hi] (lo, hi: decimal strings / Fractions): box k is the hull
    [ivq(p_k).a, ivq(p_{k+1}).b] of the exact grid points p_k = lo + (hi - lo) k/nb, as thin-interval endpoints (a, b).
    Consecutive boxes overlap by the rounding width, so their union contains [lo, hi] exactly (checked by the audit)."""
    lo, hi = Fraction(lo), Fraction(hi)
    pts = [lo + (hi - lo) * k / nb for k in range(nb + 1)]
    return [(ivq(pts[k]).a, ivq(pts[k + 1]).b) for k in range(nb)]


def thin_frac(t):
    """exact value of a thin interval endpoint (as returned by .a / .b) as a Fraction."""
    lo, hi = t._mpi_
    assert lo == hi
    return _raw_to_fraction(lo)


def mpf_frac(x):
    """exact value of an mpmath.mpf / float / int as a Fraction."""
    if isinstance(x, (int, Fraction)):
        return Fraction(x)
    if isinstance(x, float):
        return Fraction(x)
    if hasattr(x, '_mpf_'):
        return _raw_to_fraction(x._mpf_)          # no re-rounding
    raise TypeError(f"mpf_frac: {type(x)}")


def nz(v):
    """map an exact zero interval to the shared sentinel Z (so products can skip it)."""
    m = v._mpi_
    return Z if (m[0] == _FZ and m[1] == _FZ) else v


class Space:
    _cache = {}

    def __new__(cls, n0, n1, T):
        key = (n0, n1, T)
        if key in cls._cache:
            return cls._cache[key]
        s = super().__new__(cls)
        s.n0, s.n1, s.T = n0, n1, T
        s.idx = [(i, j) for j in range(n1 + 1) for i in range(n0 + 1) if i + j <= T]
        s.pos = {p: k for k, p in enumerate(s.idx)}
        s.N = len(s.idx)
        # multiplication table: for each pair (ka, kb) the output index (or skip)
        s.mt = [[s.pos.get((a[0] + b[0], a[1] + b[1])) for b in s.idx] for a in s.idx]
        cls._cache[key] = s
        return s


class Jet:
    __slots__ = ('S', 'c')

    def __init__(self, S, c=None):
        self.S = S
        self.c = c if c is not None else [Z] * S.N

    @staticmethod
    def const(S, v):
        J = Jet(S)
        J.c[0] = iv.mpf(v) if not isinstance(v, type(Z)) else v
        return J

    @staticmethod
    def var(S, k, box):
        """independent variable number k (0 or 1) ranging over the interval box."""
        J = Jet.const(S, box)
        p = (1, 0) if k == 0 else (0, 1)
        if p in S.pos:
            J.c[S.pos[p]] = ONE
        return J

    def copy(self):
        return Jet(self.S, list(self.c))

    def __add__(self, o):
        if isinstance(o, Jet):
            return Jet(self.S, [a + b for a, b in zip(self.c, o.c)])
        J = self.copy(); J.c[0] = J.c[0] + o; return J
    __radd__ = __add__

    def __neg__(self):
        return Jet(self.S, [-a for a in self.c])

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, Jet):
            return Jet(self.S, [a * o for a in self.c])
        S = self.S
        out = [Z] * S.N
        ca, cb, mt = self.c, o.c, S.mt
        nzb = [k for k, v in enumerate(cb) if v is not Z]
        for ka, va in enumerate(ca):
            if va is Z:
                continue
            row = mt[ka]
            for kb in nzb:
                ko = row[kb]
                if ko is not None:
                    out[ko] = out[ko] + va * cb[kb]
        return Jet(S, [nz(v) if v is not Z else v for v in out])
    __rmul__ = __mul__

    def recip(self):
        """1/J by the recursion sum_{a+b=k} J_a R_b = delta_k0 (holds pointwise)."""
        S = self.S
        R = [Z] * S.N
        inv0 = ONE / self.c[0]
        R[0] = inv0
        for k in range(1, S.N):
            i, j = S.idx[k]
            acc = Z
            for (a, b) in S.idx:
                if (a, b) == (0, 0) or a > i or b > j:
                    continue
                kk = S.pos.get((i - a, j - b))
                if kk is not None:
                    acc = acc + self.c[S.pos[(a, b)]] * R[kk]
            R[k] = nz(-acc * inv0) if acc is not Z else Z
        return Jet(S, R)

    def __truediv__(self, o):
        if isinstance(o, Jet):
            return self * o.recip()
        return self * (ONE / o)

    def __rtruediv__(self, o):
        return self.recip() * o

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        R = Jet.const(self.S, ONE)
        B = self
        while n:
            if n & 1:
                R = R * B
            n >>= 1
            if n:
                B = B * B
        return R

    def nil(self):
        """the jet minus its constant term (nilpotent part)."""
        J = self.copy(); J.c[0] = Z; return J

    def compose1(self, F):
        """f(J) for a univariate f, given F[k] = enclosure of f^(k)/k! over the range of J (k = 0..T)."""
        N = self.nil()
        out = Jet.const(self.S, F[0])
        P = None
        for k in range(1, self.S.T + 1):
            P = N if P is None else P * N
            out = out + P * F[k]
        return out

    def __getitem__(self, ij):
        return self.c[self.S.pos[ij]] if ij in self.S.pos else None


def compose2(G, X, E):
    """G(X, E): G is a jet in variables (u0, u1) whose coefficients enclose the derivatives of g over a box containing the range
    of (X, E); X, E are jets in a common target space.  Returns sum_{a,c} G[a,c] (X - X0)^a (E - E0)^c (Faa di Bruno)."""
    S = X.S
    NX, NE = X.nil(), E.nil()
    powX = [Jet.const(S, ONE)]
    powE = [Jet.const(S, ONE)]
    for k in range(1, S.T + 1):
        powX.append(powX[-1] * NX)
        powE.append(powE[-1] * NE)
    out = Jet(S)
    for (a, c) in G.S.idx:
        if a + c > S.T:
            continue
        g = G.c[G.S.pos[(a, c)]]
        if g is Z:
            continue
        out = out + (powX[a] * powE[c]) * g
    return out
