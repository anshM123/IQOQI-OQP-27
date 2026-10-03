"""
exact.py -- small exact-arithmetic toolkit used by all verification scripts of P2_literal_noise.

* Q2:  numbers a + b sqrt(2) with a, b rational (fractions.Fraction); exact field operations and exact sign.
* Poly: polynomials in one variable t with Q2 coefficients; exact evaluation; certified nonnegativity on an interval
        [lo, hi] (rational endpoints) by Bernstein coefficients with de Casteljau subdivision (a polynomial is >= 0
        on an interval if all its Bernstein coefficients there are >= 0).
* rigorous enclosures of pi and of sin(x) on rational intervals (alternating Taylor series), all in Fractions.
No floating point number is used for any decision.
"""
from fractions import Fraction as Fr
from math import comb


# ------------------------------------------------------------------------------------------------------------------
# Q(sqrt 2)
# ------------------------------------------------------------------------------------------------------------------
class Q2:
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    @staticmethod
    def c(x):
        return x if isinstance(x, Q2) else Q2(x, 0)

    @staticmethod
    def ok(x):
        return isinstance(x, (Q2, int, Fr))

    def __add__(self, o):
        if not Q2.ok(o):
            return NotImplemented
        o = Q2.c(o)
        return Q2(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.a, -self.b)

    def __sub__(self, o):
        if not Q2.ok(o):
            return NotImplemented
        return self + (-Q2.c(o))

    def __rsub__(self, o):
        if not Q2.ok(o):
            return NotImplemented
        return Q2.c(o) - self

    def __mul__(self, o):
        if not Q2.ok(o):
            return NotImplemented
        o = Q2.c(o)
        return Q2(self.a * o.a + 2 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def conj(self):
        return Q2(self.a, -self.b)

    def norm(self):
        return self.a * self.a - 2 * self.b * self.b

    def __truediv__(self, o):
        if not Q2.ok(o):
            return NotImplemented
        o = Q2.c(o)
        n = o.norm()
        if n == 0:
            raise ZeroDivisionError
        t = self * o.conj()
        return Q2(t.a / n, t.b / n)

    def __rtruediv__(self, o):
        if not Q2.ok(o):
            return NotImplemented
        return Q2.c(o) / self

    def sign(self):
        """exact sign of a + b sqrt2."""
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        # opposite signs: compare a^2 with 2 b^2
        if a > 0:          # b < 0
            return 1 if a * a > 2 * b * b else -1        # a^2 = 2b^2 impossible (sqrt2 irrational) unless both 0
        return 1 if 2 * b * b > a * a else -1

    def __eq__(self, o):
        o = Q2.c(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def __lt__(self, o):
        return (self - o).sign() < 0

    def __le__(self, o):
        return (self - o).sign() <= 0

    def __gt__(self, o):
        return (self - o).sign() > 0

    def __ge__(self, o):
        return (self - o).sign() >= 0

    def __float__(self):
        return float(self.a) + float(self.b) * 2 ** 0.5

    def __repr__(self):
        return f"({self.a} + {self.b}*sqrt2)"


SQRT2 = Q2(0, 1)


# ------------------------------------------------------------------------------------------------------------------
# polynomials with Q2 (or Fraction) coefficients
# ------------------------------------------------------------------------------------------------------------------
class Poly:
    """coefficients c[k] of t^k."""

    def __init__(self, coeffs):
        c = [Q2.c(x) for x in coeffs]
        while len(c) > 1 and c[-1] == Q2(0):
            c.pop()
        self.c = c if c else [Q2(0)]

    @staticmethod
    def const(x):
        return Poly([x])

    @staticmethod
    def t():
        return Poly([0, 1])

    def deg(self):
        return len(self.c) - 1

    def __add__(self, o):
        o = o if isinstance(o, Poly) else Poly.const(o)
        n = max(len(self.c), len(o.c))
        return Poly([(self.c[k] if k < len(self.c) else Q2(0)) + (o.c[k] if k < len(o.c) else Q2(0))
                     for k in range(n)])

    __radd__ = __add__

    def __neg__(self):
        return Poly([-x for x in self.c])

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Poly) else Poly.const(o)))

    def __rsub__(self, o):
        return Poly.const(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, Poly) else Poly.const(o)
        r = [Q2(0)] * (len(self.c) + len(o.c) - 1)
        for i, x in enumerate(self.c):
            for j, y in enumerate(o.c):
                r[i + j] = r[i + j] + x * y
        return Poly(r)

    __rmul__ = __mul__

    def __call__(self, t):
        r = Q2(0)
        for x in reversed(self.c):
            r = r * t + x
        return r

    def is_zero(self):
        return all(x == Q2(0) for x in self.c)

    def __repr__(self):
        return " + ".join(f"{x}*t^{k}" for k, x in enumerate(self.c))


def bernstein_coeffs(p, lo, hi):
    """Bernstein coefficients of p on [lo, hi] (exact)."""
    n = p.deg()
    # substitute t = lo + (hi - lo) s : coefficients in s
    lo, hi = Fr(lo), Fr(hi)
    w = hi - lo
    # q(s) = p(lo + w s)
    q = [Q2(0)] * (n + 1)
    for k, ck in enumerate(p.c):
        # (lo + w s)^k = sum_j C(k,j) lo^(k-j) w^j s^j
        for j in range(k + 1):
            q[j] = q[j] + ck * (comb(k, j) * lo ** (k - j) * w ** j)
    # power basis -> Bernstein: b_i = sum_{j<=i} C(i,j)/C(n,j) q_j
    return [sum((q[j] * Fr(comb(i, j), comb(n, j)) for j in range(i + 1)), Q2(0)) for i in range(n + 1)]


def certify_nonneg(p, lo, hi, depth=0, maxdepth=40):
    """True if p >= 0 on [lo, hi] is certified by Bernstein coefficients (with subdivision).  Returns
    (ok, number_of_boxes)."""
    if p.is_zero():
        return True, 1
    b = bernstein_coeffs(p, lo, hi)
    if all(x.sign() >= 0 for x in b):
        return True, 1
    # a negative endpoint value is a genuine counterexample
    if p(Fr(lo)).sign() < 0 or p(Fr(hi)).sign() < 0:
        return False, 1
    if depth >= maxdepth:
        return False, 1
    mid = (Fr(lo) + Fr(hi)) / 2
    ok1, n1 = certify_nonneg(p, lo, mid, depth + 1, maxdepth)
    if not ok1:
        return False, n1
    ok2, n2 = certify_nonneg(p, mid, hi, depth + 1, maxdepth)
    return ok2, n1 + n2


# ------------------------------------------------------------------------------------------------------------------
# rigorous enclosures of pi and sin (rational intervals)
# ------------------------------------------------------------------------------------------------------------------
def arctan_inv_bounds(n, terms=40):
    """bounds for arctan(1/n), n >= 2 integer: alternating series with decreasing terms."""
    x = Fr(1, n)
    s = Fr(0)
    partial = []
    for k in range(terms):
        s += (-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
        partial.append(s)
    # consecutive partial sums bracket the limit
    lo, hi = min(partial[-1], partial[-2]), max(partial[-1], partial[-2])
    return lo, hi


def pi_bounds(terms=40):
    """Machin: pi = 16 arctan(1/5) - 4 arctan(1/239)."""
    l5, h5 = arctan_inv_bounds(5, terms)
    l239, h239 = arctan_inv_bounds(239, terms)
    return 16 * l5 - 4 * h239, 16 * h5 - 4 * l239


PI_LO, PI_HI = pi_bounds()
assert Fr(314159265358979323846, 10 ** 20) < PI_LO < PI_HI < Fr(314159265358979323847, 10 ** 20)
assert PI_HI - PI_LO < Fr(1, 10 ** 50)


def sin_bounds_point(x, terms=30):
    """rigorous bounds of sin(x) for rational 0 <= x <= 2 (alternating series, decreasing terms)."""
    assert 0 <= x <= 2
    s = Fr(0)
    term = Fr(x)
    partial = []
    for k in range(terms):
        s += term
        partial.append(s)
        term = -term * x * x / ((2 * k + 2) * (2 * k + 3))
    return min(partial[-1], partial[-2]), max(partial[-1], partial[-2])


def sin_pi_frac_bounds(r):
    """rigorous bounds of sin(pi r) for rational r in [0, 1/2]: sin is increasing on [0, pi/2]."""
    r = Fr(r)
    assert 0 <= r <= Fr(1, 2)
    lo_x, hi_x = r * PI_LO, r * PI_HI
    lo, _ = sin_bounds_point(lo_x)
    if hi_x >= PI_LO / 2:
        # the argument interval may reach pi/2, where sin stops increasing: use the trivial upper bound 1
        hi = Fr(1)
    else:
        _, hi = sin_bounds_point(hi_x)
    return max(lo, Fr(0)), min(hi, Fr(1))


def sin2_pi_bounds(s):
    """rigorous bounds of sin^2(pi s) for any rational s."""
    s = Fr(s)
    s = s - (s.numerator // s.denominator)        # s in [0, 1)
    if s > Fr(1, 2):
        s = 1 - s                                  # sin^2(pi s) = sin^2(pi (1 - s))
    lo, hi = sin_pi_frac_bounds(s)
    return lo * lo, hi * hi


def cos_pi_frac_bounds(r):
    """cos(pi r) = sin(pi (1/2 - r)) for r in [0, 1/2]."""
    return sin_pi_frac_bounds(Fr(1, 2) - Fr(r))


if __name__ == "__main__":
    print("pi in", float(PI_LO), float(PI_HI))
    print("sin(pi/6) in", [float(t) for t in sin_pi_frac_bounds(Fr(1, 6))])
    x = Q2(3, -2)
    print(x, x.sign(), float(x))
    p = Poly([Q2(1), Q2(-2), Q2(1)])                  # (1 - t)^2
    print(certify_nonneg(p, 0, 2))
