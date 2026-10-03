"""
cyc12.py -- exact arithmetic in the cyclotomic field Q(zeta), zeta = exp(i pi/6) (12th root of unity), and in its
real subfield Q(sqrt3).  Elements of Q(zeta): c0 + c1 zeta + c2 zeta^2 + c3 zeta^3 (Fractions), zeta^4 = zeta^2 - 1.
Real elements satisfy c2 = 0, c3 = -c1/2 and equal c0 + (c1/2) sqrt3.
"""
from fractions import Fraction as Fr
from mpmath import iv


def _reduce(d):
    d = list(d) + [Fr(0)] * (7 - len(d))
    for k in range(6, 3, -1):            # zeta^k = zeta^(k-2) - zeta^(k-4)
        if d[k]:
            d[k - 2] += d[k]
            d[k - 4] -= d[k]
            d[k] = Fr(0)
    return tuple(d[:4])


class Z12:
    __slots__ = ("c",)

    def __init__(self, c=(0, 0, 0, 0)):
        self.c = tuple(Fr(x) for x in c)

    @staticmethod
    def zp(k):
        return _ZP[k % 12]

    def __add__(self, o):
        o = _lift(o)
        return Z12(tuple(a + b for a, b in zip(self.c, o.c)))

    __radd__ = __add__

    def __neg__(self):
        return Z12(tuple(-a for a in self.c))

    def __sub__(self, o):
        return self + (-_lift(o))

    def __rsub__(self, o):
        return _lift(o) - self

    def __mul__(self, o):
        o = _lift(o)
        d = [Fr(0)] * 7
        for i, a in enumerate(self.c):
            if a:
                for j, b in enumerate(o.c):
                    if b:
                        d[i + j] += a * b
        return Z12(_reduce(d))

    __rmul__ = __mul__

    def conj(self):
        out = Z12()
        for k, a in enumerate(self.c):
            if a:
                out = out + _ZP[(12 - k) % 12] * a
        return out

    def re(self):
        return (self + self.conj()) * Fr(1, 2)

    def im(self):
        return (self - self.conj()) * Z12((0, 0, 0, Fr(-1, 2)))     # times -i/2  (zeta^3 = i)

    def is_zero(self):
        return all(a == 0 for a in self.c)

    def __eq__(self, o):
        return (self - _lift(o)).is_zero()

    def real_q3(self):
        """for a real element: (a, b) with value a + b sqrt3"""
        c0, c1, c2, c3 = self.c
        assert c2 == 0 and c3 == -c1 / 2, "not real"
        return Q3(c0, c1 / 2)

    def to_complex(self):
        import cmath
        z = cmath.exp(1j * cmath.pi / 6)
        return sum(float(a) * z ** k for k, a in enumerate(self.c))


def _lift(o):
    if isinstance(o, Z12):
        return o
    return Z12((o, 0, 0, 0))


_ZP = []
for _k in range(12):
    d = [Fr(0)] * 12
    d[_k] = Fr(1)
    # reduce zeta^k with zeta^6 = -1 first
    if _k >= 6:
        d = [Fr(0)] * 12
        d[_k - 6] = Fr(-1)
    _ZP.append(Z12(_reduce(d[:7])))
ZETA = _ZP[1]
I_ = _ZP[3]


class Q3:
    """a + b sqrt3, exact field arithmetic"""
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(self, o):
        o = q3(o)
        return Q3(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q3(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-q3(o))

    def __rsub__(self, o):
        return q3(o) - self

    def __mul__(self, o):
        o = q3(o)
        return Q3(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def inv(self):
        n = self.a * self.a - 3 * self.b * self.b
        assert n != 0
        return Q3(self.a / n, -self.b / n)

    def __truediv__(self, o):
        return self * q3(o).inv()

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def __eq__(self, o):
        return (self - q3(o)).is_zero()

    def sign(self):
        """exact sign of a + b sqrt3"""
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        # opposite signs: compare a^2 and 3 b^2
        if a > 0:          # b < 0
            return 1 if a * a > 3 * b * b else -1
        return 1 if 3 * b * b > a * a else -1

    def iv(self):
        return iv.mpf(self.a.numerator) / self.a.denominator + \
            iv.mpf(self.b.numerator) / self.b.denominator * iv.sqrt(iv.mpf(3))

    def __float__(self):
        return float(self.a) + float(self.b) * 3 ** 0.5

    def __repr__(self):
        return f"({self.a} + {self.b} sqrt3)"


def q3(o):
    return o if isinstance(o, Q3) else Q3(o, 0)


if __name__ == "__main__":
    import cmath
    z = cmath.exp(1j * cmath.pi / 6)
    for k in range(12):
        assert abs(_ZP[k].to_complex() - z ** k) < 1e-12
    s3 = ZETA * 2 - _ZP[3]
    assert s3.real_q3() == Q3(0, 1)
    x = Z12((Fr(1, 3), 2, -1, Fr(5, 7)))
    y = Z12((2, Fr(-1, 2), 3, 1))
    assert abs((x * y).to_complex() - x.to_complex() * y.to_complex()) < 1e-12
    assert abs(x.conj().to_complex() - x.to_complex().conjugate()) < 1e-12
    assert abs(float(x.re().real_q3()) - x.to_complex().real) < 1e-12
    assert abs(float(x.im().real_q3()) - x.to_complex().imag) < 1e-12
    print("cyc12 self-test passed")
