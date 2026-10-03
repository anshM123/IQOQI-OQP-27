"""
cyclo.py -- exact arithmetic in the cyclotomic field Q(zeta_N), zeta_N = exp(2 pi i / N).

Element = (tuple of Python ints of length phi(N), positive int denominator), power basis
1, z, ..., z^{phi-1}, reduced modulo the cyclotomic polynomial Phi_N (monic, integer).
Complex conjugation: z -> z^{-1}.  Numerical evaluation with mpmath.
"""
from math import gcd
from functools import lru_cache
import mpmath as mp


def cyclotomic_poly(N):
    """integer coefficients (low -> high) of Phi_N via x^N - 1 = prod_{d|N} Phi_d."""
    # polynomial division, exact integer
    def polydiv(a, b):
        a = list(a)
        q = [0] * (len(a) - len(b) + 1)
        for i in range(len(a) - len(b), -1, -1):
            c = a[i + len(b) - 1] // b[-1]
            q[i] = c
            for j in range(len(b)):
                a[i + j] -= c * b[j]
        assert all(v == 0 for v in a[:len(b) - 1])
        return q
    num = [-1] + [0] * (N - 1) + [1]
    for d in range(1, N):
        if N % d == 0:
            num = polydiv(num, cyclotomic_poly(d))
    return num


class Field:
    def __init__(self, N):
        self.N = N
        self.phi_poly = cyclotomic_poly(N)
        self.deg = len(self.phi_poly) - 1
        n = self.deg
        # reduction table: z^k for k in [0, 2n) as integer vectors
        red = []
        for k in range(2 * n):
            if k < n:
                v = [0] * n
                v[k] = 1
            else:
                # z^k = z * z^{k-1}
                prev = red[k - 1]
                v = [0] + prev[:-1]
                top = prev[-1]
                if top:
                    for j in range(n):
                        v[j] -= top * self.phi_poly[j]
            red.append(v)
        self.red = red
        # z^k for any k mod N
        self._pow = {}
        for k in range(N):
            self._pow[k] = self._power_vec(k)
        self.zero = (tuple([0] * n), 1)
        self.one = (tuple([1] + [0] * (n - 1)), 1)

    def _power_vec(self, k):
        n = self.deg
        k %= self.N
        v = [0] * n
        v[0] = 1
        base = [0] * n
        if n > 1:
            base[1] = 1
        else:
            base[0] = -self.phi_poly[0]
        e = (tuple(v), 1)
        b = (tuple(base), 1)
        for _ in range(k):
            e = self.mul(e, b)
        return e

    # --- constructors
    def z(self, k):
        return self._pow[k % self.N]

    def from_int(self, a, den=1):
        n = self.deg
        return self.norm((tuple([a] + [0] * (n - 1)), den))

    def from_frac(self, fr):
        return self.from_int(fr.numerator, fr.denominator)

    # --- normalisation
    def norm(self, x):
        v, den = x
        if den < 0:
            v = tuple(-a for a in v)
            den = -den
        g = den
        for a in v:
            g = gcd(g, a)
            if g == 1:
                break
        if g > 1:
            v = tuple(a // g for a in v)
            den //= g
        return (tuple(v), den)

    def is_zero(self, x):
        return all(a == 0 for a in x[0])

    def add(self, x, y):
        (a, da), (b, db) = x, y
        if da == db:
            return self.norm((tuple(p + q for p, q in zip(a, b)), da))
        return self.norm((tuple(p * db + q * da for p, q in zip(a, b)), da * db))

    def neg(self, x):
        return (tuple(-a for a in x[0]), x[1])

    def sub(self, x, y):
        return self.add(x, self.neg(y))

    def scal(self, x, num, den=1):
        return self.norm((tuple(a * num for a in x[0]), x[1] * den))

    def mul(self, x, y):
        (a, da), (b, db) = x, y
        n = self.deg
        prod = [0] * (2 * n - 1)
        for i, ai in enumerate(a):
            if ai == 0:
                continue
            for j, bj in enumerate(b):
                if bj:
                    prod[i + j] += ai * bj
        out = prod[:n]
        for k in range(n, 2 * n - 1):
            c = prod[k]
            if c:
                rv = self.red[k]
                for j in range(n):
                    if rv[j]:
                        out[j] += c * rv[j]
        return self.norm((tuple(out), da * db))

    def conj(self, x):
        a, da = x
        out = self.zero
        acc = [0] * self.deg
        for k, ak in enumerate(a):
            if ak:
                zv = self._pow[(-k) % self.N][0]
                for j in range(self.deg):
                    acc[j] += ak * zv[j]
        return self.norm((tuple(acc), da))

    def mul_matrix(self, x):
        """rational matrix (list of lists of Fractions) of multiplication by x in the power basis"""
        from fractions import Fraction
        n = self.deg
        cols = []
        for k in range(n):
            e = (tuple(1 if j == k else 0 for j in range(n)), 1)
            p = self.mul(x, e)
            cols.append([Fraction(v, p[1]) for v in p[0]])
        return [[cols[j][i] for j in range(n)] for i in range(n)]

    def inv(self, x):
        from fractions import Fraction
        assert not self.is_zero(x), "division by zero"
        M = self.mul_matrix(x)
        n = self.deg
        # solve M y = e0
        A = [row[:] + [Fraction(1 if i == 0 else 0)] for i, row in enumerate(M)]
        for c in range(n):
            p = next(r for r in range(c, n) if A[r][c] != 0)
            A[c], A[p] = A[p], A[c]
            pv = A[c][c]
            A[c] = [v / pv for v in A[c]]
            for r in range(n):
                if r != c and A[r][c] != 0:
                    f = A[r][c]
                    A[r] = [vr - f * vc for vr, vc in zip(A[r], A[c])]
        ys = [A[i][n] for i in range(n)]
        den = 1
        for yv in ys:
            den = den * yv.denominator // gcd(den, yv.denominator)
        return self.norm((tuple(int(yv * den) for yv in ys), den))

    def div(self, x, y):
        return self.mul(x, self.inv(y))

    def re(self, x):
        return self.scal(self.add(x, self.conj(x)), 1, 2)

    def im(self, x):
        # (x - conj x)/(2i) ; i = z^{N/4}
        assert self.N % 4 == 0
        mi = self.z(3 * self.N // 4)  # -i = 1/i
        return self.scal(self.mul(self.sub(x, self.conj(x)), mi), 1, 2)

    def i_unit(self):
        assert self.N % 4 == 0
        return self.z(self.N // 4)

    def to_complex(self, x, dps=50):
        with mp.workdps(dps):
            a, da = x
            s = mp.mpc(0)
            for k, ak in enumerate(a):
                if ak:
                    s += ak * mp.expjpi(mp.mpf(2 * k) / self.N)
            return s / da

    def to_cfloat(self, x):
        """float approximation (non-rigorous; diagnostics only).  Each power-basis coefficient is converted by exact
        rational scaling ak/da (Python int true division: correctly rounded, no intermediate overflow even when ak
        and da have thousands of bits); if a coefficient itself exceeds the float range, fall back to mpmath."""
        a, da = x
        roots = self.__dict__.get("_roots_c")
        if roots is None:
            import cmath
            roots = [cmath.exp(2j * cmath.pi * k / self.N) for k in range(self.deg)]
            self._roots_c = roots
        try:
            s = 0j
            for k, ak in enumerate(a):
                if ak:
                    s += (ak / da) * roots[k]
            return s
        except OverflowError:
            v = self.to_complex(x, 40)
            return complex(float(v.real), float(v.imag))

    def is_real(self, x):
        return self.is_zero(self.sub(x, self.conj(x)))

    def from_gaussian_rational(self, re_fr, im_fr):
        """element re + i*im with Fractions re, im"""
        from fractions import Fraction
        a = self.from_frac(Fraction(re_fr))
        b = self.mul(self.from_frac(Fraction(im_fr)), self.i_unit())
        return self.add(a, b)


if __name__ == "__main__":
    import cmath
    for N in (12, 16, 20, 24):
        F = Field(N)
        x = F.add(F.z(1), F.from_int(3, 2))
        y = F.sub(F.z(5), F.z(N - 2))
        p = F.mul(x, y)
        err = abs(F.to_cfloat(p) - F.to_cfloat(x) * F.to_cfloat(y))
        q = F.div(x, y)
        err2 = abs(F.to_cfloat(q) - F.to_cfloat(x) / F.to_cfloat(y))
        err3 = abs(F.to_cfloat(F.conj(x)) - F.to_cfloat(x).conjugate())
        err4 = abs(F.to_cfloat(F.re(y)) - F.to_cfloat(y).real) + abs(F.to_cfloat(F.im(y)) - F.to_cfloat(y).imag)
        print(N, F.deg, F.phi_poly, f"{err:.1e} {err2:.1e} {err3:.1e} {err4:.1e}")
