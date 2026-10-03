"""
Stand-alone verifier for certificates/dkz_d{d}.json  (does not import the generator).

For each certificate (d, v, W) it checks, in exact rational arithmetic:
  (1) every support point k = (k00,k01,k10,k11) satisfies k00 + k11 = k01 + k10 (mod d), every weight is >= 0,
      t = sum W < 1;
  (2) for every link xy and n in Z_d:   v * flo_xy(n) + (1-v)/d - (AW)_xy(n) - (1-t)/(2d) >= 0,
      where flo_xy(n) is a rigorous LOWER bound of f_xy(n) = 1/(2 d^2 sin^2(pi (n - alpha_x - beta_y)/d)),
      computed twice, independently:
        (a) mpmath interval arithmetic (mpmath.iv, 60 digits);
        (b) Fractions: pi enclosed by its first 50 decimals, sin by alternating Taylor partial sums;
  (3) v > v_thr(d) (competitor threshold) EXACTLY: v_thr = a + b sqrt2 with rational a, b; sign test by squaring.
Conclusion printed per d:  v_c(DKZ_d) >= v > v_thr(d) >= v_c(competitor_d).

Run: python verify_dkz_certificates.py
"""
import os
import json
import glob
from fractions import Fraction as Fr
import mpmath

HERE = os.path.dirname(os.path.abspath(__file__))
ALPHA = (Fr(0), Fr(1, 2))
BETA = (Fr(1, 4), Fr(-1, 4))
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]

# pi = 3.14159265358979323846264338327950288419716939937510 58209... (first 50 decimals)
PI_LO = Fr('3.14159265358979323846264338327950288419716939937510')
PI_HI = PI_LO + Fr(1, 10 ** 50)


def raw_to_frac(t):
    """mpmath raw mpf tuple (sign, man, exp, bc) -> exact Fraction"""
    sign, man, exp, bc = t
    v = Fr(int(man)) * (Fr(2) ** exp if exp >= 0 else Fr(1, 2 ** (-exp)))
    return -v if sign else v


def flo_iv(d):
    mpmath.iv.dps = 60
    out = {}
    for x, y in LINKS:
        g = ALPHA[x] + BETA[y]
        for n in range(d):
            r = (n - g) / d
            arg = mpmath.iv.pi * mpmath.iv.mpf(r.numerator) / r.denominator
            s = mpmath.iv.sin(arg)
            val = 1 / (2 * d * d * s * s)
            lo = raw_to_frac(val._mpi_[0])     # exact binary rational: lower endpoint of the enclosure
            hi = raw_to_frac(val._mpi_[1])
            assert 0 < lo <= hi and hi - lo < Fr(1, 10 ** 50)
            out[(x, y, n)] = lo
    return out


def sin_upper(x):
    """upper bound of sin(x), 0 < x <= 2 (alternating series, decreasing terms): partial sum ending with + term"""
    s, term, j = Fr(0), x, 0
    while True:
        s += term if j % 2 == 0 else -term
        nxt = term * x * x / ((2 * j + 2) * (2 * j + 3))
        if j % 2 == 0 and nxt < Fr(1, 10 ** 45):
            return s                  # last term added was positive -> upper bound
        term, j = nxt, j + 1


def flo_frac(d):
    out = {}
    for x, y in LINKS:
        g = ALPHA[x] + BETA[y]
        for n in range(d):
            r = (n - g) / d
            r = r - (r.numerator // r.denominator)
            if r > Fr(1, 2):
                r = 1 - r
            assert 0 < r < Fr(1, 2)
            xh = r * PI_HI
            assert xh < PI_LO / 2     # sin increasing on [0, pi/2] -> sin(pi r) <= sin(r PI_HI)
            sh = min(sin_upper(xh), Fr(1))
            out[(x, y, n)] = 1 / (2 * d * d * sh * sh)
    return out


def vthr_parts(d):
    """v_thr(d) = a + b sqrt2 (rational a, b)."""
    if d % 2 == 0:
        # 4(d-1) / ((4(d-1) - d^2) + d^2 sqrt2)
        P, Q = Fr(4 * (d - 1) - d * d), Fr(d * d)
        num = Fr(4 * (d - 1))
    else:
        # 4 / ((4 - d) + d sqrt2)
        P, Q = Fr(4 - d), Fr(d)
        num = Fr(4)
    N = P * P - 2 * Q * Q
    return num * P / N, -num * Q / N


def greater_than_vthr(v, d):
    a, b = vthr_parts(d)
    # v > a + b sqrt2  <=>  (v - a) > b sqrt2
    lhs = v - a
    if b <= 0:
        return lhs > 0 or (lhs == 0 and b < 0) or (lhs < 0 and lhs * lhs < 2 * b * b)
    return lhs > 0 and lhs * lhs > 2 * b * b


def check(d, cert, flo):
    v = Fr(cert['v'])
    W = {tuple(k): Fr(w) for k, w in cert['W']}
    t = Fr(0)
    AW = {(li, n): Fr(0) for li in range(4) for n in range(d)}
    for k, w in W.items():
        k00, k01, k10, k11 = k
        assert all(0 <= c < d for c in k)
        assert (k00 + k11 - k01 - k10) % d == 0, k
        assert w >= 0
        t += w
        for li in range(4):
            AW[(li, k[li])] += w
    assert 0 <= t < 1
    rhs = (1 - t) / (2 * d)
    slack = min(v * flo[(x, y, n)] + (1 - v) / d - AW[(li, n)] - rhs
                for li, (x, y) in enumerate(LINKS) for n in range(d))
    return v, t, slack


def main():
    files = sorted(glob.glob(os.path.join(HERE, 'certificates', 'dkz_d*.json')),
                   key=lambda p: int(os.path.basename(p)[5:-5]))
    allok = True
    for path in files:
        data = json.load(open(path))
        d = data['d']
        f1, f2 = flo_iv(d), flo_frac(d)
        for label, cert in data['certificates'].items():
            v, t, s1 = check(d, cert, f1)
            _, _, s2 = check(d, cert, f2)
            ok = s1 >= 0 and s2 >= 0
            beat = greater_than_vthr(v, d)
            allok &= ok
            print(f'd={d:2d} [{label:5s}] v = {str(v):>14s} = {float(v):.8f}  t = {float(t):.6f}  '
                  f'min slack (iv) {float(s1):.3e}  (frac) {float(s2):.3e}  -> local: {"YES" if ok else "NO"};  '
                  f'v > v_thr(d) exactly: {beat}')
    print('ALL CERTIFICATES VALID' if allok else 'SOME CERTIFICATE FAILED')


if __name__ == '__main__':
    main()
