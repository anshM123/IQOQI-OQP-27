"""Tests for verify_cert.py: every exact or transcendental constant that enters an interval is checked to CONTAIN the exact value
(exact integers / rationals compared exactly; transcendental values against 1200-bit mpmath values), the tail bounds are checked
against exact partial sums, and the F-enclosures are cross-checked against direct quadrature and against the previous
implementation (verify_gauss.py, Bell-polynomial derivatives; an independent code path).
Usage: python test_verify_cert.py [--quick]      (prints PASS/FAIL per test; exit code 1 on any failure)
"""
import sys
import os
import math
import random
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import verify_cert as vc                       # noqa: E402  (sets iv.prec = 160, mp.prec = 200)
import mpmath                                  # noqa: E402
from mpmath import iv, mp                      # noqa: E402

HP = 1200                                      # bits of the reference values
QUICK = '--quick' in sys.argv
RESULTS = []


def frac_of_mp(x):
    """exact rational value of an mp.mpf."""
    return vc.raw_to_frac(x._mpf_)


def lo_f(x):
    return vc.raw_to_frac(vc.LO(x))


def hi_f(x):
    return vc.raw_to_frac(vc.HI(x))


def contains(x, q):
    """exact containment of the rational q in the interval x."""
    return lo_f(x) <= q <= hi_f(x)


def contains_hp(x, val, err=Fraction(1, 2 ** (HP - 40))):
    """containment of a high-precision reference value val (relative error <= err) with that margin."""
    q = frac_of_mp(val)
    e = abs(q) * err if q else err
    return lo_f(x) <= q - e and q + e <= hi_f(x)


def hp(f):
    """evaluate f() with mp.prec = HP."""
    old = mp.prec
    mp.prec = HP
    try:
        return f()
    finally:
        mp.prec = old


def check(name, cond, info=''):
    RESULTS.append((name, bool(cond)))
    print(f"{'PASS' if cond else 'FAIL'}  {name}  {info}", flush=True)


# ---------------------------------------------------------------- 1. exact integers and rationals (G6)
def test_integers():
    ok = True
    nums = [math.factorial(n) for n in range(0, 201)]
    nums += [vc.dfact(n) for n in range(-1, 40, 2)]
    nums += [math.comb(i, k) for i in range(0, 300) for k in (0, 1, 2, 7, 8, 14, 16)]
    nums += [vc.poch(d, k) for d in (201, 202, 777, 1000, 1999, 2000) for k in range(0, 17)]
    nums += [2 ** j * math.factorial(j) for j in range(1, 8)]
    for n in nums:
        ok &= contains(vc.ivi(n), Fraction(n))
    check('integers -> intervals contain the exact integer (factorials to 200!, n!!, C(i,k), (d)_k, 2^j j!)', ok, f'{len(nums)} values')
    # the table constants of the certifier
    ok = all(contains(vc.FACT[n], Fraction(math.factorial(n))) for n in range(17))
    ok &= all(contains(vc.TCO[j], Fraction(2 ** j * math.factorial(j))) for j in range(1, 8))
    ok &= all(contains(vc.DFF[j], Fraction(vc.dfact(2 * j - 1))) for j in range(1, 9))
    ok &= all(contains(vc.FACT2J[j], Fraction(math.factorial(2 * j))) for j in range(1, 8))
    ok &= contains(vc.DF13, Fraction(135135)) and contains(vc.DF15, Fraction(2027025))
    check('certifier tables FACT, TCO, DFF, FACT2J, 13!!, 15!! contain the exact integers', ok)
    # rationals
    rng = random.Random(1)
    ok = True
    for _ in range(2000):
        q = Fraction(rng.randrange(-10 ** 60, 10 ** 60), rng.randrange(1, 10 ** 50))
        ok &= contains(vc.ivq(q), q)
    for d in (201, 1000, 2000):
        for j in range(1, d, 7):
            ok &= contains(vc.ivq(Fraction(j, 2 * d)), Fraction(j, 2 * d)) and contains(vc.ivq(Fraction(d, j)), Fraction(d, j))
    check('rationals -> intervals contain the exact rational', ok)
    # regression: the rounding that G6 refers to
    old = mp.prec
    mp.prec = 53
    x = iv.mpf(mpmath.factorial(25))
    mp.prec = old
    check('regression (G6): iv.mpf(mpmath.factorial(25)) at 53 bits does NOT contain 25! (the old pattern)',
          not contains(x, Fraction(math.factorial(25))))


# ---------------------------------------------------------------- 2. Bernoulli numbers, zeta, pi, elementary functions
def test_bernoulli():
    ok = True
    for n in range(0, len(vc.BERN)):
        p, q = mpmath.bernfrac(n)
        ok &= vc.BERN[n] == Fraction(int(p), int(q))
    check('Bernoulli numbers (exact recurrence) agree with mpmath.bernfrac', ok, f'B_0..B_{len(vc.BERN) - 1}')


def test_zeta():
    ok = True
    worst = 0
    for s in range(2, 18):
        z = vc.ZETA[s]
        ok &= contains_hp(z, hp(lambda: mp.zeta(s)))
        if s % 2 == 0:
            n = s // 2
            exact = hp(lambda: abs(mp.mpf(vc.BERN[2 * n].numerator) / vc.BERN[2 * n].denominator) * (2 * mp.pi) ** (2 * n)
                       / (2 * mp.factorial(2 * n)))
            ok &= contains_hp(z, exact)
        worst = max(worst, float(hi_f(z) - lo_f(z)))
    check('zeta(s), 2 <= s <= 17: Euler-Maclaurin enclosures contain zeta(s) (1200-bit reference; even s also B_2n formula)',
          ok, f'max width {worst:.1e}')


def test_pi_and_elementary():
    ok = contains_hp(vc.PI, hp(lambda: +mp.pi))
    ok &= contains_hp(vc.SQ2PI, hp(lambda: mp.sqrt(2 * mp.pi)))
    rng = random.Random(2)
    for _ in range(300):
        q = Fraction(rng.randrange(1, 10 ** 30), rng.randrange(1, 10 ** 28))
        x = vc.ivq(q)
        xm = lambda: mp.mpf(q.numerator) / q.denominator          # noqa: E731
        ok &= contains_hp(vc.isin(x), hp(lambda: mp.sin(xm())), err=Fraction(1, 2 ** 1100))
        ok &= contains_hp(vc.icos(x), hp(lambda: mp.cos(xm())), err=Fraction(1, 2 ** 1100))
        ok &= contains_hp(vc.ilog(x), hp(lambda: mp.log(xm())), err=Fraction(1, 2 ** 1100))
        ok &= contains_hp(vc.isqrt(x), hp(lambda: mp.sqrt(xm())), err=Fraction(1, 2 ** 1100))
        q2 = Fraction(rng.randrange(-10 ** 32, 10 ** 30), 10 ** 28)
        ok &= contains_hp(vc.iexp(vc.ivq(q2)), hp(lambda: mp.exp(mp.mpf(q2.numerator) / q2.denominator)), err=Fraction(1, 2 ** 1100))
    check('pi, sqrt(2 pi), sin, cos, exp, log, sqrt (widened) contain the 1200-bit values', ok, '300 random arguments')


# ---------------------------------------------------------------- 3. g_r coefficients and g_r(1)
def test_g():
    ok = contains_hp(vc.GCO[1], hp(lambda: -(4 / mp.pi) * (1 + mp.log(4 / mp.pi))))
    for n in range(1, vc.NSER + 1):
        ref = hp(lambda: (8 / mp.pi) * mp.zeta(2 * n) * (mp.mpf(1) / 2 - mp.mpf(4) ** (-n)) / (mp.mpf(4) ** n * n * (2 * n + 1)))
        ok &= contains_hp(vc.GCO[2 * n + 1], ref)
        bound = hp(lambda: (2 * mp.pi / 3) / (mp.mpf(4) ** n * n * (2 * n + 1)))
        ok &= frac_of_mp(ref) <= frac_of_mp(bound)                  # |g_{2n+1}| <= (2 pi/3) 4^-n/(n(2n+1))
    check('g_i (i <= 141) contain (8/pi) zeta(2n)(1/2 - 4^-n)/(4^n n(2n+1)); bound |g_i| <= (2pi/3)4^-n/(n(2n+1)) holds', ok)
    ref = hp(lambda: -16 * mp.catalan / mp.pi ** 2)                  # g_r(1) = -(16/pi^2) Catalan
    check('g_r(1) enclosure (series + tail) contains -16 G/pi^2', contains_hp(vc.GR1, ref),
          f'width {float(hi_f(vc.GR1) - lo_f(vc.GR1)):.1e}')
    # the series represents g_r: compare at x = 0.7 with the Clausen definition (non-rigorous reference, 1200 bits)
    x = Fraction(7, 10)
    s = sum((vc.GCO[i] * vc.ivq(x ** i) for i in range(1, vc.IMAX + 1, 2)), vc.ZERO)
    s = s + iv.make_mpf((vc.fzero, vc.HI(vc.TWOPI3 * vc.ivq(vc.gtail_frac(0)))))   # x^i <= 1
    ref = hp(lambda: -(8 / mp.pi ** 2) * (mp.clsin(2, mp.pi * mp.mpf(7) / 20) + mp.clsin(2, mp.pi - mp.pi * mp.mpf(7) / 20))
             - (4 / mp.pi) * mp.mpf(7) / 10 * mp.log(mp.mpf(7) / 10))
    check('g_r(0.7) by the series contains the Clausen-function value', contains_hp(s, ref, err=Fraction(1, 2 ** 1000)))


def test_gtail():
    ok = True
    for k in range(0, 17):
        partial = sum(Fraction(math.comb(2 * n + 1, k), 4 ** n * n * (2 * n + 1)) for n in range(vc.NSER + 1, vc.NSER + 400))
        ok &= partial <= vc.gtail_frac(k)
    check('tail sums: sum_{n>NSER} 4^-n C(2n+1,k)/(n(2n+1)) <= gtail_frac(k), k = 0..16 (exact partial sums)', ok)
    ok = mpmath.mpf(0) <= 0 and vc.mpf_le(vc.HI(vc.SK[1]), vc.from_int(8)) and vc.mpf_le(vc.HI(vc.SK[16]), vc.from_int(8))
    check('S_1, S_16 <= 8 (the constant of |F_r^(k)| <= 8 k! d^2/(d)_k)', ok,
          f'S_1 <= {float(hi_f(vc.SK[1])):.6f}, S_16 <= {float(hi_f(vc.SK[16])):.3e}')


# ---------------------------------------------------------------- 4. the regular part F_r
def exact_poly_coeffs(d, mm, i, kmax):
    """[h^k] prod_{q<i} (mm+q+h)/(d+q), k <= kmax, from the full integer polynomial in b (independent of the shift recurrence)."""
    poly = [1]                                                       # coefficients of prod_{q<i} (b + q) in powers of b
    for q in range(i):
        new = [0] * (len(poly) + 1)
        for e, c in enumerate(poly):
            new[e] += c * q
            new[e + 1] += c
        poly = new
    den = vc.poch(d, i)
    out = []
    for k in range(kmax + 1):
        # [h^k] P(mm + h) = P^(k)(mm)/k! = sum_e c_e C(e, k) mm^(e-k)
        s = sum(c * math.comb(e, k) * mm ** (e - k) for e, c in enumerate(poly) if e >= k)
        out.append(Fraction(s, den))
    return out


def test_fr_series():
    ok = True
    cases = [(201, 1), (201, 100), (201, 200), (1000, 3), (2000, 1999), (777, 400)]
    for d, mm in cases:
        INV = [vc.ONE / vc.ivi(d + q) for q in range(vc.IMAX)]
        rec = {}
        vc.fr_series(mm, INV, record=rec)
        for i in (1, 2, 3, 17, 50, 100, vc.IMAX):
            ex = exact_poly_coeffs(d, mm, i, vc.KMAX)
            for k in range(vc.KMAX + 1):
                ok &= contains(rec[i][k], ex[k])
    check('fr_series: truncated-product coefficients contain the exact [h^k] (m+h)_i/(d)_i (k <= 14)', ok, f'{len(cases)} (d,m)')


def test_fr_tail():
    """|sum_{i>IMAX} g_i p_i^(k)(m)| <= k!/(d)_k (2pi/3) gtail(k), checked against exact p_i^(k) for IMAX < i <= IMAX + 40."""
    ok = True
    for d, mm in ((201, 200), (201, 1), (1000, 999)):
        for k in (0, 2, 8, 14):
            tot = Fraction(0)
            for i in range(vc.IMAX + 2, vc.IMAX + 42, 2):
                n = (i - 1) // 2
                gbound = hp(lambda: (2 * mp.pi / 3) / (mp.mpf(4) ** n * n * (2 * n + 1)))
                pk = exact_poly_coeffs(d, mm, i, k)[k] * math.factorial(k)
                # e_k bound used in the proof: p_i^(k)(m) <= k! C(i,k)/(d)_k
                ok &= pk <= Fraction(math.factorial(k) * math.comb(i, k), vc.poch(d, k))
                tot += frac_of_mp(gbound) * pk
            bound = hi_f(vc.TWOPI3 * vc.ivq(vc.gtail_frac(k))) * Fraction(math.factorial(k), vc.poch(d, k))
            ok &= tot <= bound
    check('F_r tail bound and p_i^(k)(m) <= k! C(i,k)/(d)_k hold (exact p_i^(k), i up to IMAX + 40)', ok)


def test_S_bound():
    """|F_r^(k)(b)| <= k! d^2 S_k/(d)_k at non-integer b (numerical: 300-bit series evaluation, k = 1, 16)."""
    ok = True
    old = mp.prec
    mp.prec = 300
    for d in (201, 1000):
        for b in (mp.mpf('0.37'), mp.mpf(d) / 3 + mp.mpf('0.21'), mp.mpf(d) - mp.mpf('0.4')):
            for k in (1, 16):
                tot = mp.mpf(0)
                c = [mp.mpf(1)] + [mp.mpf(0)] * k
                for i in range(1, 400):
                    c = [c[0] * (b + i - 1) / (d + i - 1)] + [(c[j] * (b + i - 1) + c[j - 1]) / (d + i - 1) for j in range(1, k + 1)]
                    if i % 2 == 1:
                        n = (i - 1) // 2
                        g = (-(4 / mp.pi) * (1 + mp.log(4 / mp.pi)) if i == 1 else
                             (8 / mp.pi) * mp.zeta(2 * n) * (mp.mpf(1) / 2 - mp.mpf(4) ** (-n)) / (mp.mpf(4) ** n * n * (2 * n + 1)))
                        tot += g * c[k]
                val = abs(tot) * math.factorial(k) * d * d
                bnd = mp.mpf(math.factorial(k)) * d * d * mp.make_mpf(vc.HI(vc.SK[k])) / vc.poch(d, k)
                ok &= val <= bnd
    mp.prec = old
    check('|F_r^(k)(b)| <= k! d^2 S_k/(d)_k at non-integer b (k = 1, 16; numerical)', ok)


# ---------------------------------------------------------------- 5. polygamma at integers, psi bounds
def test_polygamma():
    ok = True
    gs = vc.Gauss(220) if QUICK else vc.Gauss(300)
    d = gs.d
    for nord in (1, 2, 3, 7, 13, 14, 15):
        for mm in (1, 2, 17, d // 2, d - 1):
            ok &= contains_hp(gs.polyg(nord, mm), hp(lambda: mp.polygamma(nord, mm + 1)), err=Fraction(1, 2 ** 1000))
    for k in (2, 8, 14):
        for mm in (1, 5, d - 1):
            ref = hp(lambda: k * mp.polygamma(k - 1, mm + 1) + mm * mp.polygamma(k, mm + 1))
            ok &= contains_hp(gs.kappa(k, mm), ref, err=Fraction(1, 2 ** 1000))
    check(f'psi^(n)(m+1) = (-1)^(n+1) n! [zeta(n+1) - H^(n+1)_m] and kappa_k enclosures contain the 1200-bit values (d = {d})', ok)
    ok = True
    for n in (15, 16):
        for z in ('0.3', '1.25', '7', '100'):
            zz = mp.mpf(z)
            ok &= abs(mp.polygamma(n, zz)) <= mp.factorial(n - 1) / zz ** n + mp.factorial(n) / zz ** (n + 1)
    for b in ('0.25', '1', '10', '1000'):
        bb = mp.mpf(b)
        k16 = 16 * mp.polygamma(15, bb + 1) + bb * mp.polygamma(16, bb + 1)
        ok &= abs(k16) <= 31 * mp.factorial(14) / (bb + 1) ** 15 + 32 * mp.factorial(15) / (bb + 1) ** 16
    check('|psi^(n)(z)| <= (n-1)!/z^n + n!/z^(n+1) and the kappa_16 bound (spot values)', ok)


# ---------------------------------------------------------------- 6. Gaussian truncation moments
def test_trunc():
    ok = True
    nfall = 0
    for j in range(1, 9):
        for (t, L) in ((Fraction(1, 300), Fraction(3, 4)), (Fraction(7, 1), Fraction(150, 2)), (Fraction(1, 1), Fraction(1, 1)),
                       (Fraction(9, 1), Fraction(3, 1)), (Fraction(4, 1), Fraction(6, 1)), (Fraction(50, 1), Fraction(30, 1))):
            ti, Li = vc.ivq(t), vc.ivq(L)
            before = vc.STATS['trunc_fallback']
            ub = vc.trunc_mom_ub(j, ti, Li)
            nfall += vc.STATS['trunc_fallback'] - before
            a2 = hp(lambda: (mp.mpf(L.numerator) / L.denominator) ** 2 / (mp.mpf(t.numerator) / t.denominator))
            exact = hp(lambda: (mp.mpf(t.numerator) / t.denominator) ** j * mp.mpf(2) ** j / mp.sqrt(mp.pi)
                       * mp.gammainc(j + mp.mpf(1) / 2, a2 / 2))
            ok &= frac_of_mp(exact) <= hi_f(ub)
            a2i = vc.ivq(L * L / t)
            ubm = vc.mj_ub(j, a2i)
            exm = hp(lambda: mp.mpf(2) ** j / mp.sqrt(mp.pi) * mp.gammainc(j + mp.mpf(1) / 2, a2 / 2))
            ok &= frac_of_mp(exm) <= hi_f(ubm)
    check('E[z^(2j) 1{|z| >= L}] <= trunc_mom_ub and m_j(a) <= mj_ub, j = 1..8, incl. the fallback branch (G3)', ok,
          f'{nfall} fallback cases tested')


# ---------------------------------------------------------------- 7. exact decimal strings
def test_decimal():
    rng = random.Random(3)
    ok = True
    for _ in range(3000):
        q = Fraction(rng.randrange(-10 ** 70, 10 ** 70), rng.randrange(1, 10 ** 75)) * Fraction(2) ** rng.randrange(-900, 300)
        x = vc.ivq(q)
        for raw in (vc.LO(x), vc.HI(x)):
            ok &= Fraction(vc.raw_to_dec(raw)) == vc.raw_to_frac(raw)
    ok &= vc.raw_to_dec(vc.LO(vc.ZERO)) == '0'
    check('raw_to_dec gives the exact value of the endpoint (3000 random intervals, round trip through Fraction)', ok)


# ---------------------------------------------------------------- 8. F against direct quadrature (consistency)
def test_F_quadrature():
    d = 201
    gs = vc.Gauss(d)
    old = mp.prec
    mp.prec = 140
    ok = True
    info = []
    for mm in ((3, 100) if QUICK else (3, 37, 100, 198)):
        b = mp.mpf(mm)
        lB = mp.log(mp.beta(b, d - b))

        def dens(x):
            return mp.exp((b - 1) * mp.log(x) + (d - b - 1) * mp.log(1 - x) - lB)

        def Ghat(x):                                                # Ghat(d x)
            return -(8 * mp.mpf(d) ** 2 / mp.pi ** 2) * (mp.clsin(2, mp.pi * x / 2) + mp.clsin(2, mp.pi - mp.pi * x / 2))
        s1 = -mp.digamma(b) + mp.digamma(d - b)
        s2 = -mp.psi(1, b) - mp.psi(1, d - b)
        pts = [0, mp.mpf(mm) / d / 4, mp.mpf(mm) / d, min(1, 4 * mp.mpf(mm) / d), 1]
        pts = sorted(set(pts))
        F0 = mp.quad(lambda x: Ghat(x) * dens(x), pts)
        F2 = mp.quad(lambda x: Ghat(x) * dens(x) * ((mp.log(x) - mp.log(1 - x) + s1) ** 2 + s2), pts)
        for val, enc in ((F0, gs.Fv[mm][0]), (F2, gs.Fv[mm][1])):
            q = frac_of_mp(val)
            tol = abs(q) * Fraction(1, 10 ** 30) + Fraction(1, 10 ** 30)
            ok &= lo_f(enc) - tol <= q <= hi_f(enc) + tol
            info.append(f'{float(abs(q - (lo_f(enc) + hi_f(enc)) / 2)):.1e}')
    mp.prec = old
    check('F(m), F\'\'(m) at d = 201 agree with direct Beta-density quadrature (40 digits)', ok, 'deviations ' + ' '.join(info))


# ---------------------------------------------------------------- 9. H(m,t) - F(m) against nested quadrature (consistency)
def test_HmF_quadrature():
    d, mm = 201, 6
    gs = vc.Gauss(d)
    old = mp.prec
    mp.prec = 110
    lB = {}

    def F(b):
        if b not in lB:
            lB[b] = mp.log(mp.beta(b, d - b))
        lb = lB[b]
        f = lambda x: (-(8 * mp.mpf(d) ** 2 / mp.pi ** 2) * (mp.clsin(2, mp.pi * x / 2) + mp.clsin(2, mp.pi - mp.pi * x / 2))  # noqa
                       * mp.exp((b - 1) * mp.log(x) + (d - b - 1) * mp.log(1 - x) - lb))
        return mp.quad(f, [0, b / d / 4, b / d, 4 * b / d, 1])
    t = mp.mpf('0.05')
    Fm = F(mp.mpf(mm))
    # E[F(m + z) - F(m)], z ~ N(0, t), by a 30-node Gauss-Hermite rule (nodes |xi| < 7.6, so |z| < 1.7 < L = 4.5; the truncation
    # 1{|z| < L} changes the expectation by less than 1e-80 here)
    xs, ws = gauss_hermite_prob(30)
    tot = mp.mpf(0)
    for x, w in zip(xs, ws):
        tot += w * (F(mm + mp.sqrt(t) * x) - Fm)
    enc = gs.HmF(mm, vc.ivq(Fraction(1, 20)))
    q = frac_of_mp(tot)
    mp.prec = old
    dev = abs(q - (lo_f(enc) + hi_f(enc)) / 2)
    check('H(m,t) - F(m) (order-14 expansion + remainders) agrees with Gauss-Hermite x Beta quadrature (d = 201, m = 6, t = 0.05)',
          lo_f(enc) - Fraction(1, 10 ** 25) <= q <= hi_f(enc) + Fraction(1, 10 ** 25), f'deviation {float(dev):.1e}')


def gauss_hermite_prob(n):
    """nodes and weights of the n-point Gauss rule for the standard normal law (Golub-Welsch)."""
    J = mp.matrix(n, n)
    for k in range(1, n):
        J[k - 1, k] = J[k, k - 1] = mp.sqrt(k)
    E, Q = mp.eigsy(J)
    return [E[i] for i in range(n)], [Q[0, i] ** 2 for i in range(n)]


# ---------------------------------------------------------------- 10. cross-check with the previous implementation
def test_old_implementation():
    """verify_gauss.py (Bell polynomials, harmonic-sum logarithmic derivatives, crude bounds for k >= 10) at the same d and
       160 bits: the enclosures of F^(2j)(m) (j <= 4), tau_m and the root boxes must overlap."""
    import mpmath as _m
    d = 203
    src = open(os.path.join(HERE, 'verify_gauss.py'), encoding='utf-8').read()
    head = src.split('# ---------------------------------------------------------------- variogram coefficients')[0]
    argv = sys.argv
    cwd = os.getcwd()
    saved = (iv.prec, mp.prec)
    sys.argv = ['verify_gauss.py', str(d), '160']
    g = {'__name__': 'vg_head'}
    try:
        os.chdir(HERE)
        exec(compile(head, 'verify_gauss_head', 'exec'), g)
    finally:
        sys.argv = argv
        os.chdir(cwd)
        iv.prec, mp.prec = saved
    gs = vc.Gauss(d)
    ok = True
    for mm in range(1, d):
        for j in range(0, 5):
            a, b = g['Fv'][mm][j], gs.Fv[mm][j]
            ok &= lo_f(a) <= hi_f(b) and lo_f(b) <= hi_f(a)
    for mm in range(1, (d - 1) // 2 + 1):
        a, b = g['Dlt'][mm] - g['Dlt'][d - mm], gs.Dlt[mm] - gs.Dlt[d - mm]
        ok &= lo_f(a) <= hi_f(b) and lo_f(b) <= hi_f(a)
    check(f'previous implementation (verify_gauss.py head, 160 bits, d = {d}): F^(2j)(m), j <= 4, and tau_m enclosures overlap', ok)
    del _m


def main():
    t0 = time.time()
    test_integers()
    test_bernoulli()
    test_zeta()
    test_pi_and_elementary()
    test_g()
    test_gtail()
    test_fr_series()
    test_fr_tail()
    test_S_bound()
    test_polygamma()
    test_trunc()
    test_decimal()
    test_F_quadrature()
    test_HmF_quadrature()
    test_old_implementation()
    nf = sum(1 for _, r in RESULTS if not r)
    print(f"{len(RESULTS) - nf}/{len(RESULTS)} tests passed  [{time.time() - t0:.0f}s]")
    sys.exit(1 if nf else 0)


if __name__ == '__main__':
    main()
