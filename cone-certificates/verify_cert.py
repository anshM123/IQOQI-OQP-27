"""Unified rigorous certificate for CONE_d in the Gaussian regime 201 <= d <= 2000 (CONE_PROOF.md, Lemmas R1-R4 and Lemma B).

ONE run, ONE precision (iv.prec = PREC = 160 bits) and ONE code version (the SHA-256 of this file is written into the output).
Everything that enters a decision is an mpmath interval (outward rounding); every decision is an exact comparison of interval
endpoints; nothing is taken from another run.  Exact integers and rationals (factorials, binomials, Bernoulli numbers, Pochhammer
symbols, Euler-Maclaurin coefficients) are formed in Python integer / Fraction arithmetic and only then converted to intervals with
outward rounding (mpmath rounds int -> interval outward; a rational p/q is enclosed by the interval quotient of the two enclosures).
Values of transcendental functions (pi, sin, cos, exp, log, sqrt) are mpmath interval values widened by a further 16 units in the
last place.

For the given d the script computes:
 1. F^(2j)(m), j = 0..7, at every integer 1 <= m <= d-1, where F(b) = E Ghat(d X_b), X_b ~ Beta(b, d-b), F = F_s + F_r (Lemma R2):
      F_s^(k)(m) = (4d/pi) kappa_k(m),  kappa_k(m) = k psi^(k-1)(m+1) + m psi^(k)(m+1)  (k >= 2),
                   psi^(n)(m+1) = (-1)^(n+1) n! [zeta(n+1) - H^(n+1)_m],  zeta(s) enclosed by an Euler-Maclaurin sum in exact rational
                   arithmetic plus its remainder bound;
      F_r(b) = d^2 sum_{i odd} g_i p_i(b),  p_i(b) = (b)_i/(d)_i,  g_r(x) = sum_{i odd} g_i x^i (exact Bernoulli numbers, enclosure of
                   pi), so F_r^(k)(m) = d^2 sum_{i odd} g_i k! [h^k] p_i(m + h):  the Taylor coefficients of p_i(m + h) for k <= 14 by
                   exact truncated products for i <= IMAX, and the tail i > IMAX by
                   0 <= p_i^(k)(b) <= p_i^(k)(d) = k! e_k(1/d, ..., 1/(d+i-1)) <= k! C(i,k)/(d)_k   (b in [0, d]),
                   |g_{2n+1}| <= (2 pi/3) 4^-n/(n(2n+1))   (n >= 1),
                   so |tail of F_r^(k)| <= d^2 k!/(d)_k (2 pi/3) sum_{n > NSER} 4^-n C(2n+1,k)/(n(2n+1))  (ratio test, exact rationals);
      the same two facts give |F_r^(k)(b)| <= k! d^2 S_k/(d)_k on [0, d] with S_k = sum_{i odd} |g_i| C(i,k) (computed, <= 8),
      used for k = 16 (Lagrange remainder) and k = 1 (sup|F'|).
 2. tau_m = Dlt(m) - Dlt(d-m), Dlt = P_v - F = P_{v,r} - F_r (Lemma R2), P_{v,r} by the prefix-sum Green formula with
      P_{v,r}(d) = d^2 g_r(1), g_r(1) = sum_{i <= IMAX} g_i + [0, tail]  (g_i > 0 for i >= 3).
 3. Root boxes [a_m, b_m] (1 <= m < d/2) of Hc_m(t) = tau_m: certified sign change Hc_m(a_m) < tau_m < Hc_m(b_m) of the interval
      enclosure Hc_m(t) = [H(m,t) - F(m)] - [H(d-m,t) - F(d-m)], H(b,t) - F(b) = sum_{j<=7} t^j F^(2j)(b)/(2^j j!) - truncation terms
      + order-16 Lagrange remainder (two levels).  The search itself (Newton on midpoints, step doubling) is untrusted.
 4. Tail quantities (Lemma R4): sup|F'| <= (4d/pi)(H_d + 1) + d S_1; log P(E^c) <= log(2d) - 9/(32 Phi1+); eps_t <= (3d/8) sup|F'| P(E^c)
      (computed as logarithms: no underflow); the box radius r = 2^e (a power of two, r >= 8 eps_t/c1min, r >= 2^-100); the widened
      boxes Q_m = [lo_m, hi_m] with lo_m <= a_m - r, hi_m >= b_m + r (outward rounded); Phi(d/2) (d even) is a fixed exact number.
 5. On the Poincare-Miranda box Q = prod_m Q_m of Lemma B (evaluated ON Q, no perturbation margins borrowed):
      (B1)  min_k at_k(Phi) > 0 for all Phi in Q  (interval DFT with Phi(m) ranging over Q_m);
      (D)   c_D := min_m inf_{t in Q_m} Hc_m'(t) > 0 and c_D r > 2 eps_t  (with the sign changes this gives (B3));
      (B3)  also directly: Hc_m(lo_m) - tau_m < -2 eps_t and Hc_m(hi_m) - tau_m > 2 eps_t for every m;
      (ii)  min_m Delta^2 W_H > 4 eps_t on Q, W_H = (P_v - H(., Phi))_S  (Lemma R1 (ii) for the exact process, |P - H| <= eps_t);
      boxes in t > 0.
 6. Output logs/cert_g_d{d}.json: every certified bound as the EXACT decimal expansion of the interval endpoint (a string), the
    SHA-256 of this file, the precisions; a SHA-256 of the exact box endpoints (all m).  --dump-boxes writes all boxes as well.
Usage: python verify_cert.py d [--dump-boxes]
"""
import sys
import os
import time
import json
import math
import hashlib
import platform
import traceback
from fractions import Fraction

import mpmath
from mpmath import iv, mp
from mpmath.libmp import mpf_lt, mpf_gt, mpf_le, mpf_neg, from_int, fzero, finf, fninf, fnan

PREC = 160            # bits of every interval computation
XPREC = PREC + 40     # bits of the untrusted root search; the box endpoints are exact binary numbers of this size
NSER = 70             # g_r(x) = sum_{i odd} g_i x^i: i = 1, 3, ..., IMAX explicit, i > IMAX by the tail bound
IMAX = 2 * NSER + 1
KMAX = 14             # F_r^(k)(m) from the exact truncated series for k <= KMAX
EM_N, EM_K = 64, 40   # Euler-Maclaurin parameters for zeta(s), 2 <= s <= 17
R_FLOOR_LOG2 = -100   # box radius r = 2^e with e >= R_FLOOR_LOG2 ...
R_CAP_LOG2 = -80      # ... and e <= R_CAP_LOG2 (r is chosen with P(E^c) evaluated at Phi(1) = b_1 + 2^R_CAP_LOG2)
SCRIPT = os.path.abspath(__file__)
QD2 = os.path.dirname(SCRIPT)

iv.prec = PREC
mp.prec = XPREC


def code_sha256():
    with open(SCRIPT, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


# ================================================================ interval helpers
def LO(x):
    """raw lower endpoint (mpmath mpf tuple)."""
    return x._mpi_[0]


def HI(x):
    return x._mpi_[1]


def finite(x):
    return all(v not in (finf, fninf, fnan) for v in x._mpi_)


def pt(raw):
    """point interval at an exact raw endpoint."""
    return iv.make_mpf((raw, raw))


def upper(x):
    """point interval at the upper endpoint of x (an upper bound of every element of x)."""
    return pt(HI(x))


def sym(x):
    """[-u, u] with u the upper endpoint of x (x >= 0)."""
    return iv.make_mpf((mpf_neg(HI(x)), HI(x)))


def is_pos(x):
    """certified: every element of x is > 0."""
    return finite(x) and mpf_gt(LO(x), fzero)


def is_neg(x):
    return finite(x) and mpf_lt(HI(x), fzero)


ZERO = iv.mpf(0)
ONE = iv.mpf(1)


def ivi(n):
    """enclosure of the exact integer n (mpmath converts a Python int to an interval with outward rounding)."""
    return iv.mpf(int(n))


def ivq(x):
    """enclosure of the exact rational x."""
    x = Fraction(x)
    return iv.mpf(int(x.numerator)) / iv.mpf(int(x.denominator))


def ivq2(lo, hi):
    """enclosure of the real interval [lo, hi] with exact rational endpoints."""
    return iv.make_mpf((LO(ivq(lo)), HI(ivq(hi))))


EPSW = iv.ldexp(ONE, -(PREC - 4))


def widen(x):
    """x widened outward by 16 units in the last place (relative 2^-(PREC-4))."""
    e = HI(abs(x) * EPSW)
    return x + iv.make_mpf((mpf_neg(e), e))


def isin(x):
    return widen(iv.sin(x))


def icos(x):
    return widen(iv.cos(x))


def iexp(x):
    return widen(iv.exp(x))


def ilog(x):
    return widen(iv.log(x))


def isqrt(x):
    return widen(iv.sqrt(x))


PI = widen(+iv.pi)
SQ2PI = isqrt(2 * PI)


def dfact(n):
    """exact double factorial n!! (n odd >= -1)."""
    return math.prod(range(n, 0, -2)) if n > 0 else 1


def poch(x, k):
    """exact rising factorial (x)_k for integers x, k >= 0."""
    return math.prod(range(x, x + k))


# ================================================================ exact decimal strings of endpoints
def raw_to_frac(v):
    if v in (finf, fninf, fnan):
        raise ValueError('non-finite endpoint')
    sign, man, exp, bc = v
    if not man:
        return Fraction(0)
    val = Fraction(int(man) << exp) if exp >= 0 else Fraction(int(man), 1 << (-exp))
    return -val if sign else val


def raw_to_dec(v):
    """EXACT decimal expansion of a finite binary endpoint (no rounding)."""
    if v in (finf, fninf, fnan):
        raise ValueError('non-finite endpoint')
    sign, man, exp, bc = v
    if not man:
        return '0'
    s = '-' if sign else ''
    man = int(man)
    if exp >= 0:
        return s + str(man << exp)
    k = -exp
    digits = str(man * 5 ** k)                     # man 2^-k = man 5^k / 10^k
    if len(digits) <= k:
        digits = '0' * (k - len(digits) + 1) + digits
    ip, fp = digits[:-k], digits[-k:].rstrip('0')
    return s + ip + ('.' + fp if fp else '')


def raw_to_hex(v):
    sign, man, exp, bc = v
    return f"{'-' if sign else ''}{int(man):x}p{exp}"


def nstr(raw, n=8):
    return mpmath.nstr(mp.make_mpf(raw), n)


# ================================================================ d-independent exact constants
def bernoulli_numbers(nmax):
    """B_0..B_nmax exactly (B_1 = -1/2), from sum_{k=0}^{n} C(n+1,k) B_k = 0."""
    B = [Fraction(1)]
    for n in range(1, nmax + 1):
        B.append(-sum(math.comb(n + 1, k) * B[k] for k in range(n)) / (n + 1))
    return B


BERN = bernoulli_numbers(max(2 * NSER, 2 * EM_K))


def zeta_iv(s):
    """enclosure of zeta(s), s >= 2 an integer:
       zeta(s) = sum_{n<N} n^-s + N^(1-s)/(s-1) + N^-s/2 + sum_{j=1}^{K} B_2j/(2j)! (s)_{2j-1} N^(-s-2j+1) + R,
       |R| <= |B_2K|/(2K)! (s)_{2K-1} N^(-s-2K+1)  (Euler-Maclaurin; |B_2K(x)| <= |B_2K| on [0,1], x^-s completely monotone).
       All terms exact rationals."""
    N, K = EM_N, EM_K
    S = sum(Fraction(1, n ** s) for n in range(1, N))
    S += Fraction(1, (s - 1) * N ** (s - 1)) + Fraction(1, 2 * N ** s)
    term = None
    for j in range(1, K + 1):
        term = BERN[2 * j] * poch(s, 2 * j - 1) / (math.factorial(2 * j) * N ** (s + 2 * j - 1))
        S += term
    rem = abs(term)
    return ivq2(S - rem, S + rem)


ZETA = {s: zeta_iv(s) for s in range(2, 18)}

# g_r(x) = -(8/pi^2)[Cl2(pi x/2) + Cl2(pi - pi x/2)] - (4/pi) x log x = sum_{i odd} g_i x^i  (|x| < 2):
#   g_1 = -(4/pi)(1 + log(4/pi)),  g_{2n+1} = 8 |B_2n| (1/2 - 4^-n) pi^(2n-1) / (2n (2n+1)!)   (n >= 1; all > 0)
GCO = {1: -(4 / PI) * (1 + ilog(4 / PI))}
for _n in range(1, NSER + 1):
    _R = abs(BERN[2 * _n]) * (Fraction(1, 2) - Fraction(1, 4 ** _n)) / (2 * _n * math.factorial(2 * _n + 1))
    GCO[2 * _n + 1] = 8 * ivq(_R) * PI ** (2 * _n - 1)
TWOPI3 = 2 * PI / 3      # |g_{2n+1}| = (8/pi) zeta(2n) (1/2 - 4^-n)/(4^n n(2n+1)) <= (2 pi/3) 4^-n/(n(2n+1))


def gtail_frac(k):
    """exact rational upper bound of sum_{n > NSER} 4^-n C(2n+1, k)/(n(2n+1)):  u_{n+1}/u_n <= rho for n >= N0 := NSER+1, with
       rho = (1/4)(2N0+3)(2N0+2)/((2N0+3-k)(2N0+2-k)) (x/(x-k) decreases in x, and n(2n+1)/((n+1)(2n+3)) <= 1)."""
    N0 = NSER + 1
    u0 = Fraction(math.comb(2 * N0 + 1, k), 4 ** N0 * N0 * (2 * N0 + 1))
    rho = Fraction((2 * N0 + 3) * (2 * N0 + 2), 4 * (2 * N0 + 3 - k) * (2 * N0 + 2 - k))
    assert 0 < rho < 1
    return u0 / (1 - rho)


GTAIL = {k: TWOPI3 * ivq(gtail_frac(k)) for k in range(0, 17)}        # >= sum_{i > IMAX, odd} |g_i| C(i, k)
SK = {k: sum((abs(GCO[i]) * math.comb(i, k) for i in range(1, IMAX + 1, 2)), ZERO) + GTAIL[k] for k in (1, 16)}
for _k in (1, 16):
    assert mpf_le(HI(SK[_k]), from_int(8)), 'S_k <= 8 fails'
GR1 = sum((GCO[i] for i in range(1, IMAX + 1, 2)), ZERO) + iv.make_mpf((fzero, HI(GTAIL[0])))   # g_r(1)

FACT = [ivi(math.factorial(n)) for n in range(0, 17)]
TCO = [None] + [ivi(2 ** j * math.factorial(j)) for j in range(1, 8)]           # 2^j j! = (2j)!/(2j-1)!!
DF13 = ivi(dfact(13))
DF15 = ivi(dfact(15))
DFF = [None] + [ivi(dfact(2 * j - 1)) for j in range(1, 9)]                      # (2j-1)!!
FACT2J = [None] + [ivi(math.factorial(2 * j)) for j in range(1, 8)]              # (2j)!

STATS = {'trunc_fallback': 0, 'mj_fallback': 0}


# ================================================================ Gaussian truncation moments
def trunc_mom_ub(j, t, L):
    """upper bound (point interval) of E[z^(2j) 1{|z| >= L}], z ~ N(0, t), t > 0 a point interval:
       = t^j E[xi^(2j) 1{|xi| >= a}], a = L/sqrt(t);  int_a^inf x^n e^(-x^2/2) dx <= a^(n-1) e^(-a^2/2)/(1 - (n-1)/a^2) for a^2 > n-1
       (integration by parts); otherwise the full moment t^j (2j-1)!!  (valid for every j, including j = 8)."""
    n = 2 * j
    a2 = L * L / t
    if mpf_gt(LO(a2), from_int(n)):
        a = isqrt(a2)
        val = t ** j * (2 / SQ2PI) * a ** (n - 1) * iexp(-a2 / 2) / (1 - (n - 1) / a2)
        return upper(val)
    STATS['trunc_fallback'] += 1
    return upper(t ** j * DFF[j])


def mj_ub(j, a2):
    """upper bound of m_j(a) = E[xi^(2j) 1{|xi| >= a}] (a^2 an interval)."""
    n = 2 * j
    if mpf_gt(LO(a2), from_int(n)):
        a = isqrt(a2)
        return upper((2 / SQ2PI) * a ** (n - 1) * iexp(-a2 / 2) / (1 - (n - 1) / a2))
    STATS['mj_fallback'] += 1
    return DFF[j]


# ================================================================ the regular part F_r: exact truncated series
def fr_series(mm, INV, record=None):
    """[sum_{i odd <= IMAX} g_i [h^k] p_i(mm + h)]_{k=0..KMAX},  p_i(b) = prod_{q<i} (b+q)/(d+q),
       by the exact recurrence c^(i+1)_k = (c^(i)_k (mm+i) + c^(i)_{k-1}) / (d+i)  (all terms >= 0)."""
    c = [ONE] + [ZERO] * KMAX
    out = [ZERO] * (KMAX + 1)
    for i in range(1, IMAX + 1):
        A = ivi(mm + i - 1)
        inv = INV[i - 1]
        c = [c[0] * A * inv] + [(c[k] * A + c[k - 1]) * inv for k in range(1, KMAX + 1)]
        if record is not None:
            record[i] = list(c)
        if i % 2 == 1:
            g = GCO[i]
            for k in range(0, KMAX + 1, 2):
                out[k] += g * c[k]
    return out


# ================================================================ the per-d enclosures
class Gauss:
    """all enclosures of CONE_PROOF.md for one d that do not depend on the box (F^(2j)(m), Dlt, H - F, d/dt H)."""

    def __init__(self, d):
        assert d >= 8
        self.d = d
        D = self.D = ivi(d)
        D2 = self.D2 = D * D
        c4d = self.c4d = 4 * D / PI
        self.half = (d - 1) // 2
        # harmonic sums H^(s)_n, n = 0..d, s = 1..17
        H = self.H = {s: [ZERO] for s in range(1, 18)}
        for n in range(1, d + 1):
            N_ = ivi(n)
            for s in range(1, 18):
                H[s].append(H[s][-1] + ONE / N_ ** s)
        # F^(2j)(m), j = 0..7, and F_r(m)
        self.INV = [ONE / ivi(d + q) for q in range(IMAX)]
        self.TAILF = [sym(D2 * FACT[k] / ivi(poch(d, k)) * GTAIL[k]) for k in range(KMAX + 1)]
        self.REG16 = upper(D2 * FACT[16] / ivi(poch(d, 16)) * SK[16])     # sup_[0,d] |F_r^(16)|
        self.Fv, self.FrV = {}, {}
        for mm in range(1, d):
            out = fr_series(mm, self.INV)
            self.FrV[mm] = D2 * out[0] + self.TAILF[0]
            Fm = [c4d * ivi(mm) * (H[1][mm] - H[1][d]) + self.FrV[mm]]   # F_s(m) = (4d/pi) m [psi(m+1) - psi(d+1)]
            for j in range(1, 8):
                k = 2 * j
                Fm.append(c4d * self.kappa(k, mm) + D2 * FACT[k] * out[k] + self.TAILF[k])
            self.Fv[mm] = Fm
        # P_{v,r}: Delta^2 P = g_r''(m/d) on 1..d-1, P(0) = 0, P(d) = d^2 g_r(1);  g_r''(x) = 2 csc(pi x/2) - (4/pi)/x
        f = [None] + [2 / isin(PI * ivq(Fraction(j, 2 * d))) - (4 / PI) * ivq(Fraction(d, j)) for j in range(1, d)]
        Pd = D2 * GR1
        pre1 = [ZERO]
        for j in range(1, d):
            pre1.append(pre1[-1] + ivi(j) * f[j])
        suf2 = [ZERO] * (d + 1)
        for j in range(d - 1, 0, -1):
            suf2[j] = suf2[j + 1] + ivi(d - j) * f[j]
        self.Pvr = [ZERO] * (d + 1)
        self.Pvr[d] = Pd
        self.Dlt = [ZERO] * (d + 1)                                     # Dlt(0) = Dlt(d) = 0 exactly
        for mm in range(1, d):
            self.Pvr[mm] = ivq(Fraction(mm, d)) * Pd - (ivq(Fraction(d - mm, d)) * pre1[mm] + ivq(Fraction(mm, d)) * suf2[mm + 1])
            self.Dlt[mm] = self.Pvr[mm] - self.FrV[mm]                  # P_v - F = P_{v,r} - F_r  (Lemma R2)
        self.SCACHE = {}

    def polyg(self, nord, mm):
        """psi^(nord)(mm + 1) = (-1)^(nord+1) nord! [zeta(nord+1) - H^(nord+1)_mm]  (nord >= 1)."""
        v = FACT[nord] * (ZETA[nord + 1] - self.H[nord + 1][mm])
        return v if nord % 2 == 1 else -v

    def kappa(self, k, mm):
        """d^k/db^k [b psi(b+1)] at b = mm (k >= 2)."""
        return k * self.polyg(k - 1, mm) + mm * self.polyg(k, mm)

    def S16(self, mm, rad, tag):
        """upper bound of sup_{|z| <= rad} |F^(16)(mm + z)|:  |kappa_16(b)| <= 31*14!/(b+1)^15 + 32*15!/(b+1)^16 (from
           |psi^(n)(z)| <= (n-1)!/z^n + n!/z^(n+1)) and |F_r^(16)| <= 16! d^2 S_16/(d)_16."""
        key = (mm, tag)
        if key not in self.SCACHE:
            blo = ivi(mm) - rad                                         # >= mm/4 > 0
            sing = self.c4d * (31 * FACT[14] / (blo + 1) ** 15 + 32 * FACT[15] / (blo + 1) ** 16)
            self.SCACHE[key] = upper(sing + self.REG16)
        return self.SCACHE[key]

    def radii(self, mm):
        """L_m = (3/4) min(m, d-m) (truncation radius of Lemma R4) and the inner radius min(m, d-m)/2 of the remainder."""
        m_ = min(mm, self.d - mm)
        return ivq(Fraction(3 * m_, 4)), ivq(Fraction(m_, 2))

    def HmF(self, mm, t):
        """enclosure of H(mm, t) - F(mm) for all t in the interval t (t > 0):
           sum_{j<=7} t^j F^(2j)(mm)/(2^j j!) - sum_j F^(2j)(mm) T_j/(2j)! + E[R16(z) 1{|z| < L}],  T_j = E[z^(2j) 1{|z| >= L}],
           |R16(z)| <= S |z|^16/16! with S = S_near on |z| < L/... (inner radius) and S_far beyond."""
        L, Lnear = self.radii(mm)
        Fj = self.Fv[mm]
        main = ZERO
        tp = ONE
        for j in range(1, 8):
            tp = tp * t
            main += tp * Fj[j] / TCO[j]
        tt = upper(t)                                                   # every error term below increases with t
        err = (DF15 * tt ** 8 * self.S16(mm, Lnear, 'near') + trunc_mom_ub(8, tt, Lnear) * self.S16(mm, L, 'far')) / FACT[16]
        for j in range(1, 8):
            err += upper(abs(Fj[j])) * trunc_mom_ub(j, tt, L) / FACT2J[j]
        return main + sym(err)

    def Hc(self, mm, t):
        """enclosure of Hc_m(t) = [H(m,t) - F(m)] - [H(d-m,t) - F(d-m)]."""
        return self.HmF(mm, t) - self.HmF(self.d - mm, t)

    def dH(self, bb, tbox, L, S):
        """enclosure of d/dt H(bb, t) for all t in tbox:
           d/dt E[z^(2j) 1{|z|<L}] = j t^(j-1)(2j-1)!! - T_j',  0 <= T_j' <= j t^(j-1) m_j(a) + L^(2j+1) phi(a)/t^(3/2);
           |d/dt E[R16 1{|z|<L}]| <= (1/2)[S t^7 13!!/14! + phi_t(L)(S L^16/16! 2L/t + 2 S L^15/15!)]  (heat equation, two
           integrations by parts);  a, phi(a), phi_t(L) maximised over the box (a = L/sqrt(t_hi), 1/t at t_lo)."""
        Fj = self.Fv[bb]
        main = ZERO
        for j in range(1, 8):
            main += Fj[j] * j * tbox ** (j - 1) / TCO[j]
        tl, th = pt(LO(tbox)), pt(HI(tbox))
        a2 = L * L / th
        phia = iexp(-a2 / 2) / SQ2PI
        tl32 = tl * isqrt(tl)
        err = ZERO
        for j in range(1, 8):
            dT = j * th ** (j - 1) * mj_ub(j, a2) + L ** (2 * j + 1) * phia / tl32
            err += upper(abs(Fj[j])) * upper(dT) / FACT2J[j]
        phitL = phia / isqrt(tl)
        err += (S * th ** 7 * DF13 / FACT[14] + phitL * (S * L ** 16 / FACT[16] * 2 * L / tl + 2 * S * L ** 15 / FACT[15])) / 2
        return main + sym(err)


# ================================================================ the certificate for one d
def certify(d, dump_boxes=False, verbose=True):
    t0 = time.time()

    def log(msg):
        if verbose:
            print(f"d={d}: {msg} [{time.time() - t0:.0f}s]", flush=True)

    gs = Gauss(d)
    D, Fv, Dlt, half = gs.D, gs.Fv, gs.Dlt, gs.half
    log("F^(2j)(m), j <= 7, tau_m enclosed")

    # ---- root boxes [a_m, b_m] (certified sign change; the search is untrusted)
    def mid(x):
        return (mp.make_mpf(LO(x)) + mp.make_mpf(HI(x))) / 2

    TAU, A_, B_, C1 = {}, {}, {}, {}
    sc_left, sc_right = None, None
    width_max = fzero
    for mm in range(1, half + 1):
        tau = Dlt[mm] - Dlt[d - mm]
        TAU[mm] = tau
        C1[mm] = (Fv[mm][1] - Fv[d - mm][1]) / 2
        cms = [None] + [mid((Fv[mm][j] - Fv[d - mm][j]) / TCO[j]) for j in range(1, 8)]
        taum = mid(tau)
        tm = taum / cms[1]
        for _ in range(60):
            fv = sum(cms[j] * tm ** j for j in range(1, 8)) - taum
            fd = sum(j * cms[j] * tm ** (j - 1) for j in range(1, 8))
            tm = tm - fv / fd

        def gt(tmp):
            return gs.Hc(mm, iv.mpf(tmp)) - tau

        g0 = gt(tm)
        step0 = max((mp.make_mpf(HI(g0)) - mp.make_mpf(LO(g0))) / cms[1] / 4, abs(tm) * mp.mpf(2) ** -100, mp.mpf(2) ** -XPREC)
        a_, step, ga = tm, step0, g0
        for it in range(400):
            if is_neg(ga):
                break
            a_ -= step
            step *= 2
            ga = gt(a_)
        else:
            raise RuntimeError(f'm={mm}: no left sign change')
        b_, step, gb = tm, step0, g0
        for it in range(400):
            if is_pos(gb):
                break
            b_ += step
            step *= 2
            gb = gt(b_)
        else:
            raise RuntimeError(f'm={mm}: no right sign change')
        if not a_ > 0:
            raise RuntimeError(f'm={mm}: root box reaches t <= 0')
        A_[mm], B_[mm] = a_, b_
        wdt = HI(iv.mpf(b_) - iv.mpf(a_))
        if mpf_gt(wdt, width_max):
            width_max = wdt
        if sc_left is None or mpf_gt(HI(ga), sc_left):
            sc_left = HI(ga)
        if sc_right is None or mpf_lt(LO(gb), sc_right):
            sc_right = LO(gb)
    log(f"root boxes: max width {nstr(width_max, 3)}, Phi(1) d = {mpmath.nstr(A_[1] * d, 8)}")
    c1min = None
    for mm in range(1, half + 1):
        if c1min is None or mpf_lt(LO(C1[mm]), c1min):
            c1min = LO(C1[mm])
    if not mpf_gt(c1min, fzero):
        raise RuntimeError('c1min <= 0')

    # ---- Phi(d/2) for even d: a fixed exact number (the antisymmetric equation is vacuous at d/2)
    phalf = None
    if d % 2 == 0:
        h2 = d // 2
        box = {mm: iv.mpf([A_[mm], B_[mm]]) for mm in (h2 - 1, h2 - 2, h2 - 3)}
        phalf = mid((15 * box[h2 - 1] - 6 * box[h2 - 2] + box[h2 - 3]) / 10)

    # ---- tail quantities (Lemma R4) in logarithms
    supF1 = upper(gs.c4d * (gs.H[1][d] + 1) + D * SK[1])                # |F_s'| <= (4d/pi)(H_d + 1), |F_r'| <= d S_1

    def log_tails(phi1_hi):
        """upper bounds of log P(E^c) <= log(2d) - 9/(32 Phi1) and log eps_t = log((3d/8) sup|F'| P(E^c))."""
        lp = ilog(2 * D) - ivi(9) / (32 * phi1_hi)
        le = ilog(3 * D / 8) + ilog(supF1) + lp
        return upper(lp), upper(le)

    phi1_cap = upper(iv.mpf(B_[1]) + iv.ldexp(ONE, R_CAP_LOG2))
    _, le_cap = log_tails(phi1_cap)
    need_r = upper(8 * iexp(le_cap) / pt(c1min))
    e = R_FLOOR_LOG2
    while e <= R_CAP_LOG2 and mpf_lt(LO(iv.ldexp(ONE, e)), HI(need_r)):
        e += 1
    if e > R_CAP_LOG2:
        raise RuntimeError('box radius above the cap')
    R = iv.ldexp(ONE, e)                                                # exact power of two

    Q = {0: ZERO}
    lo_min = None
    for mm in range(1, half + 1):
        lo = LO(iv.mpf(A_[mm]) - R)
        hi = HI(iv.mpf(B_[mm]) + R)
        Q[mm] = Q[d - mm] = iv.make_mpf((lo, hi))
        if lo_min is None or mpf_lt(lo, lo_min):
            lo_min = lo
    if phalf is not None:
        Q[d // 2] = iv.mpf(phalf)
    phi1_hi = upper(Q[1])
    if not mpf_le(HI(phi1_hi), HI(phi1_cap)):
        raise RuntimeError('Phi(1)+ above the a priori cap')
    lp, le = log_tails(phi1_hi)
    EPS = upper(iexp(le))                                               # eps_t (upper bound), no underflow in mpf
    log(f"tails: log P(E^c) <= {nstr(HI(lp), 6)}, log eps_t <= {nstr(HI(le), 6)}, r = 2^{e}")

    # ---- (D) and (B3) on the widened boxes
    cD, cD_m, dHmax = None, None, mp.mpf(0)
    face_left, face_right = None, None
    for mm in range(1, half + 1):
        L, _ = gs.radii(mm)
        tb = Q[mm]
        dm = gs.dH(mm, tb, L, gs.S16(mm, L, 'far'))
        dd = gs.dH(d - mm, tb, L, gs.S16(d - mm, L, 'far'))
        dHc = dm - dd
        if cD is None or mpf_lt(LO(dHc), cD):
            cD, cD_m = LO(dHc), mm
        dHmax = max(dHmax, mp.make_mpf(HI(abs(dm))), mp.make_mpf(HI(abs(dd))))
        lo_pt, hi_pt = pt(LO(tb)), pt(HI(tb))
        fl = gs.Hc(mm, lo_pt) - TAU[mm]
        fh = gs.Hc(mm, hi_pt) - TAU[mm]
        if face_left is None or mpf_gt(HI(fl), face_left):
            face_left = HI(fl)
        if face_right is None or mpf_lt(LO(fh), face_right):
            face_right = LO(fh)
    ok_D = is_pos(pt(cD)) and is_pos(pt(cD) * R - 2 * EPS)
    ok_B3 = is_neg(pt(face_left) + 2 * EPS) and is_pos(pt(face_right) - 2 * EPS)
    ok_sc = mpf_lt(sc_left, fzero) and mpf_gt(sc_right, fzero)
    ratio = mp.make_mpf(cD) / (mp.make_mpf(c1min) / 4)                  # display only (the old 'ratio_min')
    log(f"(D): inf Hc' >= {nstr(cD, 6)} (m = {cD_m}; ratio to c1min/4 = {mpmath.nstr(ratio, 6)}); faces ok: {ok_B3}")

    # ---- (B1): variogram coefficients on Q
    cosv = [icos(2 * PI * ivq(Fraction(j, d))) for j in range(d)]
    at_min, at_k = None, None
    for k in range(1, d // 2 + 1):
        s = ZERO
        for mm in range(1, half + 1):
            s += Q[mm] * cosv[(k * mm) % d]
        s = 2 * s
        if d % 2 == 0:
            s += Q[d // 2] if k % 2 == 0 else -Q[d // 2]
        wgt = ivq(Fraction(2, d)) if 2 * k != d else ivq(Fraction(1, d))
        a = -wgt * s
        if at_min is None or mpf_lt(LO(a), at_min):
            at_min, at_k = LO(a), k
    ok_B1 = mpf_gt(at_min, fzero)
    log(f"min at_k on Q >= {nstr(at_min, 6)} (k = {at_k}; d^2 min = {mpmath.nstr(mp.make_mpf(at_min) * d * d, 6)})")

    # ---- (ii): slack on Q
    W = [ZERO] * (d + 1)
    for mm in range(1, d // 2 + 1):
        W[mm] = W[d - mm] = ((Dlt[mm] - gs.HmF(mm, Q[mm])) + (Dlt[d - mm] - gs.HmF(d - mm, Q[mm]))) / 2
    w_min, w_m = None, None
    for mm in range(1, d):
        w = W[mm + 1] - 2 * W[mm] + W[mm - 1]
        if w_min is None or mpf_lt(LO(w), w_min):
            w_min, w_m = LO(w), mm
    ok_slack = is_pos(pt(w_min) - 4 * EPS)
    ok_box = mpf_gt(lo_min, fzero)
    log(f"min Delta^2 W on Q >= {nstr(w_min, 6)} (m = {w_m}; d min = {mpmath.nstr(mp.make_mpf(w_min) * d, 6)})")

    checks = dict(B1_at_positive=bool(ok_B1), B3_sign_changes=bool(ok_sc), D_derivative_times_r=bool(ok_D),
                  B3_faces_direct=bool(ok_B3), slack_exceeds_4eps=bool(ok_slack), boxes_positive=bool(ok_box))
    ok = all(checks.values())

    # ---- box digest (all m, exact)
    hsh = hashlib.sha256()
    for mm in range(1, half + 1):
        hsh.update(f"{mm} {raw_to_hex(A_[mm]._mpf_)} {raw_to_hex(B_[mm]._mpf_)} "
                   f"{raw_to_hex(LO(Q[mm]))} {raw_to_hex(HI(Q[mm]))}\n".encode())
    if phalf is not None:
        hsh.update(f"half {raw_to_hex(phalf._mpf_)}\n".encode())

    dec = raw_to_dec
    bounds = dict(
        r=dec(LO(R)), r_log2=e,
        phi1_root=[dec(A_[1]._mpf_), dec(B_[1]._mpf_)],
        phi1_box=[dec(LO(Q[1])), dec(HI(Q[1]))],
        phi_half=None if phalf is None else dec(phalf._mpf_),
        box_lo_min=dec(lo_min),
        root_width_max=dec(width_max),
        c1min_lo=dec(c1min),
        signchange_left_max_hi=dec(sc_left),
        signchange_right_min_lo=dec(sc_right),
        D_cD_lo=dec(cD), D_worst_m=cD_m,
        face_left_max_hi=dec(face_left),
        face_right_min_lo=dec(face_right),
        at_min_lo=dec(at_min), at_argk=at_k,
        slack_min_lo=dec(w_min), slack_argm=w_m,
        supF1_hi=dec(HI(supF1)),
        S1_hi=dec(HI(SK[1])), S16_hi=dec(HI(SK[16])),
        log_ptail_hi=dec(HI(lp)),
        log_eps_tail_hi=dec(HI(le)),
        dHmax_hi=dec(dHmax._mpf_),
        tail_gr1_hi=dec(HI(GTAIL[0])),
        tail_Fr_hi=dec(HI(gs.TAILF[0])),
    )
    ln10 = mp.log(10)
    approx = dict(
        d2_at_min=mpmath.nstr(mp.make_mpf(at_min) * d * d, 8),
        d_slack_min=mpmath.nstr(mp.make_mpf(w_min) * d, 8),
        ratio_D_to_c1min_over_4=mpmath.nstr(ratio, 8),
        log10_eps_tail=mpmath.nstr(mp.make_mpf(HI(le)) / ln10, 8),
        log10_cD_r_over_2eps=mpmath.nstr((mp.log(mp.make_mpf(cD) * mp.make_mpf(LO(R)) / 2) - mp.make_mpf(HI(le))) / ln10, 8),
        log10_slack_over_4eps=mpmath.nstr((mp.log(mp.make_mpf(w_min) / 4) - mp.make_mpf(HI(le))) / ln10, 8),
        r=mpmath.nstr(mp.make_mpf(LO(R)), 6),
    )
    res = dict(d=d, ok=bool(ok), checks=checks, bounds=bounds, approx=approx,
               box_sha256=hsh.hexdigest(),
               code='verify_cert.py', code_sha256=code_sha256(),
               iv_prec=PREC, search_prec=XPREC, nser=NSER, kmax=KMAX, em=[EM_N, EM_K],
               stats=dict(STATS), python=platform.python_version(), mpmath=mpmath.__version__,
               mpmath_backend=mpmath.libmp.BACKEND, secs=f"{time.time() - t0:.1f}")
    if dump_boxes:
        os.makedirs(os.path.join(QD2, 'logs', 'boxes'), exist_ok=True)
        boxes = {str(mm): [dec(A_[mm]._mpf_), dec(B_[mm]._mpf_), dec(LO(Q[mm])), dec(HI(Q[mm]))]
                 for mm in range(1, half + 1)}
        with open(os.path.join(QD2, 'logs', 'boxes', f'box_g_d{d}.json'), 'w') as fh:
            json.dump(dict(d=d, box_sha256=res['box_sha256'], boxes=boxes, phi_half=bounds['phi_half']), fh)
    return res


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    d = int(args[0])
    dump = '--dump-boxes' in sys.argv
    out = os.path.join(QD2, 'logs', f'cert_g_d{d}.json')
    try:
        res = certify(d, dump_boxes=dump)
    except Exception:
        tb = traceback.format_exc()
        with open(os.path.join(QD2, 'logs', f'cert_g_err_d{d}.txt'), 'w') as fh:
            fh.write(tb)
        print(f"d={d}: ERROR\n{tb}", flush=True)
        sys.exit(1)
    tmp = out + '.tmp'
    with open(tmp, 'w') as fh:
        json.dump(res, fh, indent=1)
    os.replace(tmp, out)
    a = res['approx']
    print(f"d={d}: CERTIFIED={res['ok']}  d^2 min at_k = {a['d2_at_min']}, d min slack = {a['d_slack_min']}, "
          f"(D) ratio = {a['ratio_D_to_c1min_over_4']}, log10 eps_t = {a['log10_eps_tail']}  [{res['secs']}s]", flush=True)


if __name__ == '__main__':
    main()
