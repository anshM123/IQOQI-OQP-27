"""a03: rigorous special-function layer for the all-d proof.
 g_i  : Taylor coefficients of g_r at 0 (odd i), |g_i| <= 8.38/(2^i i (i-1)) for odd i >= 3 (from |B_2n| <= 2(2n)! zeta(2n)/(2pi)^2n).
 a_n  : (-1)^n g_r^(n)(1)/n! = (-1)^n sum_{i>=n} g_i C(i,n)  (so g_r(1-x) = sum_n a_n x^n), interval incl. tail.
 polyg(n, z): psi^(n)(z) for real interval z >= 1 (recurrence to z+N >= 30, asymptotic series, remainder
       |R_K^(n)(y)| <= |B_2K| (2K+n-1)!/((2K)! y^(2K+n))  (as in QD2-L12)).
 kappa(n, b) = n psi^(n-1)(b+1) + b psi^(n)(b+1) = d^n/db^n [b psi(b+1)].
 Binet B_2j(b) = b^(2j-1) kappa_2j(b)/(2j-2)! = 1 - sum_{k=1}^{K-1} beta_jk b^(-2k) + Rt_j(b),
       beta_jk = (B_2k/(2k)) (2k+2j-2)!/((2k-2)! (2j-2)!),  |Rt_j^(l)(b)| <= rho_jl b^(-2K-l)."""
import math
import mpmath
from mpmath import iv, mp
from fractions import Fraction as Fr
from a02_jets import Jet, Space, Z, ONE, ivq, ivfact, ivbinom, ivff, lah

PI = iv.pi
FACT = [math.factorial(k) for k in range(200)]          # EXACT integers (G6); converted with iv.mpf(int) (outward) at use


def ivF(q):
    return ivq(q)


BERN = {k: Fr(*[int(v) for v in mpmath.bernfrac(k)]) for k in range(0, 61, 2)}

# ---------------------------------------------------------------- g_i and a_n
# exact: g_i = (16 zeta(i-1)/pi) (1/2 - 2^(1-i)) / (2^(i-1) (i-1) i) for odd i >= 3 (|B_2n| = 2 (2n)! zeta(2n)/(2pi)^2n);
# for i <= IMAX zeta(i-1) via exact Bernoulli numbers, beyond via 1 <= zeta(s) <= 1 + 2^-s + 2^(1-s)/(s-1).
IMAX = 301
IBIG = 2400
gco = {1: -(4 / PI) * (1 + iv.log(4 / PI))}
for n in range(1, (IMAX - 1) // 2 + 1):
    p, q = mpmath.bernfrac(2 * n)
    Bn = abs(iv.mpf(int(p)) / iv.mpf(int(q)))
    gco[2 * n + 1] = (8 / PI ** 2) * Bn / (2 * n * ivfact(2 * n + 1)) * PI ** (2 * n + 1) * (iv.mpf(1) / 2 - iv.mpf(4) ** (-n))
for i in range(IMAX + 2, IBIG + 1, 2):
    s_ = i - 1
    zeta = iv.mpf([1, 1]) + iv.mpf([0, 1]) * (iv.mpf(2) ** (-s_) + iv.mpf(2) ** (1 - s_) / (s_ - 1))
    gco[i] = (16 * zeta / PI) * (iv.mpf(1) / 2 - iv.mpf(2) ** (1 - i)) / (iv.mpf(2) ** (i - 1) * (i - 1) * i)


def g(i):
    return gco.get(i, Z) if i % 2 == 1 else Z


# |g_i| = 16 zeta(i-1)(1/2 - 2^(1-i))/(pi 2^(i-1)(i-1) i) <= (8 pi/3)/(2^i i (i-1)) (zeta(i-1) <= zeta(2) = pi^2/6), and 8 pi/3 < 8.38
G_TAIL = ivq('8.38')
assert (8 * PI / 3).b < G_TAIL.a


def gtail_abs(i):
    """upper bound of |g_i| for odd i >= 3."""
    return G_TAIL / (iv.mpf(2) ** i * i * (i - 1))


NA = 260
acoef = {}
for n in range(0, NA + 1):
    s = Z
    I = max(3 * n + 3, 201)
    I = I + 1 if I % 2 == 0 else I
    assert I <= IBIG
    for i in range(max(n, 1), I + 1):
        if i % 2 == 1:
            s += gco[i] * ivbinom(i, n)
    # tail over odd i > I: terms 8.38 C(i,n)/(2^i i(i-1)) with ratio (i -> i+2) <= 9/16 for i >= 3n
    i0 = I + 2
    tail = gtail_abs(i0) * ivbinom(i0, n) / (1 - iv.mpf(9) / 16)
    acoef[n] = ((-1) ** n) * (s + iv.mpf([-tail.b, tail.b]))


def a(n):
    return acoef[n]


# |a_n| <= sum_{i>=n} |g_i| C(i,n) <= (8.38/(n(n-1))) sum_{i>=n} C(i,n) 2^-i = 16.76/(n(n-1))   (n >= 2)
A_TAIL = 2 * G_TAIL                                    # = 16.76 exactly (enclosure)


def a_bound(n):
    assert n >= 2
    return A_TAIL / (n * (n - 1))


# ---------------------------------------------------------------- polygamma
def polyg(n, z, K=12):
    """psi^(n)(z), n >= 1, z: real interval with z.a >= 1."""
    z = iv.mpf(z)
    N = max(0, int(30 - float(z.a)) + 1)
    acc = Z
    sgn = 1 if n % 2 == 0 else -1               # (-1)^n
    fn = iv.mpf(FACT[n])
    for l in range(N):
        acc += sgn * fn / (z + l) ** (n + 1)
    y = z + N
    s = iv.mpf(FACT[n - 1]) / y ** n + fn / (2 * y ** (n + 1))
    for k in range(1, K):
        s += ivq(BERN[2 * k] * Fr(FACT[2 * k + n - 1], FACT[2 * k])) / y ** (2 * k + n)
    rem = ivq(abs(BERN[2 * K]) * Fr(FACT[2 * K + n - 1], FACT[2 * K])) / y ** (2 * K + n)
    s = s + iv.mpf([-rem.b, rem.b])
    return (-sgn) * s - acc


def kappa(n, b):
    b = iv.mpf(b)
    return n * polyg(n - 1, b + 1) + b * polyg(n, b + 1)


# ---------------------------------------------------------------- Binet functions B_2j as jets
def binet_beta(j, K):
    """exact beta_jk, k = 1..K-1:  B_2j(b) = 1 - sum_k beta_jk b^-2k + Rt."""
    return [None] + [BERN[2 * k] / (2 * k) * Fr(FACT[2 * k + 2 * j - 2], FACT[2 * k - 2] * FACT[2 * j - 2])
                     for k in range(1, K)]


def binet_rho(j, K, L):
    """rho_jl (l = 0..L) with |Rt_j^(l)(b)| <= rho_jl b^(-2K-l) for b > 0  (exact rationals, enclosed outward)."""
    BK = abs(BERN[2 * K]) / FACT[2 * K]
    mu = lambda n: BK * (FACT[2 * K + n - 1] + n * FACT[2 * K + n - 2])
    out = []
    for l in range(L + 1):
        s = Fr(0)
        for i in range(l + 1):
            if l - i <= 2 * j - 1:
                s += math.comb(l, i) * Fr(FACT[2 * j - 1], FACT[2 * j - 1 - l + i]) * mu(2 * j + i)
        out.append(ivq(s / FACT[2 * j - 2]).b)
    return out


def binet_near(j, W, wmax, K=8):
    """B_2j(1/W) for a jet W whose range lies in [0, wmax]: exact polynomial part + enclosed remainder (Lah-number transfer)."""
    T = W.S.T
    beta = binet_beta(j, K)
    rho = binet_rho(j, K, T)
    W2 = W * W
    out = Jet.const(W.S, ONE)
    P = Jet.const(W.S, ONE)
    for k in range(1, K):
        P = P * W2
        out = out - P * ivF(beta[k])
    wm = iv.mpf(wmax)
    F = [iv.mpf([-1, 1]) * rho[0] * wm ** (2 * K)]
    for c in range(1, T + 1):
        assert 2 * K - c >= 0
        bnd = sum(iv.mpf(lah(c, i)) * rho[i] for i in range(1, c + 1)) * wm ** (2 * K - c) / ivfact(c)
        F.append(iv.mpf([-1, 1]) * bnd)
    return out + W.compose1(F)


def binet_far_bjet(j, bbox, order):
    """F[k] = enclosure of (d/db)^k B_2j(b)/k! over the interval bbox (b >= 1), k = 0..order (naive, via kappa_{2j+k})."""
    S1 = Space(order, 0, order)
    Bv = Jet.var(S1, 0, bbox)
    Kj = Jet(S1, [kappa(2 * j + k, bbox) / ivfact(k) for k in range(order + 1)])
    J = (Bv ** (2 * j - 1)) * Kj * (ONE / ivfact(2 * j - 2))
    return J.c


def binet_far(j, W, order_extra=0):
    """B_2j(1/W) for a jet W with range in [w_lo, w_hi], w_lo > 0 (b = 1/W in [1/w_hi, 1/w_lo], b >= 1)."""
    Bj = W.recip()
    bbox = Bj.c[0]
    F = binet_far_bjet(j, bbox, W.S.T)
    return Bj.compose1(F)


def tight_1d(fun, box, T, E=6):
    """enclosures F[k] (k = 0..T) of f^(k)/k! over the interval box, for a 1-D function given as fun(jet) -> jet:
    c_k(b) = sum_{l<E} C(k+l,l) c_{k+l}(b_c) h^l + C(k+E,E) c_{k+E}(xi) h^E  (Taylor, h = b - b_c), with c(b_c) from a thin jet
    and c_{k+E}(xi) from the naive jet over the box."""
    box = iv.mpf(box)
    bc = iv.mpf(box.mid)
    S = Space(T + E, 0, T + E)
    Jc = fun(Jet.var(S, 0, bc))
    Jb = fun(Jet.var(S, 0, box))
    h = box - bc
    F = []
    for k in range(T + 1):
        s = Z
        for l in range(E):
            s += ivbinom(k + l, l) * Jc.c[k + l] * h ** l
        s += ivbinom(k + E, E) * Jb.c[k + E] * h ** E
        F.append(s)
    return F


def binet_w(j, W, wmax_near=iv.mpf(1) / 20):
    """B_2j(1/W) for a jet W (range within [0, 1]); near form if range within [0, wmax_near], else tight far form."""
    rng = W.c[0]
    if rng.b <= wmax_near:
        return binet_near(j, W, rng.b)
    T = W.S.T
    F = tight_1d(lambda V: binet_far(j, V), rng, T)
    return W.compose1(F)
