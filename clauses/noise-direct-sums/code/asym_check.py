"""asym_check.py -- the two n-independent rigorous computations of the large-n proof (n >= 50001, S >= 50000).

(A) Region A (1 <= y, s <= 200): the n = oo quantities, with the finite-n perturbation allowances derived in PROOF_PHI.md
    (eps_bar = 401/24999 for w_out, delta_c = 6e-6 for c_n, absolute slacks 1e-8 etc.), satisfy
      (A-L)  lower capacity,  (A-U) upper capacity,  (A-P1) U > 0,  (A-P2) Q >= 0.
    Exact rationals for rho, phi, F, M1; mpmath interval for c_oo = 8/(pi^2 (2 - 16 C/pi^2)), C = Catalan
    (Ramanujan's series C = (pi/8) log(2+sqrt3) + (3/8) sum (n!)^2/((2n)! (2n+1)^2), tail bounded geometrically).
(B) the one-dimensional inequality (Region B, y,s >= 201):
      H(x) = (4/3) Phi1 [1 + 1.0001 x^2 ((1-x)^-2 - 1)] - (4/3)(k/c_oo) g(x) + 0.0017
           <= (0.9925/16) (pi xt)^2 / sin^2(pi xt),   xt = x (1 - 2e-5),   for 0 < x <= 1/2,
    g = 4 log 2 - 2 on [0,1/4], g = 4(2x - 1 - log 2x) on [1/4,1/2]  (H increasing in x, RHS increasing in x:
    checked on a grid with H(x_{i+1}) <= RHS(x_i)).
"""
from fractions import Fraction as Fr
import mpmath
from mpmath import iv

iv.dps = 40


def catalan_iv():
    s = iv.mpf(0); term_bound = None
    N = 80
    import math
    for nn in range(N):
        num = math.factorial(nn) ** 2; den = math.factorial(2 * nn) * (2 * nn + 1) ** 2   # exact integers
        g = math.gcd(num, den); num //= g; den //= g
        s += iv.mpf(num) / iv.mpf(den)
    # tail: term ratio (n+1)^2 (2n+1)^2 / ((2n+2)(2n+1)(2n+3)^2) < 1/4 ; tail <= t_N * 4/3, t_N <= 4^-N
    tail = iv.mpf([0, mpmath.mpf(4) ** (-N) * 2])
    s += tail
    return iv.pi / 8 * iv.log(2 + iv.sqrt(3)) + iv.mpf(3) / 8 * s


C = catalan_iv()
PHI1 = iv.pi / 16 + iv.pi ** 2 / 32 - C / 2
KINF = 16 * C / iv.pi ** 2
CINF = 8 / (iv.pi ** 2 * (2 - KINF))
K = Fr(1, 50)


def rho(j):
    if j <= 0: return Fr(0)
    return K * min(Fr(1), Fr(j, 3)) / (j * (j + 1))


def phi_(t):
    return Fr(8 * (2 * t + 1), (4 * t + 1) ** 2 * (4 * t + 3) ** 2)


def ivf(fr):
    return iv.mpf(fr.numerator) / fr.denominator


def region_A(Y0=200):
    eps_bar = Fr(401, 24999)
    dc = iv.mpf('6e-6')
    AF = {t: 3 * rho(t) + rho(t - 1) - rho(t // 2) for t in range(1, Y0 + 2)}
    F = {0: Fr(0)}; M1 = {0: Fr(0)}
    for t in range(1, Y0 + 1):
        F[t] = F[t - 1] + t * AF[t]
        M1[t] = M1[t - 1] + t * phi_(t)
    U = {y: CINF * ivf(M1[y]) - ivf(F[y]) for y in range(0, Y0 + 1)}
    ok = True; worst = {'L': 0, 'U': 0}; minU = None; minQ = None
    for y in range(1, Y0 + 1):
        Uplus = U[y] + ivf(eps_bar * F[y]) + iv.mpf('1e-8')
        lhs = iv.mpf(4) / 3 * Uplus / (y * (y + 1)) + 2 * ivf(rho(y)) + iv.mpf(2) / 3 * ivf(rho(y - 1)) + iv.mpf('1e-9')
        rhs = CINF * (1 - dc) / (4 * y + 1) ** 2
        r = float(lhs.b) / float(rhs.a)
        worst['L'] = max(worst['L'], r)
        if not (lhs.b < rhs.a): ok = False; print("A-L FAIL", y)
        pu = mpmath.mpf(float(U[y].a)) - mpmath.mpf('1.1e-5') if False else (U[y] - iv.mpf('1.1e-5')).a
        if not pu > 0: ok = False; print("A-P1 FAIL", y)
        minU = float(pu) if minU is None else min(minU, float(pu))
    for s in range(2, Y0 + 1):
        Up = U[s - 1] + ivf(eps_bar * F[s - 1]) + iv.mpf('1e-8')
        Dm = (1 - dc) * CINF * ivf(phi_(s)) - iv.mpf('1e-14')
        pos = 3 * rho(s) + rho(s - 1)
        num = 4 * Up - 2 * s * (s - 1) * Dm + 2 * s * (s - 1) * (ivf(pos) + iv.mpf('2.4e-10') + iv.mpf('1e-14'))
        lhs = num / (3 * s * (s + 1)) + iv.mpf(4) / (3 * (s + 1)) * ivf(rho(s // 2)) + iv.mpf('1e-12')
        rhs = CINF * (1 - dc) / (4 * s + 3) ** 2
        r = float(lhs.b) / float(rhs.a)
        worst['U'] = max(worst['U'], r)
        if not (lhs.b < rhs.a): ok = False; print("A-U FAIL", s)
        Dp = CINF * ivf(phi_(s)) + iv.mpf('1e-14')
        neg = (1 - eps_bar) * pos - rho(s // 2)
        Q = 4 * (U[s - 1] - iv.mpf('1.1e-5')) - 2 * s * (s - 1) * Dp + 2 * s * (s - 1) * ivf(neg)
        if not Q.a >= 0: ok = False; print("A-P2 FAIL", s, Q)
        q = float(Q.a) / float((4 * U[s - 1]).b)
        minQ = q if minQ is None else min(minQ, q)
    return ok, worst, minU, minQ


def H_up(x, k_over_c_lo):
    """upper bound of H at the point x (given as mpf); uses g monotone (decreasing) -> evaluate at x."""
    X = iv.mpf(x)
    if X.b <= 0.25:
        g = 4 * iv.log(2) - 2
    else:
        g = 4 * (2 * X - 1 - iv.log(2 * X))
    first = iv.mpf(4) / 3 * PHI1 * (1 + iv.mpf('1.0001') * X ** 2 * ((1 - X) ** -2 - 1))
    return (first - iv.mpf(4) / 3 * k_over_c_lo * g + iv.mpf('0.0017')).b


def rhs_lo(x):
    if x == 0:
        return (iv.mpf('0.9925') / 16).a
    xt = iv.mpf(x) * (1 - iv.mpf('2e-5'))
    t = iv.pi * xt
    return (iv.mpf('0.9925') / 16 * t ** 2 / iv.sin(t) ** 2).a


def oneD(N=2000):
    k_over_c = ivf(K) / CINF          # interval; g >= 0 so use its lower end for an upper bound of -(4/3)(k/c)g
    kc_lo = iv.mpf(k_over_c.a)
    ok = True; worst = 0
    for i in range(N):
        xa = mpmath.mpf(i) / (2 * N); xb = mpmath.mpf(i + 1) / (2 * N)
        h = H_up(xb, kc_lo)
        r = rhs_lo(xa)
        worst = max(worst, float(h) / float(r))
        if not h < r:
            ok = False; print("1D FAIL at cell", float(xa), float(xb), float(h), float(r))
    return ok, worst


if __name__ == '__main__':
    print("Catalan", C, "\nPhi1", PHI1, "\nkappa_oo", KINF, "\nc_oo", CINF)
    okA, worstA, minU, minQ = region_A()
    print(f"Region A (y,s <= 200, n >= 50001): {'PASS' if okA else 'FAIL'}; worst lower ratio {worstA['L']:.4f}, "
          f"worst upper ratio {worstA['U']:.4f}, min U lower bound {float(minU):.3e}, min Q/(4U) {float(minQ):.3f}")
    okB, worstB = oneD()
    print(f"1D inequality on (0,1/2] (2000 cells): {'PASS' if okB else 'FAIL'}; worst H(x_b)/RHS(x_a) = {worstB:.4f}")
