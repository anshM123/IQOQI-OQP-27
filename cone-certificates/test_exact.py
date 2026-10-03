"""test_exact.py: G6 tests -- every interval built from an integer / rational constant must CONTAIN the exact value.
Checks the helpers of a02_jets.py and the derived tables of a03_special.py, a05_model.py, a10_pointwise.py against exact
integer/Fraction arithmetic (and, for transcendental tables, against 60-digit mpmath values).  Prints PASS/FAIL per group;
writes logs/alld/test_exact.log via the shell redirection of run_alld.sh."""
import math, sys
from fractions import Fraction as Fr
import mpmath
from mpmath import iv, mp
from a02_jets import ivq, ivfact, ivbinom, ivff, lah, lo_frac, hi_frac, grid_boxes, thin_frac
import a03_special as S
from a05_model import kj

fails = []


def contains(v, exact, name):
    lo, hi = lo_frac(v), hi_frac(v)
    if not (lo <= exact <= hi):
        fails.append(name)
        return False
    return True


# 0. the defect being fixed: a 53-bit factorial does not contain the integer
x = iv.mpf(mpmath.factorial(25))
print("0. iv.mpf(mpmath.factorial(25)) contains 25!:", lo_frac(x) <= math.factorial(25) <= hi_frac(x), "(expected False: G6)")
# 1. exact helpers
ok = all(contains(ivfact(n), math.factorial(n), f"fact {n}") for n in range(0, 200))
ok &= all(contains(ivbinom(n, k), math.comb(n, k), f"binom {n},{k}") for n in list(range(0, 300, 7)) + [783, 2400, 2403]
          for k in (0, 1, 2, 3, 5, 17, 101, 260) if k <= n)
ok &= all(contains(ivff(n, k), math.perm(n, k), f"ff {n},{k}") for n in range(0, 3001, 37) for k in (0, 1, 2, 4, 8, 14) if k <= n)
ok &= all(contains(ivq(Fr(p, q)), Fr(p, q), f"frac {p}/{q}") for p in (1, -7, 13, 10 ** 40 + 1) for q in (3, 7, 2001, 3 ** 50))
ok &= all(contains(ivq(s), Fr(s), f"dec {s}") for s in ('0.7', '0.013', '0.015', '8.38', '4.0032', '1/300', '0.0723'))
print("1. ivfact / ivbinom / ivff / ivq contain the exact values:", ok)
# 2. Lah numbers: rising factorial x^(c) = sum_i L(c,i) x_(i) (falling), checked as polynomials at integer points
ok2 = True
for c in range(1, 15):
    for xx in range(0, 25):
        rising = math.prod(range(xx, xx + c)) if c else 1
        ok2 &= rising == sum(lah(c, i) * math.perm(xx, i) for i in range(1, c + 1))
print("2. Lah numbers satisfy x^(c rising) = sum_i L(c,i) x_(i falling) (c <= 14):", ok2)
ok &= ok2
# 3. Binet coefficients beta_jk exact, rho_jl upper bounds of the exact rationals
B = {k: Fr(*[int(v) for v in mpmath.bernfrac(k)]) for k in range(0, 41, 2)}
ok3 = True
for j in range(1, 9):
    beta = S.binet_beta(j, 8)
    for k in range(1, 8):
        ex = B[2 * k] / (2 * k) * Fr(math.factorial(2 * k + 2 * j - 2), math.factorial(2 * k - 2) * math.factorial(2 * j - 2))
        ok3 &= beta[k] == ex
    rho = S.binet_rho(j, 8, 6)
    BK = abs(B[16]) / math.factorial(16)
    mu = lambda n: BK * (math.factorial(16 + n - 1) + n * math.factorial(16 + n - 2))
    for l in range(7):
        ex = sum(math.comb(l, i) * Fr(math.factorial(2 * j - 1), math.factorial(2 * j - 1 - l + i)) * mu(2 * j + i)
                 for i in range(l + 1) if l - i <= 2 * j - 1) / math.factorial(2 * j - 2)
        ok3 &= hi_frac(rho[l]) >= ex
print("3. binet_beta exact; binet_rho >= exact rational bound:", ok3)
ok &= ok3
# 4. kj(j) = 2 (2j-2)!/(2^j j!)
ok4 = all(contains(kj(j), Fr(2 * math.factorial(2 * j - 2), 2 ** j * math.factorial(j)), f"kj {j}") for j in range(1, 12))
print("4. k_j contains 2(2j-2)!/(2^j j!):", ok4)
ok &= ok4
# 5. transcendental tables against 60-digit values: g_i (zeta formula), a_n (Taylor of the closed form), polygamma
mp.dps = 60
g = lambda i: (16 * mpmath.zeta(i - 1) / mpmath.pi) * (mpmath.mpf(1) / 2 - mpmath.mpf(2) ** (1 - i)) / (mpmath.mpf(2) ** (i - 1) * (i - 1) * i)
def mcont(v, val, name, tol=Fr(1, 10 ** 50)):
    # val is a 60-digit approximation; require containment up to 1e-50 relative slack
    lo, hi = lo_frac(v), hi_frac(v)
    vv = Fr(str(mpmath.nstr(val, 58)))
    sl = abs(vv) * tol + Fr(1, 10 ** 70)
    if not (lo - sl <= vv <= hi + sl):
        fails.append(name)
        return False
    return True
ok5 = all(mcont(S.gco[i], g(i), f"g{i}") for i in list(range(3, 120, 2)) + [301, 303, 999, 2399])
ok5 &= mcont(S.gco[1], -(4 / mpmath.pi) * (1 + mpmath.log(4 / mpmath.pi)), "g1")
mp.dps = 90
g2c = lambda y: 2 / mpmath.sin(mpmath.pi * y / 2) - 4 / (mpmath.pi * y)
tay = mpmath.taylor(g2c, mpmath.mpf(1), 30)
mp.dps = 60
for n in range(2, 30):
    an = (-1) ** n * tay[n - 2] * mpmath.factorial(n - 2) / mpmath.factorial(n)
    ok5 &= mcont(S.acoef[n], an, f"a{n}", tol=Fr(1, 10 ** 40))
for nn in (1, 2, 5, 13, 21):
    for zz in (1, 2, 7, 33):
        ok5 &= mcont(S.polyg(nn, iv.mpf(zz)), mpmath.psi(nn, zz), f"psi({nn},{zz})")
print("5. g_i, a_n, psi^(n) enclosures contain 60-digit reference values:", ok5)
ok &= ok5
# 6. grid_boxes: union covers [lo, hi] exactly, consecutive boxes overlap
ok6 = True
for (lo, hi, nb) in (('0.011', '0.015', 16), ('1', '2', 20), ('0.015', '0.45', 87), ('0', '0.05', 7)):
    bx = grid_boxes(lo, hi, nb)
    ok6 &= thin_frac(bx[0][0]) <= Fr(lo) and thin_frac(bx[-1][1]) >= Fr(hi)
    ok6 &= all(thin_frac(bx[k][1]) >= thin_frac(bx[k + 1][0]) for k in range(nb - 1))
print("6. grid_boxes cover [lo, hi] exactly:", ok6)
ok &= ok6
# 7. constants of a10 / a03: G_TAIL > 8 pi/3, KT and K2j contain the exact integers
import a10_pointwise as A10
ok7 = contains(A10.KT, 16 * math.factorial(14) + Fr(16 * math.factorial(15) * 4, 5) + math.factorial(15) + Fr(math.factorial(16), 4), "KT")
ok7 &= all(contains(A10.K2j(j), 2 * j * math.factorial(2 * j - 2) + j * math.factorial(2 * j - 1) + math.factorial(2 * j - 1)
                    + Fr(math.factorial(2 * j), 4), f"K2j {j}") for j in range(1, 9))
ok7 &= hi_frac(8 * S.PI / 3) < Fr(838, 100)
print("7. a10 constants KT, K2j exact; 8 pi/3 < 8.38:", ok7)
ok &= ok7
print("FAILS:", fails[:20] if fails else "none")
print("TEST_EXACT:", "PASS" if ok and not fails else "FAIL")
sys.exit(0 if ok and not fails else 1)
