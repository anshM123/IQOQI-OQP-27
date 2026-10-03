"""QD2-L12 (rigorous): the boundary sequence a(m) = 1/6 - f(m), f(m) = m^2 (1/B(m) - 1), B(m) = m kappa_2(m),
kappa_2(b) = 2 psi'(b+1) + b psi''(b+1), f(0) := 0, is positive, convex on m >= 0, decreases to 0, and m^2 a(m) <= 0.0723.
Consequently (Fejer/Polya, RIGOR_ALLD.md s.4) A(theta) := a(0) + 2 sum_{m>=1} a(m) cos(m theta) >= Delta^2 a(1) = 2 f(1) - f(2).
Part 1: interval arithmetic (mpmath.iv, 240 bits) for 1 <= m <= M0, with psi'(m+1) = zeta(2) - H_m^(2),
        psi''(m+1) = -2 (zeta(3) - H_m^(3)); zeta(2) = pi^2/6 (iv.pi), zeta(3) enclosed by the alternating series
        zeta(3) = (5/2) sum_{k>=1} (-1)^(k+1)/(k^3 C(2k,k)) (exact rational partial sums S_N, S_{N+1} bracket it).
Part 2: m > M0 via the Binet remainder: B(b) = 1 - 1/(6b^2) + 1/(10b^4) - 5/(42b^6) + rho, |rho| <= 11/(30 b^8)
        (|R_K^(n)(z)| <= |B_2K| (2K+n-1)!/((2K)! z^(2K+n)) for the psi expansion; rho = b(2R' + bR''), K = 4),
        whence f = 1/6 - c2 w^2 + c4 w^4 + E, |E| <= C6(W) w^6 for 0 <= w = 1/b <= W, and
        Delta^2 a(m) >= 6 c2/m^4 - (20 c4 + 4 C6)/(m-1)^6 > 0 for m >= M0 + 1 (stencil w <= 1/M0).
Outputs logs/alld/polya.json: Amin (exact lower bound of 2f(1) - f(2)), tail constant 0.0723 (m^2 a(m) <= 0.0723, all m >= 1),
        c2, c4 (exact), C6 for b >= 1000 (used by a09_smallm.py at b = d - j >= 1997) and for b >= M0."""
import sys, json, math
from fractions import Fraction as Fr
import mpmath
from mpmath import iv, mp
sys.path.insert(0, '.')
from a02_jets import ivq, lo_str, hi_str, lo_frac, hi_frac
iv.prec = 240                         # (after the import: a02_jets sets iv.prec = 120)

M0 = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
Z2 = iv.pi ** 2 / 6
# zeta(3): alternating series with terms t_k = 1/(k^3 C(2k,k)) strictly decreasing -> S_N, S_{N+1} bracket the sum
NZ = 140
S = Fr(0)
partial = []
for k in range(1, NZ + 2):
    S += Fr((-1) ** (k + 1), k ** 3 * math.comb(2 * k, k))
    partial.append(S)
lo3, hi3 = sorted([Fr(5, 2) * partial[-2], Fr(5, 2) * partial[-1]])
Z3 = iv.mpf([ivq(lo3).a, ivq(hi3).b])
assert Z3.b - Z3.a < iv.mpf(2) ** -230
assert abs(float(lo3) - float(mpmath.zeta(3))) < 1e-15        # sanity only
H2 = iv.mpf(0); H3 = iv.mpf(0)
f = [iv.mpf(0)]
for m in range(1, M0 + 2):
    H2 += iv.mpf(1) / (m * m); H3 += iv.mpf(1) / (m * m * m)
    p1 = Z2 - H2; p2 = -2 * (Z3 - H3)
    Bm = m * (2 * p1 + m * p2)
    f.append(m * m * (1 / Bm - 1))
a = [iv.mpf(1) / 6 - x for x in f]
d2 = [None] + [a[m - 1] - 2 * a[m] + a[m + 1] for m in range(1, M0 + 1)]
neg = [m for m in range(1, M0 + 1) if not d2[m].a > 0]
apos = all(a[m].a > 0 for m in range(1, M0 + 2))
m2a = max((a[m] * m * m).b for m in range(1, M0 + 2))
print("f(1) =", mpmath.nstr(f[1].mid, 12), " f(2) =", mpmath.nstr(f[2].mid, 12), " Delta^2 a(1) = 2f(1)-f(2) in", d2[1])
print("   closed forms: f(1) = 1/(pi^2/3 - 2 zeta(3)) - 1, f(2) = 1/(pi^2/6 + 1 - 2 zeta(3)) - 4:",
      bool(abs((f[1] - (1 / (iv.pi ** 2 / 3 - 2 * Z3) - 1)).b) < 1e-60 and abs((f[2] - (1 / (Z2 + 1 - 2 * Z3) - 4)).b) < 1e-60))
print("Part 1: Delta^2 a(m) > 0 for all 1 <= m <=", M0, ":", not neg, " min m^4 Delta^2 a(m) (m>=10) =",
      mpmath.nstr(min((d2[m] * m ** 4).a for m in range(10, M0 + 1)), 8), "; a(m) > 0 (m <= M0+1):", apos)
print("   max m^2 a(m) over 1..M0+1 =", mpmath.nstr(m2a, 10))

# Part 2: exact series arithmetic in w with an interval remainder
c2 = Fr(13, 180); c4 = Fr(5, 42) - Fr(1, 30) + Fr(1, 216)
assert c4 == Fr(683, 7560)


def pmul(p, q):
    r = {}
    for i, x in p.items():
        for j, z in q.items():
            r[i + j] = r.get(i + j, 0) + x * z
    return r


Y0 = {2: Fr(1, 6), 4: Fr(-1, 10), 6: Fr(5, 42)}            # exact polynomial part of y = 1 - B
Y02 = pmul(Y0, Y0); Y03 = pmul(Y02, Y0)
P = {}
for q in (Y0, Y02, Y03):
    for k, v in q.items():
        P[k] = P.get(k, 0) + v
P[2] -= Fr(1, 6); P[4] += c2; P[6] -= c4
assert all(P.get(k, 0) == 0 for k in (2, 4, 6)), P
# Binet remainder of B (K = 4): |rho| <= mu(2) b^-8, mu(2) = |B_8|/8! (9! + 2 * 8!) = 11/30 (exact)
B8 = Fr(*[int(v) for v in mpmath.bernfrac(8)])
RHO = abs(B8) / math.factorial(8) * (math.factorial(9) + 2 * math.factorial(8))
assert RHO == Fr(11, 30)


def C6_of(W):
    """|E| <= C6 w^6 for 0 <= w <= W:  w^2 E = P(w) + (y - y0)(1 + y + y0 + y^2 + y y0 + y0^2) + y^4/(1 - y)."""
    W = ivq(W)
    Y = W ** 2 / 6 + W ** 4 / 10 + 5 * W ** 6 / 42 + ivq(RHO) * W ** 8          # |y|, |y0| <= Y
    Yw = iv.mpf(1) / 6 + W ** 2 / 10 + 5 * W ** 4 / 42 + ivq(RHO) * W ** 6        # Y/w^2
    Pw8 = sum((abs(ivq(v)) * W ** (k - 8) for k, v in P.items() if k >= 8 and v != 0), iv.mpf(0))
    assert Y.b < 1
    return (Pw8 + ivq(RHO) * (1 + 2 * Y + 3 * Y ** 2) + Yw ** 4 / (1 - Y)).b


C6_M0 = C6_of(Fr(1, M0))
C6_1000 = C6_of(Fr(1, 1000))
print("Part 2: c2 = 13/180, c4 =", c4, "=", float(c4), "; C6 <=", mpmath.nstr(C6_M0, 8), "(b >=", M0, "),",
      mpmath.nstr(C6_1000, 8), "(b >= 1000)")
m = M0 + 1                                                  # stencil m-1, m, m+1 has w <= 1/M0
lhs = 6 * ivq(c2) / iv.mpf(m) ** 4
rhs = (20 * ivq(c4) + 4 * C6_M0) / iv.mpf(m - 1) ** 6
ok2 = (lhs - rhs).a > 0
# (m-1)^6/m^4 increases with m, so the check at m = M0 + 1 covers every m >= M0 + 1
print("   convexity for m >= M0+1: at m = M0+1:", mpmath.nstr(lhs.a, 6), ">", mpmath.nstr(rhs.b, 6), ":", ok2)
# positivity and the tail constant for m >= M0: a(m) = c2 w^2 - c4 w^4 - E,  m^2 a(m) <= c2 + C6 w^4,  m^2 a(m) >= c2 - c4 w^2 - C6 w^4
W0 = ivq(Fr(1, M0))
pos2 = (ivq(c2) - ivq(c4) * W0 ** 2 - C6_M0 * W0 ** 4).a > 0
TAILC = ivq('0.0723')
tail2 = (ivq(c2) + C6_M0 * W0 ** 4).b < TAILC.a
tail1 = m2a < TAILC.a
print("   a(m) > 0 for m >= M0:", pos2, "; m^2 a(m) <= 0.0723 for all m >= 1:", bool(tail1 and tail2),
      "(hence 2 sum_{m>=d} a(m) <= 0.1446/(d-1))")
ok = (not neg) and apos and ok2 and pos2 and tail1 and tail2
print("QD2-L12:", ok, "; A(theta) >= 2f(1) - f(2) >=", mpmath.nstr(d2[1].a, 15))
json.dump(dict(ok=bool(ok), M0=M0, Amin=lo_str(d2[1]), Amin_hi=hi_str(d2[1]), Amin_f=float(d2[1].a),
               f1=[lo_str(f[1]), hi_str(f[1])], f2=[lo_str(f[2]), hi_str(f[2])],
               tailc='0.0723', c2=str(c2), c4=str(c4), C6_b1000=hi_str(C6_1000), C6_bM0=hi_str(C6_M0),
               max_m2a=hi_str(m2a), iv_prec=iv.prec), open('logs/alld/polya.json', 'w'), indent=0)
