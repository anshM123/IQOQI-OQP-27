"""
ref_zmodel.py -- referee re-verification of Lemma Z (kl-divergence/THEOREM.md) from the stored exact model only.

Independent code (not derived from zcert.py / verify_main.py):
  * link laws P_xy(m) computed per m by explicit formulas (window convolution + tail formula), Fractions;
  * exact checks: nonnegativity, kernel normalisation, total mass, positivity of every P_xy(m) used;
  * T(mu*) = (1/4) sum_xy sum_m Q log(Q/P) with Q_xy(m) = 1/(2 pi^2 (m - delta_xy)^2) on Z:
      - |m| <= M by mpmath interval arithmetic (different precision, pairwise grouping by |m|);
      - |m| > M: P >= Q proved with a rational lower bound for pi^2 (so the tail is <= 0), AND a rigorous
        two-sided enclosure of the tail (so we get the true value of T(mu*), not only an upper bound).
usage: python ref_zmodel.py [M]
"""
import sys
import json
from fractions import Fraction as Fr
from mpmath import iv, mp, mpf

iv.dps = 45
mp.dps = 45
M = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
Z = json.load(open(r"..\P4_kl\zmodel_cert_A10.json"))
A, B = int(Z["A"]), int(Z["B"])
t = Fr(Z["t"])
mu = {a: Fr(v) for a, v in zip(range(-A, A + 1), Z["mu"])}
K = {0: {}, 1: {}}
for s, key in ((0, "K0"), (1, "K1")):
    for a, row in zip(range(-A, A + 1), Z[key]):
        K[s][a] = {b: Fr(v) for b, v in zip(range(-B, B + 1), row)}

# ---------------- exact model checks
assert t > 0
assert all(v >= 0 for v in mu.values())
assert all(v >= 0 for s in K for a in K[s] for v in K[s][a].values())
assert all(sum(K[s][a].values()) == 1 for s in K for a in K[s])


def nu(a):
    """tail law of alpha (|alpha| > A)"""
    a = Fr(a)
    return t / (a * a - Fr(1, 4))


tailmass = 2 * t * Fr(1) / (A + Fr(1, 2))        # sum_{|a|>A} t/(a^2-1/4) = 2t/(A+1/2) by telescoping
# independent check of the telescoping identity on a long partial sum: S_N = 1/(A+1/2) - 1/(N+1/2)
SN = sum(Fr(1) / (Fr(a) ** 2 - Fr(1, 4)) for a in range(A + 1, 400))
assert SN == Fr(1) / (A + Fr(1, 2)) - Fr(1) / (399 + Fr(1, 2))
total = sum(mu.values()) + tailmass
assert total == 1, total
print(f"[Z1] exact: mu >= 0, kernels >= 0 and normalised, total mass = {total} (exact)")


def P(link, m):
    """exact link law of the Z-model at integer m.
    latent (alpha, b0, b1); link values: 00 -> b0, 01 -> b1, 10 -> b0 - alpha, 11 -> b1 - alpha.
    window |alpha| <= A: b_s ~ K_s(.|alpha); tail |alpha| > A: b0 in {0, alpha}, b1 in {1, alpha} w.p. 1/2 each."""
    s = 0 if link in ("00", "10") else 1
    diff = link in ("10", "11")
    val = Fr(0)
    for a in range(-A, A + 1):
        b = m + a if diff else m
        if -B <= b <= B:
            val += mu[a] * K[s][a][b]
    # tail
    if link == "00":      # b0 = 0 -> value 0 ; b0 = alpha -> value alpha
        val += (tailmass / 2 if m == 0 else 0) + (nu(m) / 2 if abs(m) > A else 0)
    elif link == "01":    # b1 = 1 -> value 1 ; b1 = alpha -> value alpha
        val += (tailmass / 2 if m == 1 else 0) + (nu(m) / 2 if abs(m) > A else 0)
    elif link == "10":    # b0 - alpha in {-alpha, 0}
        val += (tailmass / 2 if m == 0 else 0) + (nu(-m) / 2 if abs(m) > A else 0)
    else:                 # 11: b1 - alpha in {1 - alpha, 0}
        val += (tailmass / 2 if m == 0 else 0) + (nu(1 - m) / 2 if abs(1 - m) > A else 0)
    return val


delta = {"00": Fr(1, 4), "01": Fr(3, 4), "10": Fr(-1, 4), "11": Fr(1, 4)}
W = A + B + 2
# exact normalisation of each link law: window part |m| <= W + far part (pure tail) by telescoping
for L in delta:
    s_win = sum(P(L, m) for m in range(-W, W + 1))
    # for |m| > W only the tail 'far' atom contributes: nu(m')/2 with m' = m, m, -m, 1-m
    if L in ("00", "01", "10"):
        far = 2 * (t / 2) * (Fr(1) / (W + Fr(1, 2)))           # sum over |m'| > W of nu(m')/2
    else:
        # m > W -> m' = 1-m <= -W ; m < -W -> m' = 1-m >= W+2
        far = (t / 2) * (Fr(1) / (W - Fr(1, 2)) + Fr(1) / (W + 1 + Fr(1, 2)))
    assert s_win + far == 1, (L, s_win + far)
print("[Z2] exact: each link law sums to 1 over Z")

# ---------------- interval sum |m| <= M
PI = iv.pi
LN2 = iv.log(iv.mpf(2))


def ivfr(x):
    x = Fr(x)
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)


Tlinks = {}
minP = None
for L, dl in delta.items():
    acc = iv.mpf(0)
    for n in range(0, M + 1):
        for m in ((0,) if n == 0 else (n, -n)):
            p = P(L, m) if abs(m) <= W else (nu(m) / 2 if L in ("00", "01") else (nu(-m) / 2 if L == "10" else nu(1 - m) / 2))
            assert p > 0
            if minP is None or (abs(m) <= W and p < minP):
                minP = p
            q = 1 / (2 * PI ** 2 * (iv.mpf(m) - ivfr(dl)) ** 2)
            acc += q * (iv.log(q) - iv.log(ivfr(p)))
    Tlinks[L] = acc
Tfin = sum(Tlinks.values(), iv.mpf(0)) / 4
print(f"[Z3] min_window P = {float(minP):.3e} > 0; per-link finite sums (nats): " +
      ", ".join(f"{L}: {float(mpf(v.mid)):.15f}" for L, v in Tlinks.items()))

# ---------------- tail |m| > M
# (a) P >= Q for |m| > M: t pi^2 (m-delta)^2 >= m'^2 - 1/4 with |m - delta| >= |m| - 3/4, |m'| <= |m| + 1.
pi_lo = Fr(314159265, 100000000)               # pi > 3.14159265
assert ivfr(pi_lo) < PI
c_lo = t * pi_lo ** 2
assert c_lo > 1
# need c_lo (n - 3/4)^2 >= (n+1)^2 for all n >= M+1; LHS - RHS is convex quadratic in n, check derivative and value
n0 = M + 1
assert c_lo * (n0 - Fr(3, 4)) ** 2 - (n0 + 1) ** 2 >= 0
assert 2 * c_lo * (n0 - Fr(3, 4)) - 2 * (n0 + 1) >= 0       # increasing from n0 on (convex)
# smallest n from which the inequality holds (information only)
nmin = next(n for n in range(1, 10 ** 4) if all(c_lo * (k - Fr(3, 4)) ** 2 >= (k + 1) ** 2 for k in (n, n + 1)))
print(f"[Z4] P >= Q for all |m| > {M} (exact rational, pi > 3.14159265; holds from |m| >= {nmin}): tail <= 0")

# (b) rigorous enclosure of the tail sum: for |m| > M, Q log(Q/P) = Q * log(R), R = (m'^2 - 1/4)/(t pi^2 (m-delta)^2)
#     R in [Rlo(n), Rhi(n)] with n = |m|; Q in [Qlo(n), Qhi(n)];  log R <= 0 so Q log R in [Qhi*log Rlo, Qlo*log Rhi].
#     Sum over n > M of 1/(n +- 3/4)^2 is bounded by integrals.
#     log R in [log(((n-1)^2 - 1/4)/(c_hi (n+3/4)^2)), log(((n+1)^2)/(c_lo (n-3/4)^2))]; both -> -log(t pi^2).
c_hi = t * Fr(314159266, 100000000) ** 2
assert ivfr(Fr(314159266, 100000000)) > PI
n1 = M + 1
logR_lo = iv.log(ivfr(((Fr(n1) - 1) ** 2 - Fr(1, 4)) / (c_hi * (Fr(n1) + Fr(3, 4)) ** 2)))   # worst (most negative) for n >= n1
logR_hi = iv.log(ivfr((Fr(n1) + 1) ** 2 / (c_lo * (Fr(n1) - Fr(3, 4)) ** 2)))               # largest for n >= n1 ... (*)
# (*) ((n+1)/(n-3/4))^2 is decreasing in n, ((n-1)^2-1/4)/(n+3/4)^2 is increasing in n -> bounds valid for all n >= n1
assert logR_hi.b <= 0
# per link: sum_{|m|>M} Q(m) in [Slo, Shi], Q(m) = 1/(2 pi^2 (m-delta)^2); sum_{|m|>M} 1/(m-delta)^2 over both signs:
#   lower: 2 * sum_{n>M} 1/(n+3/4)^2 >= 2/(M+1+3/4)  ; upper: 2 * sum_{n>M} 1/(n-3/4)^2 <= 2/(M - 3/4)
Slo = 2 / (2 * PI ** 2 * (M + iv.mpf(1) + iv.mpf(3) / 4))
Shi = 2 / (2 * PI ** 2 * (M - iv.mpf(3) / 4))
tail_lo = Shi * logR_lo          # most negative possible
tail_hi = Slo * logR_hi          # least negative possible
print(f"[Z5] per-link tail sum in [{float(mpf(tail_lo.a)):.3e}, {float(mpf(tail_hi.b)):.3e}] nats")
T_up = mpf((Tfin / LN2).b)
T_lo = mpf(((Tfin + tail_lo) / LN2).a)
T_up_with_tail = mpf(((Tfin + tail_hi) / LN2).b)
print(f"[Z6] CERTIFIED T(mu*) <= {float(T_up):.12f} bits (tail dropped, as in the theorem)")
print(f"[Z6] two-sided enclosure: T(mu*) in [{float(T_lo):.12f}, {float(T_up_with_tail):.12f}] bits")
print(f"[Z7] competitor bound 0.0703203697 - T_up = {0.0703203697 - float(T_up):.9f} bits")
