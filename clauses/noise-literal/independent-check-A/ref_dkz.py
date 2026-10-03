"""
ref_dkz.py -- referee re-check of Theorem 1(b),(c) (DKZ lower bounds and the final comparison), independent of
P2's dkz_cert.py / exact.py.

 1. DKZ behaviour from the CGLMP-paper bases (phi_a = (0, 1/2), phi_b = (1/4, -1/4), state sum_j |jj>/sqrt d,
    P(k,l) = |<k_a|<l_b|psi>|^2) at 50 digits: equals P2's closed form h_xy(b - a)/d after swapping Bob's settings;
    CGLMP value I_ME(d).
 2. certificates/dkz_d*.json: mu >= 0, sum = 1 (integers), marginals Q_xy exact; h_xy(m) enclosed with mpmath
    INTERVAL arithmetic (iv, 200 bits) -- a different enclosure method from P2's Machin/Taylor code; absorption
    condition max |Q - T^{v1}| <= (v1 - v0)/(2 d v0) decided exactly on the rational interval endpoints.
 3. Lemma 8 model built explicitly for d = 3, 4, 5 (joint law of (A0, A1, B0, B1)); link marginals = Q_xy(b-a)/d exactly.
 4. Lemma 6 (1/2-lemma) on random exact behaviours with uniform marginals (own generator; d = 2..6), plus a check that
    the hypothesis 'uniform marginals' is needed (a counter-test with non-uniform marginals fails the construction).
 5. Lemma 9 on an exact toy instance (d = 3, rational "h"), checking T^{v0} = (v0/v1) Q + (1 - v0/v1)(u + S)/2 entrywise.
 6. Final comparison: v_comp(d) < r(d) <= v0(d) for d = 4..9 (own Q(sqrt2) arithmetic), v_comp(d) < 1/2 for d >= 10
    (exact for d = 10..10^4 and the analytic monotonicity argument re-checked), and the gap 2/I_ME(d) - v0(d).
usage: python ref_dkz.py [certificate_dir]
"""
import itertools
import json
import os
import random
import sys
from fractions import Fraction as Fr

import mpmath as mp

from ref_competitor import K, R2

CERT = sys.argv[1] if len(sys.argv) > 1 else os.path.join("..", "certificates")
mp.mp.dps = 50
mp.iv.prec = 200


def raw_to_fr(raw):
    """exact value of a raw mpmath float tuple (sign, man, exp, bc)."""
    sign, man, exp, _ = raw
    v = Fr(int(man)) * (Fr(2) ** int(exp)) if exp >= 0 else Fr(int(man), 2 ** (-int(exp)))
    return -v if sign else v


def iv_to_fr(x):
    lo, hi = raw_to_fr(x._mpi_[0]), raw_to_fr(x._mpi_[1])
    assert lo <= hi
    return lo, hi


# ------------------------------------------------------------------------------------------------------------------
def part1():
    ok = True
    out = []
    for d in range(3, 11):
        w = mp.exp(2j * mp.pi / d)
        phia, phib = [0, mp.mpf(1) / 2], [mp.mpf(1) / 4, -mp.mpf(1) / 4]
        P = {}
        for xa in range(2):
            for yb in range(2):
                for k in range(d):
                    for l in range(d):
                        amp = sum(mp.conj(w ** (j * (k + phia[xa])) / mp.sqrt(d)) *
                                  mp.conj(w ** (-j * (l + phib[yb])) / mp.sqrt(d)) for j in range(d)) / mp.sqrt(d)
                        P[(xa, yb, k, l)] = abs(amp) ** 2
        delta = {(0, 0): mp.mpf(1) / 4, (0, 1): -mp.mpf(1) / 4, (1, 0): mp.mpf(3) / 4, (1, 1): mp.mpf(1) / 4}
        err = 0
        for x in range(2):
            for y in range(2):
                for a in range(d):
                    for b in range(d):
                        h = 1 / (2 * d * d * mp.sin(mp.pi * (b - a - delta[(x, y)]) / d) ** 2)
                        # P2 setting y  <->  CGLMP-paper setting 1 - y
                        err = max(err, abs(P[(x, 1 - y, a, b)] - h / d))
        # CGLMP value (BRIEF form) of P2's orientation p(a,b|x,y) = h_xy(b-a)/d
        p = lambda x, y, a, b: 1 / (2 * d ** 3 * mp.sin(mp.pi * (b - a - delta[(x, y)]) / d) ** 2)
        I = 0
        for k in range(d // 2):
            c = 1 - mp.mpf(2 * k) / (d - 1)
            for a in range(d):
                for b in range(d):
                    if (a - b - k) % d == 0: I += c * p(0, 0, a, b)
                    if (b - a - k - 1) % d == 0: I += c * p(1, 0, a, b)
                    if (a - b - k) % d == 0: I += c * p(1, 1, a, b)
                    if (b - a - k) % d == 0: I += c * p(0, 1, a, b)
                    if (a - b + k + 1) % d == 0: I -= c * p(0, 0, a, b)
                    if (b - a + k) % d == 0: I -= c * p(1, 0, a, b)
                    if (a - b + k + 1) % d == 0: I -= c * p(1, 1, a, b)
                    if (b - a + k + 1) % d == 0: I -= c * p(0, 1, a, b)
        ime = 4 / mp.mpf(d * (d - 1)) * sum((d - j) / mp.cos(mp.pi * j / (2 * d)) for j in range(1, d))
        ok &= err < mp.mpf(10) ** -40 and abs(I - ime) < mp.mpf(10) ** -40
        out.append(f"d={d}: |CGLMP-paper basis - closed form| = {mp.nstr(err, 3)}, I - I_ME = {mp.nstr(I - ime, 3)}")
    print("1. DKZ closed form = CGLMP-paper strategy with Bob's settings swapped; I = I_ME(d), d = 3..10:", ok)
    for l in out[:3]:
        print("     " + l)
    return ok


# ------------------------------------------------------------------------------------------------------------------
DELTA = {(0, 0): Fr(1, 4), (0, 1): Fr(-1, 4), (1, 0): Fr(3, 4), (1, 1): Fr(1, 4)}
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]


def h_interval(d, xy, m):
    s = Fr(m) - DELTA[xy]
    arg = mp.iv.pi * mp.iv.mpf([s.numerator, s.numerator]) / mp.iv.mpf([s.denominator * d, s.denominator * d])
    sn = mp.iv.sin(arg)
    h = 1 / (2 * d * d * sn * sn)
    lo, hi = iv_to_fr(h)
    assert 0 < lo <= hi
    return lo, hi


def load_cert(d):
    with open(os.path.join(CERT, f"dkz_d{d}.json")) as f:
        c = json.load(f)
    return c


def part2():
    ok_all = True
    v0s = {}
    for d in range(3, 21):
        c = load_cert(d)
        v1, v0, den = Fr(*c["v1"]), Fr(*c["v0"]), int(c["den"])
        ok = c["d"] == d and 0 < v0 < v1 <= 1
        Q = {xy: [Fr(0)] * d for xy in LINKS}
        tot = 0
        seen = set()
        for (m00, m01, m10), num in c["support"]:
            ok &= isinstance(num, int) and num > 0 and all(0 <= z < d for z in (m00, m01, m10))
            ok &= (m00, m01, m10) not in seen
            seen.add((m00, m01, m10))
            m11 = (m01 + m10 - m00) % d
            assert (m00 - m01 - m10 + m11) % d == 0
            tot += num
            for xy, m in zip(LINKS, (m00, m01, m10, m11)):
                Q[xy][m] += Fr(num, den)
        ok &= tot == den
        tol = (v1 - v0) / (2 * d * v0)
        worst = Fr(0)
        for xy in LINKS:
            for m in range(d):
                lo, hi = h_interval(d, xy, m)
                Tlo, Thi = v1 * lo + (1 - v1) / d, v1 * hi + (1 - v1) / d
                worst = max(worst, abs(Q[xy][m] - Tlo), abs(Q[xy][m] - Thi))
        ok &= worst <= tol
        # also: the certificate's Q has the right normalisation per link (automatic) and T^{v1} sums to 1 (enclosure)
        ok_all &= ok
        v0s[d] = v0
        print(f"   d={d:2d}: support {len(seen):3d}, max|Q - T^v1| <= {float(worst):.3e} vs tol {float(tol):.3e}  "
              f"-> v_c(DKZ_{d}) >= {float(v0):.12f}: {ok}")
    print("2. DKZ certificates re-verified with mpmath interval enclosures (200 bits):", ok_all)
    return ok_all, v0s


# ------------------------------------------------------------------------------------------------------------------
def part3():
    ok = True
    for d in (3, 4, 5):
        c = load_cert(d)
        den = int(c["den"])
        mu = {}
        for (m00, m01, m10), num in c["support"]:
            mu[(m00, m01, m10, (m01 + m10 - m00) % d)] = Fr(num, den)
        joint = {}
        for m, w in mu.items():
            for a0 in range(d):
                lam = (a0, (a0 + m[0] - m[2]) % d, (a0 + m[0]) % d, (a0 + m[1]) % d)   # (A0, A1, B0, B1)
                joint[lam] = joint.get(lam, Fr(0)) + w / d
        ok &= sum(joint.values()) == 1
        Q = {xy: [Fr(0)] * d for xy in LINKS}
        for m, w in mu.items():
            for xy, mm in zip(LINKS, m):
                Q[xy][mm] += w
        for (x, y) in LINKS:
            for a in range(d):
                for b in range(d):
                    val = sum((w for lam, w in joint.items() if lam[x] == a and lam[2 + y] == b), Fr(0))
                    ok &= val == Q[(x, y)][(b - a) % d] / d
    print("3. Lemma 8: explicit joint law of (A0,A1,B0,B1) from mu reproduces Q_xy(b-a)/d on all four links "
          "(d = 3,4,5, exact):", ok)
    return ok


# ------------------------------------------------------------------------------------------------------------------
def random_uniform_marginal_behaviour(d, rng):
    """each link = (1/d) * doubly stochastic (random rational mixture of permutation matrices)."""
    p = {}
    for x in range(2):
        for y in range(2):
            M = [[Fr(0)] * d for _ in range(d)]
            k = rng.randint(1, 5)
            ws = [Fr(rng.randint(1, 20)) for _ in range(k)]
            S = sum(ws)
            for w in ws:
                perm = list(range(d))
                rng.shuffle(perm)
                for a in range(d):
                    M[a][perm[a]] += w / S / d
            p[(x, y)] = M
    return p


def half_model(p, d):
    J = {}
    for a0, a1, b0, b1 in itertools.product(range(d), repeat=4):
        J[(a0, a1, b0, b1)] = (p[(0, 0)][a0][b0] * p[(1, 1)][a1][b1] + p[(0, 1)][a0][b1] * p[(1, 0)][a1][b0]) / 2
    return J


def links_of(J, d):
    L = {}
    for (x, y) in LINKS:
        L[(x, y)] = [[sum((w for lam, w in J.items() if lam[x] == a and lam[2 + y] == b), Fr(0))
                      for b in range(d)] for a in range(d)]
    return L


def part4():
    rng = random.Random(99)
    ok = True
    for d in range(2, 7):
        for trial in range(2 if d < 6 else 1):
            p = random_uniform_marginal_behaviour(d, rng)
            J = half_model(p, d)
            ok &= min(J.values()) >= 0 and sum(J.values()) == 1
            L = links_of(J, d)
            for xy in LINKS:
                for a in range(d):
                    for b in range(d):
                        ok &= L[xy][a][b] == (p[xy][a][b] + Fr(1, d * d)) / 2
    # the hypothesis is needed for the construction: non-uniform marginals -> link (0,1) of P_1 is not u
    d = 2
    p = {xy: [[Fr(1, 2), Fr(0)], [Fr(0), Fr(1, 2)]] for xy in LINKS}
    p[(0, 0)] = [[Fr(1), Fr(0)], [Fr(0), Fr(0)]]          # deterministic link (marginals not uniform)
    L = links_of(half_model(p, d), d)
    neg = any(L[xy][a][b] != (p[xy][a][b] + Fr(1, 4)) / 2 for xy in LINKS for a in range(2) for b in range(2))
    print("4. Lemma 6: (P1 + P2)/2 reproduces (p + u)/2 exactly on random uniform-marginal behaviours (d = 2..6):", ok,
          "| construction fails without uniform marginals (as it should):", neg)
    return ok and neg


# ------------------------------------------------------------------------------------------------------------------
def part5():
    """Lemma 9 algebra on an exact toy instance: d = 3, 'h' rational with uniform marginals."""
    d = 3
    rng = random.Random(5)
    p = random_uniform_marginal_behaviour(d, rng)
    v0, v1 = Fr(1, 3), Fr(2, 5)
    T = lambda v: {xy: [[v * p[xy][a][b] + (1 - v) / (d * d) for b in range(d)] for a in range(d)] for xy in LINKS}
    T1, T0 = T(v1), T(v0)
    # a local Q with uniform marginals close to T1: Q = T1 + E with E of zero marginals, |E| <= bound
    bound = (v1 - v0) / (2 * d * d * v0)
    E = {xy: [[Fr(0)] * d for _ in range(d)] for xy in LINKS}
    e = bound / 2
    E[(0, 0)][0][0], E[(0, 0)][0][1], E[(0, 0)][1][0], E[(0, 0)][1][1] = e, -e, -e, e
    Q = {xy: [[T1[xy][a][b] - E[xy][a][b] for b in range(d)] for a in range(d)] for xy in LINKS}
    kappa = v0 / (v1 - v0)
    S = {xy: [[Fr(1, d * d) + 2 * kappa * E[xy][a][b] for b in range(d)] for a in range(d)] for xy in LINKS}
    ok = all(S[xy][a][b] >= 0 for xy in LINKS for a in range(d) for b in range(d))
    for xy in LINKS:
        for a in range(d):
            for b in range(d):
                rhs = (v0 / v1) * Q[xy][a][b] + (1 - v0 / v1) * (Fr(1, d * d) + S[xy][a][b]) / 2
                ok &= rhs == T0[xy][a][b]
    print("5. Lemma 9 identity T^{v0} = (v0/v1) Q + (1 - v0/v1)(u + S)/2 and S >= 0 at the stated bound (exact toy):", ok)
    return ok


# ------------------------------------------------------------------------------------------------------------------
def v_even(d):
    return K(4 * (d - 1)) / ((R2 - 1) * (d * d) + 4 * (d - 1))


def v_odd(d):
    return K(4) / ((R2 - 1) * d + 4)


def part6(v0s):
    r = {4: Fr(69, 100), 5: Fr(687, 1000), 6: Fr(171, 250), 7: Fr(683, 1000), 8: Fr(341, 500), 9: Fr(681, 1000)}
    ok = True
    for d in range(4, 10):
        vc = v_even(d) if d % 2 == 0 else v_odd(d)
        ok &= (K(r[d]) - vc).sgn() > 0 and r[d] <= v0s[d]
        # stronger: v_comp(d) < v0(d) directly and < 1/2 + something irrelevant
        ok &= (K(v0s[d]) - vc).sgn() > 0
    half = K(Fr(1, 2))
    big = all((half - (v_even(d) if d % 2 == 0 else v_odd(d))).sgn() > 0 for d in range(10, 10001))
    small_fail = (v_even(8) - half).sgn() > 0 and (v_odd(9) - half).sgn() > 0
    # analytic: (sqrt2-1) d^2 - 4 d + 4 > 0 for real d >= 9 (value at 9 positive, derivative 2(sqrt2-1)d - 4 > 0 for
    # d >= 5);  (sqrt2 - 1) d - 4 > 0 for d >= 10
    an = ((R2 - 1) * 81 - 32).sgn() > 0 and ((R2 - 1) * 10 - 4).sgn() > 0 and ((R2 - 1) * 10 - 4).sgn() > 0 \
        and ((R2 - 1) * 9 - 4).sgn() < 0
    # gap to 2/I_ME (mpmath, informational)
    gaps = []
    for d in range(3, 21):
        ime = 4 / mp.mpf(d * (d - 1)) * sum((d - j) / mp.cos(mp.pi * j / (2 * d)) for j in range(1, d))
        gaps.append(2 / ime - mp.mpf(v0s[d].numerator) / v0s[d].denominator)
    print(f"6. comparison: d = 4..9 v_comp < r(d) <= v0(d): {ok}; v_comp < 1/2 for all d = 10..10000 (exact): {big}; "
          f"fails at d = 8, 9 as stated: {small_fail}; analytic tail argument: {an}; "
          f"2/I_ME - v0 in [{mp.nstr(min(gaps), 4)}, {mp.nstr(max(gaps), 4)}] (d = 3..20)")
    return ok and big and small_fail and an


if __name__ == "__main__":
    r1 = part1()
    r2, v0s = part2()
    r3 = part3()
    r4 = part4()
    r5 = part5()
    r6 = part6(v0s)
    print("RESULT:", "PASS" if all([r1, r2, r3, r4, r5, r6]) else "FAIL")
