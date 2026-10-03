"""
Step 6 helper: independent re-check of noise-literal/certificates/dkz_d{d}.json with OWN code.

P2 format: {"d", "v1": [num, den], "v0": [num, den], "den": D, "support": [[[m00, m01, m10], numerator], ...]},
mu(m00,m01,m10) = numerator/D, m11 = m01 + m10 - m00 mod d.
P2 claim (THEOREM.md Lemma 9, covariant form): if mu is a probability distribution and
    |Q_xy(m) - T_xy(m)| <= (v1 - v0)/(2 d v0)  for all xy, m,   T_xy(m) = v1 h_xy(m) + (1 - v1)/d,
then v_c(DKZ_d) >= v0.  (Own re-derivation of Lemma 9 in the report: T^{v0} = (v0/v1) Q + (1 - v0/v1)(u + kappa E),
kappa = v0/(v1 - v0), E = T^{v1} - Q with zero marginals; u + kappa E = (u + S)/2 with S = u + 2 kappa E >= 0 iff
E >= -(v1 - v0)/(2 d^2 v0) entrywise; then the 1/2-lemma.)  Only the LOWER deviation E >= -bound is actually needed,
i.e. Q - T <= bound; we check both sides as P2 states.
h_xy(m) = 1/(2 d^2 sin^2(pi (m - delta_xy)/d)), delta = (1/4, -1/4, 3/4, 1/4) for xy = 00, 01, 10, 11
(= own f_xy with g_xy = alpha_x + beta_y, alpha = (0,1/2), beta = (1/4,-1/4)).
Enclosures: mpmath.iv (60 digits) AND own Fractions/Taylor with pi to 50 decimals (both sides).
"""
import os
import json
import glob
from fractions import Fraction as Fr
import mpmath

HERE = os.path.dirname(os.path.abspath(__file__))
P2 = os.path.join(os.path.dirname(HERE), 'P2_literal_noise', 'certificates')
DELTA = {(0, 0): Fr(1, 4), (0, 1): Fr(-1, 4), (1, 0): Fr(3, 4), (1, 1): Fr(1, 4)}
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
PI_LO = Fr('3.14159265358979323846264338327950288419716939937510')
PI_HI = PI_LO + Fr(1, 10 ** 50)


def raw_to_frac(t):
    sign, man, exp, bc = t
    v = Fr(int(man)) * (Fr(2) ** exp if exp >= 0 else Fr(1, 2 ** (-exp)))
    return -v if sign else v


def h_iv(d):
    mpmath.iv.dps = 60
    out = {}
    for xy in LINKS:
        for m in range(d):
            r = (m - DELTA[xy]) / d
            s = mpmath.iv.sin(mpmath.iv.pi * mpmath.iv.mpf(r.numerator) / r.denominator)
            val = 1 / (2 * d * d * s * s)
            out[(xy, m)] = (raw_to_frac(val._mpi_[0]), raw_to_frac(val._mpi_[1]))
    return out


def sin_partial(x, upper):
    """alternating Taylor partial sum of sin, 0 < x <= 2: upper=True -> ends with + term (upper bound)"""
    s, term, j = Fr(0), x, 0
    while True:
        s += term if j % 2 == 0 else -term
        nxt = term * x * x / ((2 * j + 2) * (2 * j + 3))
        if nxt < Fr(1, 10 ** 48) and ((j % 2 == 0) == upper):
            return s
        term, j = nxt, j + 1


def h_frac(d):
    out = {}
    for xy in LINKS:
        for m in range(d):
            r = (m - DELTA[xy]) / d
            r = r - (r.numerator // r.denominator)
            if r > Fr(1, 2):
                r = 1 - r
            assert 0 < r < Fr(1, 2) and r * PI_HI < PI_LO / 2
            s_lo = sin_partial(r * PI_LO, upper=False)
            s_hi = min(sin_partial(r * PI_HI, upper=True), Fr(1))
            assert 0 < s_lo < s_hi
            out[(xy, m)] = (1 / (2 * d * d * s_hi * s_hi), 1 / (2 * d * d * s_lo * s_lo))
    return out


def check(path):
    c = json.load(open(path))
    d = c['d']
    v1 = Fr(*c['v1'])
    v0 = Fr(*c['v0'])
    den = c['den']
    assert 0 < v0 < v1 <= 1
    Q = {(xy, m): Fr(0) for xy in LINKS for m in range(d)}
    tot = 0
    for (m00, m01, m10), num in c['support']:
        assert num >= 0 and all(0 <= z < d for z in (m00, m01, m10))
        m11 = (m01 + m10 - m00) % d
        tot += num
        w = Fr(num, den)
        for xy, mm in zip(LINKS, (m00, m01, m10, m11)):
            Q[(xy, mm)] += w
    assert tot == den, (d, tot, den)          # probability distribution
    bound = (v1 - v0) / (2 * d * v0)
    res = {}
    for name, H in (('iv', h_iv(d)), ('frac', h_frac(d))):
        worst_low = None     # max over entries of Q - T_hi... we need Q - T <= bound and T - Q <= bound
        worst = Fr(0)
        for xy in LINKS:
            for m in range(d):
                T_lo = v1 * H[(xy, m)][0] + (1 - v1) / d
                T_hi = v1 * H[(xy, m)][1] + (1 - v1) / d
                dev = max(Q[(xy, m)] - T_lo, T_hi - Q[(xy, m)])     # >= |Q - T| for the true T
                worst = max(worst, dev)
                low = Q[(xy, m)] - T_lo                              # needed side: Q - T <= bound
                worst_low = low if worst_low is None else max(worst_low, low)
        res[name] = (worst <= bound, float(bound - worst), float(bound - worst_low))
    return d, v0, v1, len(c['support']), float(bound), res


def main():
    files = sorted(glob.glob(os.path.join(P2, 'dkz_d*.json')), key=lambda p: int(os.path.basename(p)[5:-5]))
    allok = True
    for p in files:
        d, v0, v1, ns, bound, res = check(p)
        ok = all(r[0] for r in res.values())
        allok &= ok
        print(f'd={d:2d}: v0 = {float(v0):.12f}, v1 = {float(v1):.12f}, support {ns:3d}, bound (v1-v0)/(2dv0) = '
              f'{bound:.3e}; two-sided margin iv {res["iv"][1]:.3e} frac {res["frac"][1]:.3e}; '
              f'one-sided margin {res["iv"][2]:.3e} -> {"VALID" if ok else "INVALID"}')
    print('ALL P2 CERTIFICATES VALID (own check)' if allok else 'SOME P2 CERTIFICATE INVALID')


if __name__ == '__main__':
    main()
