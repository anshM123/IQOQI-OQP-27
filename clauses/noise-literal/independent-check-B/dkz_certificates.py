"""
Step 4: rigorous lower bounds on v_c(DKZ_d) (literal uniform noise) from exact certificates.

Cyclic reduction.  DKZ_d is a 'cyclic' behaviour: p(a,b|x,y) = f_xy(b - a mod d)/d with
     f_xy(n) = 1 / (2 d^2 sin^2(pi (n - g_xy)/d)),   g_xy = alpha_x + beta_y,  alpha = (0,1/2), beta = (1/4,-1/4),
so v DKZ + (1-v) u is cyclic with difference distributions T_xy = v f_xy + (1-v)/d.
SUFFICIENT CONDITION FOR LOCALITY (proof in REPORT.md):  if W is a probability distribution on
     C_d = {k = (k00,k01,k10,k11) in Z_d^4 : k00 + k11 = k01 + k10 mod d}
with coordinate marginals T_xy, then the cyclic behaviour is local (alpha_0 = g uniform, beta_y = g + k_0y,
alpha_1 = g + k_00 - k_10).
CERTIFICATE (error absorption through the cyclic 1/2-lemma):  rational weights W >= 0 on C_d with t = sum W < 1 and
     T_xy(n) - (A W)_xy(n) >= (1 - t)/(2d)   for all x, y, n,          (A W)_xy(n) = sum_k W(k) [k_xy = n].
Then R = T - A W has, for each xy, total mass exactly 1 - t (sum_n f_xy(n) = 1) and entries >= (1-t)/(2d), so
r = R/(1-t) = (g + unif)/2 with g = 2r - unif a 4-tuple of distributions; by the cyclic 1/2-lemma r has a local model,
and T = t (AW/t) + (1-t) r does too.  Only LOWER bounds of f_xy(n) are needed: rigorous rational enclosures from
Machin's formula for pi and alternating Taylor series for sin (pure Fractions, no floating point in the check).

Usage:  python dkz_certificates.py [dmin dmax]      writes certificates/dkz_d{d}.json and prints the verification.
"""
import sys
import os
import json
import itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix, hstack

HERE = os.path.dirname(os.path.abspath(__file__))
CERT_DIR = os.path.join(HERE, 'certificates')

ALPHA = (Fr(0), Fr(1, 2))
BETA = (Fr(1, 4), Fr(-1, 4))
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]


# ------------------------------------------------------------------ rigorous enclosures (Fractions only)
def arctan_bounds(x, nterms=60):
    """0 < x < 1 rational: (lo, hi) with lo <= arctan(x) <= hi (alternating series, decreasing terms)."""
    s = Fr(0)
    partial = []
    for k in range(nterms):
        s += (-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
        partial.append(s)
    # partial sum ending with a positive term (k even) is an upper bound, negative term (k odd) a lower bound
    hi = partial[-2] if (nterms - 1) % 2 == 1 else partial[-1]
    lo = partial[-1] if (nterms - 1) % 2 == 1 else partial[-2]
    assert lo < hi
    return lo, hi


def round_down(q, den=10 ** 45):
    return Fr((q.numerator * den) // q.denominator, den)


def round_up(q, den=10 ** 45):
    return Fr(-((-q.numerator * den) // q.denominator), den)


def pi_bounds():
    """Machin: pi = 16 arctan(1/5) - 4 arctan(1/239); outward-rounded to 45 decimals."""
    a_lo, a_hi = arctan_bounds(Fr(1, 5))
    b_lo, b_hi = arctan_bounds(Fr(1, 239))
    lo = round_down(16 * a_lo - 4 * b_hi)
    hi = round_up(16 * a_hi - 4 * b_lo)
    assert Fr(314159265358979, 10 ** 14) < lo < hi < Fr(314159265358980, 10 ** 14)
    assert hi - lo < Fr(1, 10 ** 44)
    return lo, hi


PI_LO, PI_HI = pi_bounds()


def sin_bounds(x, nterms=30):
    """0 < x <= 2 rational: (lo, hi) with lo <= sin(x) <= hi (alternating Taylor series whose terms
    x^(2j+1)/(2j+1)! decrease because x^2 <= 4 < (2j+2)(2j+3)); outward-rounded to 45 decimals."""
    assert 0 < x <= 2
    s = Fr(0)
    term = x
    partial = []
    for j in range(nterms):
        s += term if j % 2 == 0 else -term
        partial.append(s)
        term = term * x * x / ((2 * j + 2) * (2 * j + 3))
    hi = partial[-1] if (nterms - 1) % 2 == 0 else partial[-2]
    lo = partial[-2] if (nterms - 1) % 2 == 0 else partial[-1]
    assert lo < hi and hi - lo < Fr(1, 10 ** 40)
    return round_down(lo), round_up(hi)


def sin2_pi_r_bounds(r):
    """rational r, not in Z/2: rigorous (lo, hi) for sin^2(pi r)."""
    r = r - (r.numerator // r.denominator)          # r mod 1 in [0,1)
    if r > Fr(1, 2):
        r = 1 - r                                    # sin^2(pi r) = sin^2(pi (1-r))
    assert 0 < r < Fr(1, 2)
    x_lo, x_hi = r * PI_LO, r * PI_HI
    assert x_hi < PI_LO / 2                          # stays inside [0, pi/2], where sin is increasing
    lo = sin_bounds(x_lo)[0]
    hi = sin_bounds(x_hi)[1]
    assert 0 < lo <= hi <= 1
    return lo * lo, hi * hi


def f_bounds(d):
    """dict (x, y, n) -> (lo, hi) rigorous bounds of f_xy(n) = 1/(2 d^2 sin^2(pi (n - g_xy)/d))."""
    out = {}
    for x, y in LINKS:
        g = ALPHA[x] + BETA[y]
        for n in range(d):
            s2lo, s2hi = sin2_pi_r_bounds((n - g) / d)
            out[(x, y, n)] = (1 / (2 * d * d * s2hi), 1 / (2 * d * d * s2lo))
    return out


def f_float(d):
    import mpmath as mp
    mp.mp.dps = 30
    out = {}
    for x, y in LINKS:
        g = ALPHA[x] + BETA[y]
        for n in range(d):
            out[(x, y, n)] = float(1 / (2 * d * d * mp.sin(mp.pi * (n - mp.mpf(g.numerator) / g.denominator) / d) ** 2))
    return out


# ------------------------------------------------------------------ cyclic local polytope
def cyclic_set(d):
    """C_d as list of (k00, k01, k10, k11)"""
    return [(k00, k01, k10, (k01 + k10 - k00) % d) for k00, k01, k10 in itertools.product(range(d), repeat=3)]


def marginal_matrix(d, C):
    """A: rows (link index, n) -> 4d rows; columns k in C."""
    A = lil_matrix((4 * d, len(C)))
    for j, k in enumerate(C):
        for li in range(4):
            A[li * d + k[li], j] = 1.0
    return csr_matrix(A)


def target_float(d, v, ff):
    return np.array([v * ff[(x, y, n)] + (1 - v) / d for (x, y) in LINKS for n in range(d)])


def lp_vc_cyclic(d):
    """float LP: max v s.t. A W = v f + (1-v)/d, sum W = 1, W >= 0"""
    C = cyclic_set(d)
    A = marginal_matrix(d, C)
    ff = f_float(d)
    fv = np.array([ff[(x, y, n)] for (x, y) in LINKS for n in range(d)])
    Aeq = hstack([A, csr_matrix((-(fv - 1.0 / d)).reshape(-1, 1))]).tocsr()
    beq = np.full(4 * d, 1.0 / d)
    c = np.zeros(len(C) + 1)
    c[-1] = -1
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * len(C) + [(0, 1)], method='highs')
    assert res.status == 0
    return res.x[-1]


def lp_certificate(d, v):
    """float LP: max M s.t. T - A W - (1 - sum W)/(2d) >= M, W >= 0."""
    C = cyclic_set(d)
    A = marginal_matrix(d, C)
    ff = f_float(d)
    T = target_float(d, v, ff)
    # A W - (sum W)/(2d) + M <= T - 1/(2d)
    Aub = hstack([A - csr_matrix(np.full((4 * d, len(C)), 1.0 / (2 * d))), csr_matrix(np.ones((4 * d, 1)))]).tocsr()
    bub = T - 1.0 / (2 * d)
    c = np.zeros(len(C) + 1)
    c[-1] = -1
    res = linprog(c, A_ub=Aub, b_ub=bub, bounds=[(0, None)] * len(C) + [(None, None)], method='highs',
                  options={'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10})
    assert res.status == 0, res.message
    return C, res.x[:-1], res.x[-1]


# ------------------------------------------------------------------ exact verification
def verify(d, v, W):
    """W: dict k -> Fraction (k in C_d).  Returns (ok, min_slack (Fraction), t)."""
    v = Fr(v)
    assert 0 < v < 1
    Cset = set(cyclic_set(d))
    t = Fr(0)
    AW = {(li, n): Fr(0) for li in range(4) for n in range(d)}
    for k, w in W.items():
        assert k in Cset, k
        assert w >= 0
        t += w
        for li in range(4):
            AW[(li, k[li])] += w
    assert t < 1
    fb = f_bounds(d)
    rhs = (1 - t) / (2 * d)
    min_slack = None
    for li, (x, y) in enumerate(LINKS):
        for n in range(d):
            T_lo = v * fb[(x, y, n)][0] + (1 - v) / d
            slack = T_lo - AW[(li, n)] - rhs
            if min_slack is None or slack < min_slack:
                min_slack = slack
    return min_slack >= 0, min_slack, t


def rationalize(C, Wf, den=10 ** 15):
    W = {}
    for k, w in zip(C, Wf):
        q = Fr(int(round(max(w, 0.0) * den)), den)
        if q > 0:
            W[k] = q
    return W


def v_thr_float(d):
    c = 2 ** 0.5 - 1
    return 4 * (d - 1) / (4 * (d - 1) + c * d * d) if d % 2 == 0 else 4 / (4 + c * d)


def I_ME(d):
    import math
    return 4 / (d * (d - 1)) * sum((d - j) / math.cos(math.pi * j / (2 * d)) for j in range(1, d))


def make_certificate(d, v):
    C, Wf, M = lp_certificate(d, float(v))
    W = rationalize(C, Wf)
    ok, slack, t = verify(d, v, W)
    return W, ok, slack, t, M


def main(dmin, dmax):
    os.makedirs(CERT_DIR, exist_ok=True)
    print(f'pi in [{float(PI_LO)!r}, {float(PI_HI)!r}], width {float(PI_HI - PI_LO):.1e}')
    for d in range(dmin, dmax + 1):
        vcf = lp_vc_cyclic(d)
        bound = 2 / I_ME(d)
        print(f'd={d}: float LP v_c(DKZ_d) (cyclic) = {vcf:.12f};  2/I_ME(d) = {bound:.12f};  '
              f'competitor threshold = {v_thr_float(d):.12f}')
        results = {}
        # main certificate: v = 2/I_ME(d) rounded down to 4 decimals, minus 1e-4; tight: within 2e-6
        for label, v in [('main', Fr(int(bound * 10 ** 4) - 1, 10 ** 4)),
                         ('tight', Fr(int(bound * 10 ** 6) - 1, 10 ** 6))]:
            W, ok, slack, t, M = make_certificate(d, v)
            print(f'   [{label}] v = {v} = {float(v):.8f}: LP margin {M:.3e}; exact check: '
                  f'{"PASS" if ok else "FAIL"} (min slack {float(slack):.3e}, t = {float(t):.6f}, '
                  f'{len(W)} nonzero weights)')
            if ok:
                results[label] = {'v': str(v), 't': str(t), 'min_slack': str(slack),
                                  'W': [[list(k), str(w)] for k, w in sorted(W.items())]}
        with open(os.path.join(CERT_DIR, f'dkz_d{d}.json'), 'w') as fh:
            json.dump({'d': d, 'convention': 'f_xy(n) = 1/(2 d^2 sin^2(pi (n - alpha_x - beta_y)/d)), '
                                             'alpha=(0,1/2), beta=(1/4,-1/4); k = (k00,k01,k10,k11), '
                                             'k00+k11 = k01+k10 mod d',
                       'certificates': results}, fh)


if __name__ == '__main__':
    if len(sys.argv) >= 3:
        main(int(sys.argv[1]), int(sys.argv[2]))
    else:
        main(3, 9)
