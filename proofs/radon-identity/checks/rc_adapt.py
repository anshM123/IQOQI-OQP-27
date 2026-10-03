"""Q_RI_check/rc_adapt.py -- (i) regeneration of the rc01 instances (verbatim generation code, same seed and call order);
(ii) adaptive recursive-bisection Gauss-Legendre for L(H + c0) (same piecewise set-up as rc_core.Inst.L)."""
import random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum


def rc01_instances():
    rng = random.Random(20261002)

    def block(PHP, BHB, X):
        r = BHB.shape[0]; q = PHP.shape[0]
        H = sp.zeros(r + q, r + q)
        H[:r, :r] = BHB; H[r:, r:] = PHP; H[r:, :r] = X; H[:r, r:] = X.H
        return H

    def randX(q, r, nr=9, den=4, scale=1):
        return sp.Matrix(q, r, lambda i, j: (sp.Rational(rng.randint(-nr, nr), den)
                                             + sp.I*sp.Rational(rng.randint(-nr, nr), den))*scale)

    insts = []
    for (M, r) in [(2, 1), (3, 1), (3, 2), (4, 2), (5, 2), (5, 3), (6, 3)]:
        insts.append(Inst.proj(herm(rng, M), r, 'rand_M%d_r%d' % (M, r)))
    insts.append(Inst.proj(herm(rng, 7), 1, 'rank1B_M7'))
    insts.append(Inst.proj(herm(rng, 7), 6, 'corank1_M7'))
    insts.append(Inst.proj(with_spectrum(rng, [2, 2, 2, -1, -1, 0]), 3, 'degenH_222m1m10_M6'))
    insts.append(Inst.proj(with_spectrum(rng, [3, 3, -3, -3]), 2, 'degenH_33m3m3_M4'))
    insts.append(Inst.proj(block(with_spectrum(rng, [1, 1, -2]), with_spectrum(rng, ['1/2', '1/2']), randX(3, 2)), 2,
                           'degen_blocks_PHP11m2_BHB.5.5'))
    H1 = herm(rng, 2)
    H11 = sp.diag(H1, H1)
    perm = [0, 2, 1, 3]
    H11 = sp.Matrix(4, 4, lambda i, j: H11[perm[i], perm[j]])
    insts.append(Inst.proj(H11, 2, 'H1+H1_all_roots_double'))
    insts.append(Inst.proj(block(herm(rng, 2), sp.zeros(2, 2), randX(2, 2)), 2, 'zero_BHB_M4'))
    insts.append(Inst.proj(block(sp.zeros(3, 3), sp.zeros(2, 2), randX(3, 2)), 2, 'zero_both_diag_blocks_M5'))
    v = sp.Matrix([1, sp.I, 2, -1, sp.Rational(1, 2)])
    w = sp.Matrix([0, 1, -sp.I, 1, 3])
    insts.append(Inst.proj((v*v.H - w*w.H).applyfunc(sp.expand), 2, 'rank2_singular_M5'))
    insts.append(Inst.proj(block(herm(rng, 2), herm(rng, 2), randX(2, 2, scale=sp.Rational(1, 10**6))), 2,
                           'near_commuting_1e-6_M4'))
    insts.append(Inst.proj(block(herm(rng, 3), herm(rng, 2), randX(3, 2, scale=sp.Rational(1, 10**9))), 2,
                           'near_commuting_1e-9_M5'))
    Hw = herm(rng, 5, diag=[1000, sp.Rational(-1, 1000), 3, -250, sp.Rational(1, 10)])
    insts.append(Inst.proj(Hw, 2, 'wide_range_1e-3..1e3_M5'))
    insts.append(Inst.proj((herm(rng, 6)*10**4).applyfunc(sp.expand), 2, 'scale1e4_M6_r2'))
    insts.append(Inst.proj(herm(rng, 8), 4, 'rand_M8_r4'))
    return insts


_gl_cache = {}


def gl_nodes(n):
    key = (n, mp.mp.dps)
    if key not in _gl_cache:
        xs, ws = [], []
        for k in range(1, n + 1):
            x = mp.cos(mp.pi*(k - mp.mpf(1)/4)/(n + mp.mpf(1)/2))
            for _ in range(100):
                p0, p1 = mp.mpf(1), x
                for j in range(2, n + 1):
                    p0, p1 = p1, ((2*j - 1)*x*p1 - (j - 1)*p0)/j
                dp = n*(x*p1 - p0)/(x*x - 1)
                dx = p1/dp
                x -= dx
                if abs(dx) < mp.mpf(10)**(-mp.mp.dps - 5):
                    break
            p0, p1 = mp.mpf(1), x
            for j in range(2, n + 1):
                p0, p1 = p1, ((2*j - 1)*x*p1 - (j - 1)*p0)/j
            dp = n*(x*p1 - p0)/(x*x - 1)
            xs.append(x)
            ws.append(2/((1 - x*x)*dp*dp))
        _gl_cache[key] = (xs, ws)
    return _gl_cache[key]


def gl(f, a, b, n):
    xs, ws = gl_nodes(n)
    h = (b - a)/2
    m = (a + b)/2
    return h*mp.fsum(w*f(m + h*x) for x, w in zip(xs, ws))


def adaptive(f, a, b, tol, depth=0, stats=None):
    g1 = gl(f, a, b, 24)
    g2 = gl(f, a, b, 48)
    if abs(g1 - g2) <= tol*max(1, abs(g2)) or depth > 18:
        if stats is not None:
            stats[0] += 1
            stats[1] = max(stats[1], abs(g1 - g2))
        return g2
    m = (a + b)/2
    return adaptive(f, a, m, tol, depth + 1, stats) + adaptive(f, m, b, tol, depth + 1, stats)


def L_adaptive(I, c0=0, tol=mp.mpf(10)**(-36)):
    I.mpready()
    pts, aux = I.branch_points(c0)
    cuts = sorted(set([mp.mpf(x.p)/x.q for x in I.b] + list(pts) + list(aux)))
    tot = mp.mpf(0)
    stats = [0, mp.mpf(0)]
    for ta, tb in zip(cuts[:-1], cuts[1:]):
        k = I.npairs_at((ta + tb)/2, c0)
        if k == 0:
            continue
        f = lambda th: I.imsum_piece(ta, tb, th, c0, k)
        tot += adaptive(f, mp.mpf(0), mp.pi/2, tol, 0, stats)
    return tot/(2*mp.pi), stats
