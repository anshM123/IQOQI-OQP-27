"""rc07: re-run of the rc01/rc05 cases whose quadrature had not converged (|GL - TS| ~ |L - R|), with an ADAPTIVE
recursive-bisection Gauss-Legendre in theta on every piece (accept a panel when the 24- and 48-point rules agree to 1e-36
relative), and R recomputed at dps 90 for the near-commuting cases (where R ~ 1e-12, 1e-18 is a difference of O(1) sums).
The instances are regenerated with the same seeds/call order as in rc01 and rc05."""
import time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline

mp.mp.dps = 44
out = open('rc07_rerun.log', 'w')


# ---------------- regenerate rc01 instances (verbatim generation code, same seed and order)
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
byname = {I.name: I for I in insts}


def gl_panel(f, a, b, n):
    xs, ws = mp.gauss_legendre_nodes(n) if hasattr(mp, 'gauss_legendre_nodes') else (None, None)
    return None


_gl_cache = {}


def gl_nodes(n):
    if (n, mp.mp.dps) not in _gl_cache:
        xs = []
        ws = []
        # nodes/weights from mpmath's legendre roots
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
        _gl_cache[(n, mp.mp.dps)] = (xs, ws)
    return _gl_cache[(n, mp.mp.dps)]


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


logline(out, 'rc07: adaptive re-run (dps %d; panels accepted when |G24 - G48| <= 1e-36 rel)' % mp.mp.dps)
for name in ['rand_M3_r1', 'corank1_M7', 'wide_range_1e-3..1e3_M5', 'near_commuting_1e-6_M4', 'near_commuting_1e-9_M5']:
    I = byname[name]
    t0 = time.time()
    Lv, stats = L_adaptive(I, 0)
    with mp.workdps(90):
        I._mp_dps = None
        I.mpready()
        Rv = I.R(0)
    I._mp_dps = None
    d = abs(Lv - Rv)
    logline(out, '  %-28s L=%s R(dps90)=%s |L-R|=%s rel=%s  panels=%d max panel err=%s (%.0fs)' % (
        name, mp.nstr(Lv, 30), mp.nstr(Rv, 30), mp.nstr(d, 3), mp.nstr(d/abs(Rv), 3), stats[0], mp.nstr(stats[1], 2),
        time.time() - t0))

# ---------------- rc05 general-B cases with |GL - TS| ~ |L - R|
rng = random.Random(31337)
c1 = Inst(herm(rng, 3), [0, sp.Rational(3, 8), 1], [1, 1, 1], 'b=(0,3/8,1)')
c2 = Inst(herm(rng, 4), [-1, sp.Rational(1, 5), sp.Rational(1, 2), 2], [1, 1, 1, 1], 'b=(-1,1/5,1/2,2)')
c3 = Inst(herm(rng, 4), [0, sp.Rational(3, 5), 1], [1, 2, 1], 'b=(0,3/5^2,1)')
c4 = Inst(herm(rng, 5), [0, sp.Rational(3, 10), sp.Rational(31, 100), 1], [1, 2, 1, 1], 'b=(0,.3^2,.31,1)')
c5 = Inst(herm(rng, 6), [sp.Rational(-1, 2), sp.Rational(1, 10), sp.Rational(9, 10), 2], [1, 2, 1, 2], 'b=(-.5,.1^2,.9,2^2)')
for I, c0 in [(c4, 0), (c5, 0), (c5, sp.Rational(1, 3))]:
    t0 = time.time()
    Lv, stats = L_adaptive(I, c0)
    Rv = I.R(mp.mpf(sp.Rational(c0).p)/sp.Rational(c0).q)
    d = abs(Lv - Rv)
    logline(out, '  %-28s c0=%-4s L_B=%s R=%s |L-R|=%s panels=%d max panel err=%s (%.0fs)' % (
        I.name, str(c0), mp.nstr(Lv, 30), mp.nstr(Rv, 30), mp.nstr(d, 3), stats[0], mp.nstr(stats[1], 2), time.time() - t0))
out.close()
