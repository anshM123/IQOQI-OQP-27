"""rc01: Theorem RI, L(H) = R(H), at 40-digit working precision on exact Gaussian-rational instances, incl. tricky ones:
degenerate spectra (exactly repeated eigenvalues of H, of PHP, of BHB), H = H1 (+) H1 (every pencil root double for all
tau), rank-1 and corank-1 B, zero diagonal blocks, singular H, near-commuting (off-diagonal block 1e-6 and 1e-9), wide
dynamic range, large scale, M = 8.  Also the shifted form L(H + c0) = R(H + c0) across kinks.
Branch points: exact discriminant (rc_core).  Error estimate: |Gauss-Legendre - tanh-sinh| on every piece."""
import sys, time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, cayley, logline, fmt

mp.mp.dps = 40
out = open('rc01_RI.log', 'w')
rng = random.Random(20261002)


def block(PHP, BHB, X):
    """H = [[BHB, X^*],[X, PHP]] in the basis ran B (first r) + ran P (last M - r)."""
    r = BHB.shape[0]
    q = PHP.shape[0]
    H = sp.zeros(r + q, r + q)
    H[:r, :r] = BHB
    H[r:, r:] = PHP
    H[r:, :r] = X
    H[:r, r:] = X.H
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
H11 = sp.diag(H1, H1)        # basis order: (B,P) of block 1, (B,P) of block 2 -> permute so that B comes first
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

logline(out, 'rc01 RI: L(H) vs R(H) at dps %d  (L by exact-branch-point piecewise quadrature, err = |GL - TS|)' % mp.mp.dps)
worst = mp.mpf(0)
worst_rel = mp.mpf(0)
for I in insts:
    t0 = time.time()
    Lv, err, nb, pcs = I.L(0)
    Rv = I.R(0)
    d = abs(Lv - Rv)
    worst = max(worst, d)
    rel = d/max(abs(Rv), mp.mpf(10)**(-60))
    worst_rel = max(worst_rel, rel)
    logline(out, '  %-30s M=%d r=%d #bp=%2d pairs/piece=%s  L=%s  R=%s  |L-R|=%s rel=%s quad-err=%s  (%.0fs)' % (
        I.name, I.M, I.m[0], nb, pcs, fmt(Lv, 25), fmt(Rv, 25), mp.nstr(d, 3), mp.nstr(rel, 3), mp.nstr(err, 3),
        time.time() - t0))
logline(out, 'max |L - R| = %s ; max relative = %s' % (mp.nstr(worst, 3), mp.nstr(worst_rel, 3)))

# shifted form across kinks: c0 rational, chosen between/at eigenvalues of H and H_d
logline(out, '\nshifted form L(H + c0) = R(H + c0)')
worst2 = mp.mpf(0)
for I in [insts[3], insts[9], insts[11], insts[15]]:
    I.mpready()
    ks = sorted(set([float(-x) for x in I.lam] + [float(-x) for x in I.lam0]))
    c0s = []
    for a, b in zip(ks[:-1], ks[1:]):
        c0s.append(sp.Rational((a + b)/2).limit_denominator(64))
    c0s = [sp.Rational(ks[0] - 1).limit_denominator(8)] + c0s[:6] + [sp.Rational(ks[-1] + 1).limit_denominator(8)]
    for c0 in c0s:
        t0 = time.time()
        Lv, err, nb, pcs = I.L(c0)
        Rv = I.R(mp.mpf(c0.p)/c0.q)
        d = abs(Lv - Rv)
        worst2 = max(worst2, d)
        logline(out, '  %-30s c0=%-8s L=%s R=%s |L-R|=%s quad-err=%s (%.0fs)' % (
            I.name, str(c0), fmt(Lv, 22), fmt(Rv, 22), mp.nstr(d, 3), mp.nstr(err, 3), time.time() - t0))
logline(out, 'max |L - R| (shifted) = %s' % mp.nstr(worst2, 3))
out.close()
