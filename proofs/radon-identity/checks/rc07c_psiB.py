"""rc07c: adaptive re-run of the Psi_B(c) = E(c) checks of rc05 section (2) whose fixed-degree quadrature had not converged
(|GL - TS| > 1e-30), same instances (regenerated with the rc05 seed and order) and same c.  On every gap (b_l, b_{l+1}):
tau = b_l + (b_{l+1} - b_l) sin^2(theta), recursive-bisection Gauss-Legendre (24/48 points, 1e-36 relative)."""
import re, time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline
from rc_adapt import adaptive

mp.mp.dps = 44
out = open('rc07c_psiB.log', 'w')
rng = random.Random(31337)


def blockdiag_with(H, blocks, specs):
    H = sp.Matrix(H)
    for blk, sp_ in zip(blocks, specs):
        if sp_ is None:
            continue
        Hb = with_spectrum(rng, sp_)
        for a, i in enumerate(blk):
            for b, j in enumerate(blk):
                H[i, j] = Hb[a, b]
    return H


cases = []
cases.append(Inst(herm(rng, 3), [0, sp.Rational(3, 8), 1], [1, 1, 1], 'b=(0,3/8,1)'))
cases.append(Inst(herm(rng, 4), [-1, sp.Rational(1, 5), sp.Rational(1, 2), 2], [1, 1, 1, 1], 'b=(-1,1/5,1/2,2)'))
cases.append(Inst(herm(rng, 4), [0, sp.Rational(3, 5), 1], [1, 2, 1], 'b=(0,3/5^2,1)'))
cases.append(Inst(herm(rng, 5), [0, sp.Rational(3, 10), sp.Rational(31, 100), 1], [1, 2, 1, 1], 'b=(0,.3^2,.31,1)'))
cases.append(Inst(herm(rng, 6), [sp.Rational(-1, 2), sp.Rational(1, 10), sp.Rational(9, 10), 2], [1, 2, 1, 2],
                  'b=(-.5,.1^2,.9,2^2)'))
I0 = Inst(herm(rng, 5), [0, sp.Rational(1, 2), 1], [1, 3, 1], 'tmp')
Hdeg = blockdiag_with(I0.Hs, I0.blocks, [None, [1, 1, -1], None])
cases.append(Inst(Hdeg, [0, sp.Rational(1, 2), 1], [1, 3, 1], 'b=(0,1/2^3,1) Pi2HPi2 spec(1,1,-1)'))
Hp = herm(rng, 4)
for i in [0, 1, 2]:
    Hp[i, 3] = 0
    Hp[3, i] = 0
cases.append(Inst(Hp, [0, sp.Rational(2, 5), 1], [1, 2, 1], 'b=(0,2/5^2,1) block3 decoupled'))
byname = {I.name: I for I in cases}

todo = []
sec2 = False
for line in open('rc05_generalB.log'):
    if line.startswith('(2)'):
        sec2 = True
        continue
    if line.startswith('(3)'):
        break
    if not sec2:
        continue
    m = re.match(r'\s+(.+?)\s+c=\((\S+) \+ (\S+)j\)\s+Psi_B=.*quad-err=(\S+)', line)
    if m and float(m.group(4)) > 1e-30:
        todo.append((m.group(1).strip(), mp.mpc(m.group(2), m.group(3)), float(m.group(4))))
logline(out, 'rc07c: %d Psi_B checks of rc05 with |GL - TS| > 1e-30, recomputed adaptively (dps %d)' % (len(todo), mp.mp.dps))
for name, c, qe in todo:
    I = byname[name]
    I.mpready()
    t0 = time.time()
    tot = mp.mpc(0)
    stats = [0, mp.mpf(0)]
    for ta, tb in zip(I.bmp[:-1], I.bmp[1:]):
        def f(th, ta=ta, tb=tb):
            dv, tau = I.dvec_piece(ta, tb, th)
            return (I.S_plus(dv, c) - I.S0_plus(dv, c))*(tb - ta)*mp.sin(2*th)
        tot += adaptive(f, mp.mpf(0), mp.pi/2, mp.mpf(10)**(-36), 0, stats)
    d = abs(tot - I.E(c))
    logline(out, '  %-36s c=%-12s (rc05 quad-err %.1e)  Psi_B=%s |Psi_B - E|=%s panels=%d (%.0fs)' % (
        name, mp.nstr(c, 3), qe, mp.nstr(tot, 25), mp.nstr(d, 3), stats[0], time.time() - t0))
out.close()
