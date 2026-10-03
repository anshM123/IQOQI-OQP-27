"""rc07e: adaptive re-run of the remaining RI-B points of rc05 section (1) with |GL - TS| > 1e-30 not covered by rc07:
b=(-1,1/5,1/2,2) c0=1/3 and b=(0,1/2^3,1) c0=1/3.  Instances regenerated with the rc05 seed and call order."""
import time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline
from rc_adapt import L_adaptive

mp.mp.dps = 44
out = open('rc07e_RIB.log', 'w')
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
cases.append(Inst(herm(rng, 6), [sp.Rational(-1, 2), sp.Rational(1, 10), sp.Rational(9, 10), 2], [1, 2, 1, 2], 'b=(-.5,.1^2,.9,2^2)'))
I0 = Inst(herm(rng, 5), [0, sp.Rational(1, 2), 1], [1, 3, 1], 'tmp')
Hdeg = blockdiag_with(I0.Hs, I0.blocks, [None, [1, 1, -1], None])
cases.append(Inst(Hdeg, [0, sp.Rational(1, 2), 1], [1, 3, 1], 'b=(0,1/2^3,1) Pi2HPi2 spec(1,1,-1)'))
logline(out, 'rc07e: adaptive re-run of the RI-B points of rc05 with |GL - TS| > 1e-30 not covered by rc07 (dps %d)' % mp.mp.dps)
for I in [cases[1], cases[5]]:
    c0 = sp.Rational(1, 3)
    t0 = time.time()
    Lv, stats = L_adaptive(I, c0)
    Rv = I.R(mp.mpf(1)/3)
    logline(out, '  %-36s c0=1/3  L_B=%s R=%s |L_B-R|=%s panels=%d max panel err=%s (%.0fs)' % (
        I.name, mp.nstr(Lv, 28), mp.nstr(Rv, 28), mp.nstr(abs(Lv - Rv), 3), stats[0], mp.nstr(stats[1], 2), time.time() - t0))
out.close()
