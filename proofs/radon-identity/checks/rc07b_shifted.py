"""rc07b: adaptive re-run of every shifted-form point L(H + c0) = R(H + c0) of rc01 whose fixed-degree quadrature had not
converged (|GL - TS| > 1e-30 in rc01_RI.log).  Same instances (rc_adapt.rc01_instances), same c0."""
import re, time
import sympy as sp
import mpmath as mp
from rc_adapt import rc01_instances, L_adaptive
from rc_core import logline

mp.mp.dps = 44
out = open('rc07b_shifted.log', 'w')
byname = {I.name: I for I in rc01_instances()}
todo = []
shifted = False
for line in open('rc01_RI.log'):
    if line.startswith('shifted form'):
        shifted = True
        continue
    if not shifted:
        continue
    m = re.match(r'\s+(\S+)\s+c0=(\S+)\s+L=.*quad-err=(\S+)', line)
    if m and float(m.group(3)) > 1e-30:
        todo.append((m.group(1), sp.Rational(m.group(2)), float(m.group(3))))
logline(out, 'rc07b: %d shifted-form points of rc01 with |GL - TS| > 1e-30, recomputed adaptively (dps %d)' % (len(todo), mp.mp.dps))
for name, c0, qe in todo:
    I = byname[name]
    t0 = time.time()
    Lv, stats = L_adaptive(I, c0)
    Rv = I.R(mp.mpf(c0.p)/c0.q)
    logline(out, '  %-28s c0=%-8s (rc01 quad-err %.1e)  L=%s R=%s |L-R|=%s panels=%d max panel err=%s (%.0fs)' % (
        name, str(c0), qe, mp.nstr(Lv, 28), mp.nstr(Rv, 28), mp.nstr(abs(Lv - Rv), 3), stats[0], mp.nstr(stats[1], 2),
        time.time() - t0))
out.close()
