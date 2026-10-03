"""white_qubit_scan.py -- exploration for ledger B1 (float, not a proof).

White state noise rho_v = v Phi_D + (1 - v) 1/D^2, PVMs with rank pattern r: the noise term is the product of the
marginals n_r = p_A (x) p_B with p_A(a|x) = rank/D, a constant of the pattern.  The CGLMP-witnessed threshold is
2/I_ME(d) for all strategies iff  F(r) = v* I_max(r) + (1 - v*) I(n_r) <= 2  for all patterns r (v* = 2/I_ME).

Here: D = 2 (qubit pair).  Each measurement either is deterministic (one outcome of rank 2) or uses an ordered pair of
outcomes (s, s') with rank-one projectors; correlators E_xy = cos(theta_x - phi_y) (planar Bloch vectors suffice for
two settings per party).  I_max(r) = max over angles of the CGLMP value.
"""
import itertools
import sys

import numpy as np

sys.path.insert(0, ".")
from facets223 import cglmp_beta  # noqa: E402


def beta_np(d):
    b = cglmp_beta(d)
    return np.array([[[[float(b[x][y][a][c]) for c in range(d)] for a in range(d)] for y in range(2)]
                     for x in range(2)])


def i_me(d):
    j = np.arange(1, d)
    return 4.0 / (d * (d - 1)) * np.sum((d - j) / np.cos(np.pi * j / (2 * d)))


def scan(d, ngrid=73):
    beta = beta_np(d)
    vstar = 2 / i_me(d)
    # measurement choices: ('det', a) or ('pair', s, s2) with s != s2 (ordered: +1 -> s, -1 -> s2); unordered
    # suffices because the sign of the observable is absorbed by the angle.
    meas = [("det", a) for a in range(d)] + [("pair", s, t) for s in range(d) for t in range(s + 1, d)]
    th = np.linspace(0, 2 * np.pi, ngrid, endpoint=False)
    best = []
    for mA0, mA1, mB0, mB1 in itertools.product(meas, repeat=4):
        M = [mA0, mA1, mB0, mB1]
        # marginals
        marg = []
        for m in M:
            v = np.zeros(d)
            if m[0] == "det":
                v[m[1]] = 1
            else:
                v[m[1]] = v[m[2]] = 0.5
            marg.append(v)
        In = sum(np.sum(beta[x, y] * np.outer(marg[x], marg[2 + y])) for x in range(2) for y in range(2))
        if In <= 1e-12:
            continue
        # I(p) = sum_xy sum_ab beta p ; p(a,b) = pA pB + (1/4) e_a e_b E_xy where e = +1/-1 on the pair, 0 else
        e = []
        for m in M:
            v = np.zeros(d)
            if m[0] == "pair":
                v[m[1]], v[m[2]] = 1, -1
            e.append(v)
        c0 = In
        c = np.array([[0.25 * np.sum(beta[x, y] * np.outer(e[x], e[2 + y])) for y in range(2)] for x in range(2)])
        if np.abs(c).max() < 1e-12:
            continue
        # max over theta_x of sum_y c_xy cos(theta_x - phi_y) = |sum_y c_xy e^{-i phi_y}|; phi_0 = 0, scan phi_1
        ph = np.linspace(0, 2 * np.pi, 4001)
        val = np.abs(c[0, 0] + c[0, 1] * np.exp(-1j * ph)) + np.abs(c[1, 0] + c[1, 1] * np.exp(-1j * ph))
        k = int(np.argmax(val))
        from scipy.optimize import minimize_scalar
        g = lambda z: -(abs(c[0, 0] + c[0, 1] * np.exp(-1j * z)) + abs(c[1, 0] + c[1, 1] * np.exp(-1j * z)))
        r = minimize_scalar(g, bounds=(ph[k] - 0.002, ph[k] + 0.002), method='bounded')
        Imax = c0 + max(-r.fun, val.max())
        F = vstar * Imax + (1 - vstar) * In
        best.append((F, Imax, In, M))
    best.sort(key=lambda t: -t[0])
    print(f"d={d}: v* = {vstar:.10f}; {len(best)} qubit patterns with I(n) > 0; top 5 F = v* I_max + (1-v*) I(n):")
    for F, Imax, In, M in best[:5]:
        print(f"   F = {F:.10f}  I_max = {Imax:.8f}  I(n) = {In:.6f}  {M}", flush=True)
    return best[0][0] if best else None


if __name__ == "__main__":
    for d in range(3, 7):
        scan(d)
