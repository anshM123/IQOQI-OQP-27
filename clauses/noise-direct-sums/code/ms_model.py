"""ms_model.py -- end-to-end check of the MULTI-BLOCK local model for S = DKZ_{d_1} (+) ... (+) DKZ_{d_r} at
v = d / sum_i d_i kappa_i  (d_i >= 2).

Model (generalising ds_model.py):
  F_i  (weight q_i = v d_i/d (2 - kappa_i) + 2(1-v) d_i^2/d^2): all four outcomes in block i, adapted variables drawn
       from a decomposition of phi_i on compositions of d_i - 1 (float LP), a0 uniform in block i;
  T_ij (weight t_ij, i != j): three variables in block i with the two within-block adapted variables = 0,
       the odd variable (A0, A1, B0 or B1, each t_ij/4) uniform in block j;
       explicit fractional orientation  t_ij = 2(1-v)(d_i d_j/d^2)(1 + (kappa_i - kappa_j)/mubar),
       mubar = sum_k (d_k/d)(kappa_k - 1).
Checks: t_ij >= 0, Z_i = (1/2) sum_j t_ij equals (v d_i/d)(kappa_i - 1) - (1-v) d_i^2/d^2, total weight 1,
model == v P + (1-v) u (max abs error), and (small d) the LP critical visibility v_c (core.vc) == v.
"""
import sys, os, itertools
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import dkz_bases, behaviour, vc, ime      # noqa: E402  (read-only import)


def G(n):
    k = np.arange(n); return 1.0 / (2 * n * n * np.sin(np.pi * (4 * k + 1) / (4 * n)) ** 2)


def comp_law(phi):
    S = len(phi) - 1
    comps = [c for c in itertools.product(range(S + 1), repeat=4) if sum(c) == S]
    A = np.zeros((4 * (S + 1), len(comps)))
    for j, c in enumerate(comps):
        for i in range(4):
            A[i * (S + 1) + c[i], j] = 1.0
    res = linprog(np.zeros(len(comps)), A_eq=A, b_eq=np.concatenate([phi] * 4), bounds=[(0, None)] * len(comps),
                  method='highs')
    assert res.status == 0
    return comps, res.x


def add(Pm, lam, w):
    a0, a1, b0, b1 = lam
    Pm[0, 0, a0, b0] += w; Pm[0, 1, a0, b1] += w; Pm[1, 0, a1, b0] += w; Pm[1, 1, a1, b1] += w


def model(ds):
    r = len(ds); d = sum(ds)
    kap = [ime(n) / 2 for n in ds]
    v = d / sum(n * kp for n, kp in zip(ds, kap))
    mubar = sum(n / d * (kp - 1) for n, kp in zip(ds, kap))
    offs = np.cumsum([0] + list(ds))[:-1]
    t = np.zeros((r, r))
    for i in range(r):
        for j in range(r):
            if i != j:
                t[i, j] = 2 * (1 - v) * ds[i] * ds[j] / d ** 2 * (1 + (kap[i] - kap[j]) / mubar)
    Z = [(v * ds[i] / d) * (kap[i] - 1) - (1 - v) * ds[i] ** 2 / d ** 2 for i in range(r)]
    Zerr = max(abs(0.5 * t[i].sum() - Z[i]) for i in range(r))
    Pm = np.zeros((2, 2, d, d)); total = 0.0
    for i in range(r):
        n, off = ds[i], offs[i]
        q = v * n / d * G(n) + (1 - v) * n / d ** 2; q[0] -= Z[i]
        qi = q.sum(); phi = q / qi
        comps, w = comp_law(phi)
        for c, wt in zip(comps, w):
            if wt <= 0: continue
            n1, n2, n3, n4 = c
            for a0 in range(n):
                b0 = (a0 - n1) % n; b1 = (a0 + n2) % n; a1 = (b0 - 1 - n3) % n
                add(Pm, (off + a0, off + a1, off + b0, off + b1), qi * wt / n)
        total += qi
        for j in range(r):
            if j == i: continue
            tau = t[i, j]; ooff, on = offs[j], ds[j]
            for odd in range(4):
                for p in range(n):
                    if odd == 3:   a0, b0, a1 = p, p, (p - 1) % n
                    elif odd == 2: a0 = p; b1 = p; a1 = p
                    elif odd == 1: a0 = p; b0 = p; b1 = p
                    else:          b0 = p; a1 = (p - 1) % n; b1 = a1
                    for o in range(on):
                        if odd == 3: lam = (off + a0, off + a1, off + b0, ooff + o)
                        elif odd == 2: lam = (off + a0, off + a1, ooff + o, off + b1)
                        elif odd == 1: lam = (off + a0, ooff + o, off + b0, off + b1)
                        else: lam = (ooff + o, off + a1, off + b0, off + b1)
                        add(Pm, lam, tau / 4 / n / on)
            total += tau
    A = np.zeros((2, d, d), complex); F = np.zeros((2, d, d), complex)
    for i in range(r):
        Ai, Fi = dkz_bases(ds[i]); o = offs[i]; n = ds[i]
        for x in range(2):
            A[x, o:o + n, o:o + n] = Ai[x]; F[x, o:o + n, o:o + n] = Fi[x]
    P = behaviour(A, F)
    Pv = v * P + (1 - v) / d ** 2
    return dict(v=v, tmin=t[~np.eye(r, dtype=bool)].min(), Zerr=Zerr, total=total, err=np.abs(Pm - Pv).max(), P=P)


if __name__ == '__main__':
    comps = [(2, 2), (3, 2), (2, 2, 2), (3, 2, 2), (3, 3, 2), (4, 2, 2), (2, 2, 2, 2), (4, 3, 2), (5, 2, 2), (3, 3, 3),
             (5, 3, 2), (4, 4, 2), (3, 2, 2, 2), (6, 3, 2), (2, 2, 2, 2, 2), (7, 4, 3, 2)]
    for ds in comps:
        o = model(ds)
        d = sum(ds)
        line = (f"blocks {ds} d={d}: v_ds = {o['v']:.10f}  min t_ij = {o['tmin']:.3e}  |Z err| = {o['Zerr']:.1e}  "
                f"total weight = {o['total']:.12f}  max|model - P_v| = {o['err']:.2e}")
        if d <= 9:
            line += f"  LP v_c = {vc(o['P']):.10f}"
        print(line, flush=True)
