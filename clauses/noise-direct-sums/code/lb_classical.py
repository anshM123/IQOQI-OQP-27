"""lb_classical.py -- Theorem LB for a general CLASSICAL block C (Alice measures the same basis U in both settings on C,
Bob the same basis V): S = DKZ_{k_1} (+) ... (+) DKZ_{k_r} (+) C.  On C x C the behaviour is J(a,b)/d with J doubly
stochastic and setting independent.  Changes w.r.t. lb_model.py (identity block, J = I):
  T_Li : odd variable uniform in DKZ block i; the other Alice variable a and Bob's common value b (odd in {A0, A1}),
         or Alice's common value a and the other Bob variable b (odd in {B0, B1}), drawn from J(a,b)/m;
  F_C  : setting-independent points (a, a, b, b) with weight rho(a,b) = (v/d - Z_L/m) J(a,b) + (1-v)/d^2.
Checks: assembled model = v P + (1-v) u (modes A and B as in lb_model.py), rho >= 0, and for small d the LP v_c
(core.vc, all d^4 deterministic points) equals v0 in mode-A cases.
usage: python lb_classical.py"""
import sys, os
import numpy as np
from scipy.linalg import block_diag
from scipy.stats import unitary_group
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import dkz_bases, behaviour, vc      # noqa: E402
from ds_template import ime, G                 # noqa: E402
from ds_model import comp_law, add             # noqa: E402
from lb_model import tpatterns                 # noqa: E402

kap = lambda n: ime(n) / 2


def strategy(blocks, m, rng):
    As, Fs = [], []
    for k in blocks:
        A, F = dkz_bases(k); As.append(A); Fs.append(F)
    U = unitary_group.rvs(m, random_state=rng) if m > 1 else np.eye(1)
    V = unitary_group.rvs(m, random_state=rng) if m > 1 else np.eye(1)
    A = np.array([block_diag(*([a[x] for a in As] + [U])) for x in range(2)])
    F = np.array([block_diag(*([f[y] for f in Fs] + [V])) for y in range(2)])
    return behaviour(A, F)


def model(blocks, m, P, mode):
    r = len(blocks); K = sum(blocks); d = K + m
    ks = np.array(blocks, float); kp = np.array([kap(k) for k in blocks]); S = float(ks @ kp)
    v0 = (2 * d - K) / (d * S / K + m)
    v = v0 if mode == 'A' else 1 / kap(d)
    J = d * P[0, 0, K:, K:]
    assert all(np.allclose(d * P[x, y, K:, K:], J, atol=1e-13) for x in range(2) for y in range(2))
    w = lambda a, b: 4 * (1 - v) * a * b / d ** 2
    Z = (v * ks / d) * (kp - 1) - (1 - v) * ks ** 2 / d ** 2
    t = np.zeros((r, r)); tL = np.zeros(r); tLi = np.zeros(r)
    for i in range(r):
        for j in range(r):
            if i != j:
                t[i, j] = w(ks[i], ks[j]) / 2 * ((1 + (kp[i] - kp[j]) * (K + 2 * m) / (S - K)) if mode == 'A' else 1)
        if mode == 'A':
            tL[i] = w(ks[i], m)
        else:
            tL[i] = 2 * Z[i] - 2 * (1 - v) * ks[i] * (K - ks[i]) / d ** 2; tLi[i] = w(ks[i], m) - tL[i]
    ZL = tLi.sum() / 2
    offs = np.concatenate([[0], np.cumsum(blocks)]).astype(int)
    Pm = np.zeros((2, 2, d, d)); total = 0.0
    for i, (off, n) in enumerate(zip(offs[:-1], blocks)):
        q = v * n / d * G(n) + (1 - v) * n / d ** 2; q[0] -= Z[i]
        qi = q.sum(); comps, wt = comp_law(q / qi)
        for c, x in zip(comps, wt):
            if x <= 0: continue
            n1, n2, n3, n4 = c
            for a0 in range(n):
                b0 = (a0 - n1) % n; b1 = (a0 + n2) % n; a1 = (b0 - 1 - n3) % n
                add(Pm, (off + a0, off + a1, off + b0, off + b1), qi * x / n)
        total += qi
        for j, (ooff, on) in enumerate(zip(offs[:-1], blocks)):
            if j != i:
                tpatterns(Pm, off, n, ooff, on, t[i, j]); total += t[i, j]
        tpatterns(Pm, off, n, K, m, tL[i]); total += tL[i]
        # T_Li with J-correlated L variables
        for odd in range(4):
            for o in range(n):
                for a in range(m):
                    for b in range(m):
                        wgt = tLi[i] / 4 / n * J[a, b] / m
                        if wgt == 0: continue
                        if odd == 0:   lam = (off + o, K + a, K + b, K + b)
                        elif odd == 1: lam = (K + a, off + o, K + b, K + b)
                        elif odd == 2: lam = (K + a, K + a, off + o, K + b)
                        else:          lam = (K + a, K + a, K + b, off + o)
                        add(Pm, lam, wgt)
        total += tLi[i]
    rho = (v / d - ZL / m) * J + (1 - v) / d ** 2
    for a in range(m):
        for b in range(m):
            add(Pm, (K + a, K + a, K + b, K + b), rho[a, b])
    total += rho.sum()
    err = np.abs(Pm - (v * P + (1 - v) / d ** 2)).max()
    wmin = min([rho.min(), tL.min(), tLi.min()] + ([t[~np.eye(r, dtype=bool)].min()] if r > 1 else []))
    return v, v0, total, err, wmin


if __name__ == '__main__':
    rng = np.random.default_rng(7)
    for mode, cases in (('A', [((3,), 2), ((2, 2), 2), ((3, 2), 1), ((4,), 3), ((5, 3), 4), ((2, 3, 4), 5)]),
                        ('B', [((3, 2), 15), ((2, 2), 9), ((4, 3), 20)])):
        for blocks, m in cases:
            P = strategy(blocks, m, rng)
            v, v0, tot, err, wmin = model(blocks, m, P, mode)
            d = sum(blocks) + m
            line = (f"mode {mode} blocks {blocks} + C_{m} (random U,V; d={d}): v={v:.10f} v0={v0:.10f} "
                    f"total={tot:.14f} max|model-P_v|={err:.1e} min weight={wmin:.2e}")
            if mode == 'A' and d <= 7:
                line += f"  LP v_c={vc(P):.10f} (diff {vc(P) - v0:+.1e})"
            ok = err < 1e-12 and abs(tot - 1) < 1e-12 and wmin >= -1e-15
            print(line + ('  OK' if ok else '  FAIL'), flush=True)
