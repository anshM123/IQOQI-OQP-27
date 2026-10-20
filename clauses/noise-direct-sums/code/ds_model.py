"""ds_model.py -- end-to-end check of the Theorem DS local model for S = DKZ_k (+) DKZ_m at v_ds = d/(k kap_k + m kap_m).

Builds the explicit mixture of deterministic points
  F_i  (weight q_i): all four outcomes in block i; adapted variables (core.py convention)
       n1 = a0 - b0, n2 = b1 - a0, n3 = b0 - a1 - 1, n4 = a1 - b1  (mod n_i), sum = n_i - 1,
       drawn from an LP decomposition of phi_i on compositions, a0 uniform in block i;
  T_i  (weight tau_i = 2 Z_i): one 'odd' variable (A0, A1, B0 or B1, each 1/4) uniform in the other block, the other
       three in block i at one position with the two within-block adapted variables equal to 0;
and compares all 4 d^2 pairwise marginals with v_ds P + (1 - v_ds) u (P = behaviour of the direct sum, core.py).
"""
import sys, os, itertools
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import dkz_bases, behaviour     # noqa: E402
from ds_template import ime, G            # noqa: E402


def blockdiag(X, Y):
    n, m = X.shape[0], Y.shape[0]
    Z = np.zeros((n + m, n + m), complex); Z[:n, :n] = X; Z[n:, n:] = Y
    return Z


def comp_law(phi):
    S = len(phi) - 1
    comps = [c for c in itertools.product(range(S + 1), repeat=4) if sum(c) == S]
    A = np.zeros((4 * (S + 1), len(comps)))
    for j, c in enumerate(comps):
        for i in range(4):
            A[i * (S + 1) + c[i], j] = 1.0
    b = np.concatenate([phi] * 4)
    res = linprog(np.zeros(len(comps)), A_eq=A, b_eq=b, bounds=[(0, None)] * len(comps), method='highs')
    assert res.status == 0
    return comps, res.x


def model(k, m):
    d = k + m
    kap = {n: ime(n) / 2 for n in (k, m)}
    v = d / (k * kap[k] + m * kap[m])
    blocks = [(0, k), (k, m)]            # (offset, size)
    Pm = np.zeros((2, 2, d, d))
    total = 0.0
    for bi, (off, n) in enumerate(blocks):
        Z = (v * n / d) * (kap[n] - 1) - (1 - v) * n * n / d ** 2
        q = v * n / d * G(n) + (1 - v) * n / d ** 2
        q[0] -= Z
        qi = q.sum(); phi = q / qi
        comps, w = comp_law(phi)
        # F_i
        for c, wt in zip(comps, w):
            if wt <= 0: continue
            n1, n2, n3, n4 = c
            for a0 in range(n):
                b0 = (a0 - n1) % n; b1 = (a0 + n2) % n; a1 = (b0 - 1 - n3) % n
                assert (a1 - b1) % n == n4
                lam = (off + a0, off + a1, off + b0, off + b1)
                add(Pm, lam, qi * wt / n)
        total += qi
        # T_i: three variables in block i, odd one uniform in the other block
        tau = 2 * Z
        ooff, on = blocks[1 - bi]
        for odd in range(4):                     # 0 = A0, 1 = A1, 2 = B0, 3 = B1
            for p in range(n):
                # within-block links = the two links not containing the odd variable; adapted vars = 0
                if odd == 3:   a0, b0, a1 = p, p, (p - 1) % n          # n1 = 0, n3 = 0
                elif odd == 2: a0 = p; b1 = p; a1 = (p) % n             # n2 = 0 (b1 = a0), n4 = 0 (a1 = b1)
                elif odd == 1: a0 = p; b0 = p; b1 = p                   # n1 = 0, n2 = 0
                else:          b0 = p; a1 = (p - 1) % n; b1 = a1         # n3 = 0, n4 = 0
                for o in range(on):
                    if odd == 3: lam = (off + a0, off + a1, off + b0, ooff + o)
                    elif odd == 2: lam = (off + a0, off + a1, ooff + o, off + b1)
                    elif odd == 1: lam = (off + a0, ooff + o, off + b0, off + b1)
                    else: lam = (ooff + o, off + a1, off + b0, off + b1)
                    add(Pm, lam, tau / 4 / n / on)
        total += tau
    # target
    Ak, Fk = dkz_bases(k); Am, Fm = dkz_bases(m)
    A = np.array([blockdiag(Ak[x], Am[x]) for x in range(2)]); F = np.array([blockdiag(Fk[y], Fm[y]) for y in range(2)])
    P = behaviour(A, F)
    Pv = v * P + (1 - v) / d ** 2
    return v, total, np.abs(Pm - Pv).max()


def add(Pm, lam, w):
    a0, a1, b0, b1 = lam
    Pm[0, 0, a0, b0] += w; Pm[0, 1, a0, b1] += w; Pm[1, 0, a1, b0] += w; Pm[1, 1, a1, b1] += w


if __name__ == '__main__':
    for (k, m) in [(2, 2), (3, 2), (4, 2), (3, 3), (5, 3), (4, 4), (6, 2), (5, 4), (7, 3)]:
        v, tot, err = model(k, m)
        print(f"k={k} m={m}: v_ds = {v:.10f}  total weight = {tot:.12f}  max |model - P_v| = {err:.2e}", flush=True)
