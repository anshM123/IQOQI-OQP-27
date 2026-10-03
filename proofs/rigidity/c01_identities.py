"""c01: the identities of the optimality chain used in the equality analysis (NUMERICAL sanity checks).

For random NON-commuting reduced families V (V_k^4 = 1, M = 2..4) and d = 3..12:
 (a) F(V) (clock formula)  ==  <A,B>_tau/2 - d/2                          [paper eq. (projform), E2-R2]
 (b) N(2d-m) = N(m), N(d) = d                                             [QD-L7]
 (c) <A,B>_tau - Phi_N  ==  <v, delta>                                    [QD2 s.4 (i)]
 (d) for positive cells ell:  (1/d) sum_{c<d} [Q^ell(rot_c) - N^2 Phi_c]  ==  <u^ell, delta>, u^ell from the window form;
     and every single rotated cell inequality Q^ell(rot_c) <= N^2 Phi_c holds                         [QD2-L1, QD2-L2]
 (e) with the LP certificate of QD2/certs (read only):  <A,B>_tau - Phi_N == sum_k lambda_k <u^{ell_k}, delta>
 (f) trivial directions:  N(s) + N(d-s) <= d.
"""
import json, os, sys
import numpy as np
from rcore import *

CERTS = os.path.join(os.path.dirname(__file__), '..', '..', 'cone-certificates', 'certs')
rng = np.random.default_rng(20261002)
PHIC = phic(0.25, 0.25)
worst = dict(a=0, b=0, c=0, d=0, e=0)
maxcell = -1e9
maxtriv = -1e9
for d in range(3, 13):
    N = 4 * d
    PhiN = phiN(d)
    k = cotk(N)
    Kd = np.array([[k[(x - y) % N] for y in range(N)] for x in range(N)])
    v = v_vector(d)
    c = json.load(open(os.path.join(CERTS, f'cert_d{d}.json')))
    cells = [np.array(n, float) / c['q'] for n in c['cells']]
    lam = np.array(c['lam'])
    ucert = np.array([u_window(l) for l in cells])
    rand_cells = [d * rng.dirichlet(np.ones(d)) for _ in range(3)]
    for t in range(6):
        M = int(rng.integers(2, 5))
        V = random_family(d, M, rng)
        Q = Q_from_family(V)
        A, B = AB(Q)
        P, T, Nm, delta = counts(Q)
        ABt = float(np.sum(Kd * P))
        worst['a'] = max(worst['a'], abs(F_clock(V) - (ABt / 2 - d / 2)))
        worst['b'] = max(worst['b'], max(abs(Nm[2 * d - m] - Nm[m]) for m in range(1, d)), abs(Nm[d] - d))
        worst['c'] = max(worst['c'], abs((ABt - PhiN) - v @ delta))
        for ell in rand_cells + cells[:2]:
            K = cell_kernel(ell)
            vals = []
            for cc in range(d):
                Kc = np.roll(np.roll(K, -cc, axis=0), -cc, axis=1)       # Kc[x,y] = K[x+cc, y+cc]
                vals.append(float(np.sum(Kc * P)) - N ** 2 * PHIC)
            maxcell = max(maxcell, max(vals))
            worst['d'] = max(worst['d'], abs(np.mean(vals) - u_window(ell) @ delta))
        worst['e'] = max(worst['e'], abs((ABt - PhiN) - lam @ (ucert @ delta)))
        for s in range(1, d):
            maxtriv = max(maxtriv, Nm[s] + Nm[d - s] - d)
    print(f"d={d:2d}: done (cert K={len(lam)}, min cell n_r = {min(min(n) for n in c['cells'])})", flush=True)
print("max abs errors:", {k_: f"{v_:.2e}" for k_, v_ in worst.items()})
print(f"max over samples of single rotated cell inequality Q^ell - N^2 Phi_c = {maxcell:.3e}  (must be <= 0)")
print(f"max over samples of N(s) + N(d-s) - d = {maxtriv:.3e}  (must be <= 0)")
