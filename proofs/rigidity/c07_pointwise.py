"""c07: pointwise equality clause of (*) on step fields (NUMERICAL).  For theta on a fine grid of each cell, compute the (*)-defect at
lam* = log2/(2pi), def(theta) = sum_{nu in spec(B+ig)} h_lam*(nu) - Tr[(P(g-lam*)P)_+], and c(theta) = ||[B(theta), g(theta)]||_F.
Theorem 2(d) says def = 0 iff c = 0.  Report min def/c^2 over grid points with c > 1e-3 (should be > 0), and def where c ~ 0."""
import json, os
import numpy as np
from scipy.linalg import expm
from rcore import *
LAMS = 0.5 * np.log(2) / PI
rng = np.random.default_rng(3)
d = 4; N = 4 * d
c = json.load(open(os.path.join('..', '..', 'cone-certificates', 'certs', f'cert_d{d}.json')))
ell = np.array(c['cells'][0], float) / c['q']
t = 2 * PI * cell_endpoints(ell) / N
r0 = 2
V0 = np.array([np.diag([1.0, (1j) ** (-(1 if k >= r0 else 0))]) for k in range(d)])
H = [(lambda X: (X + X.conj().T) / 2)(rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))) for k in range(d)]
for name, V in [('random M=3', random_family(d, 3, rng)), ('rotated mixture t=0.1',
                np.array([expm(1j * .1 * H[k]) @ V0[k] @ expm(-1j * .1 * H[k]) for k in range(d)])), ('commuting mixture', V0)]:
    Q = Q_from_family(V); A, B = AB(Q); M = Q.shape[-1]
    jumps = np.array([B[j] - B[j - 1] for j in range(N)])
    ratios, zero_def, maxdef_small = [], [], 0.0
    for x in range(N):
        Px = np.eye(M) - B[x]; ev, U = np.linalg.eigh(Px); Ub = U[:, ev > .5]
        for s in np.linspace(0.01, 0.99, 60):
            th = t[x] + (t[x + 1] - t[x]) * s
            g = np.einsum('j,jab->ab', np.log(np.abs(np.sin((th - t[:N]) / 2))), jumps) / PI
            nu = np.linalg.eigvals(B[x] + 1j * g)
            hs = hlam(np.clip(nu.real, 0, 1), nu.imag, LAMS).sum()
            comp = np.linalg.eigvalsh(Ub.conj().T @ g @ Ub) if Ub.shape[1] else np.zeros(0)
            de = hs - np.clip(comp - LAMS, 0, None).sum()
            cm = np.linalg.norm(B[x] @ g - g @ B[x])
            if cm > 1e-3: ratios.append(de / cm ** 2)
            else: maxdef_small = max(maxdef_small, abs(de))
    print(f"[{name}] points with ||[B,g]|| > 1e-3: {len(ratios)};  min defect/||[B,g]||^2 = "
          f"{(min(ratios) if ratios else float('nan')):.3e};  max |defect| where ||[B,g]|| <= 1e-3: {maxdef_small:.1e}")
