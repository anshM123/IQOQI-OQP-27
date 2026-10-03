"""Item 5/6: scan of all LP certificates QD2/certs/cert_d{2..200}.json (read only): q, all cells n_r >= 1, sum n = q d, lengths,
recorded certified min lambda > 0 (from the verifier note), float residual of v - U lam~ (window-sum form, float64, own Clausen)."""
import json, re, numpy as np
from k05_cone_lemmas_core import u_window_q
bad = []; minlam = []; res = []
for d in range(2, 201):
    c = json.load(open(f'../../cone-certificates/certs/cert_d{d}.json'))
    q = c['q']; cells = c['cells']; lam = np.array(c['lam'])
    ok = (c['d'] == d and all(len(n) == d for n in cells) and all(min(n) >= 1 for n in cells) and all(sum(n) == q * d for n in cells)
          and len(lam) == len(cells) and lam.min() > 0)
    mcert = float(re.search(r'min certified lambda >= ([0-9.eE+-]+)', c['note']).group(1))
    minlam.append((mcert, d))
    if not ok or mcert <= 0:
        bad.append(d)
    if d in (2, 3, 10, 50, 100, 150, 200):
        U = np.array([u_window_q(np.array(n), q, d) for n in cells]).T
        v = 2 / np.sin(np.pi * np.arange(1, d) / (2 * d))
        res.append((d, np.abs(U @ lam - v).max() / v.max()))
print("certificates with a defect:", bad)
print("smallest certified min lambda:", sorted(minlam)[:3])
print("float64 relative residual |U lam~ - v|/max v:", [(d, f"{r:.1e}") for d, r in res])
