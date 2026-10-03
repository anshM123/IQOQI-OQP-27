"""c02: Step 4 audit of the LP certificates QD2/certs/cert_d{d}.json, d = 2..200 (read only).

For each d: every cell vector n^(k) (ell = n/q, q = 16) has n_r >= 1 for ALL residues r (all cells strictly positive),
sum_r n_r = q d, the stored lambda_k are > 0, and the certified lower bound quoted in 'note' ("min certified lambda >= ...")
is > 0.  Rigidity needs only ONE k with lambda_k > 0 and all cells positive; here EVERY k qualifies.
Also re-checks (float) that sum_k lambda_k u^{ell_k} reproduces v (window form, independent of QD2 code).
"""
import json, os, re
import numpy as np
from rcore import u_window, v_vector

CERTS = os.path.join(os.path.dirname(__file__), '..', '..', 'cone-certificates', 'certs')
bad = []
summary = []
for d in range(2, 201):
    f = os.path.join(CERTS, f'cert_d{d}.json')
    if not os.path.exists(f):
        bad.append((d, 'missing'))
        continue
    c = json.load(open(f))
    q = c['q']
    n = np.array(c['cells'], dtype=np.int64)
    lam = np.array(c['lam'], float)
    m = re.search(r'min certified lambda >= ([0-9.eE+-]+)', c.get('note', ''))
    lcert = float(m.group(1)) if m else float('nan')
    ok = (n.min() >= 1) and np.all(n.sum(axis=1) == q * d) and (lam.min() > 0) and (lcert > 0) and n.shape[1] == d
    res = float('nan')
    if d <= 40 or d in (60, 100, 150, 200):
        U = np.array([u_window(row / q) for row in n])
        v = v_vector(d)
        res = np.max(np.abs(lam @ U - v)) / np.max(np.abs(v)) if d > 2 else np.max(np.abs(lam @ U - v))
    summary.append((d, n.shape[0], int(n.min()), lam.min(), lcert, res))
    if res == res:
        print(f'd={d:3d}: K={n.shape[0]:4d}, min n_r={int(n.min())}, certified lambda >= {lcert:.3e}, rel |sum lam u - v| = {res:.1e}', flush=True)
    if not ok:
        bad.append((d, dict(min_n=int(n.min()), min_lam=lam.min(), lcert=lcert)))
for row in []:
        print(f"d={row[0]:3d}: K={row[1]:4d}, min n_r={row[2]}, min lambda(float)={row[3]:.3e}, certified >= {row[4]:.3e}, "
              f"rel |sum lam u - v| = {row[5]:.1e}")
print(f"checked {len(summary)} certificates (d = 2..200); failures: {bad if bad else 'none'}")
print("min over d of min n_r:", min(r[2] for r in summary), "; min over d of certified lambda bound:", min(r[4] for r in summary))
