# (a) is  sum h(spec(s vv* + i g)) >= Tr[(PgP)_+]  (P = 1 - vv*) for s in [0,1]?   (b) monotone in s?
import sys; sys.path.insert(0, '../common')
import numpy as np
from fcore import hstrip
rng = np.random.default_rng(7)
worst = 1e9; nonmono = 0; tot = 0
for trial in range(3000):
    M = rng.integers(2, 7)
    sc = 10**rng.uniform(-1, 2.3)
    g = rng.normal(size=(M,M)) + 1j*rng.normal(size=(M,M)); g = (g+g.conj().T)/2*sc
    if rng.random() < 0.3:   # clustered / large single eigenvalue
        w, U = np.linalg.eigh(g); w[-1] *= 20; g = (U*w)@U.conj().T
    v = rng.normal(size=M)+1j*rng.normal(size=M); v /= np.linalg.norm(v)
    P = np.eye(M) - np.outer(v, v.conj())
    rhs = np.sum(np.maximum(np.linalg.eigvalsh(P@g@P), 0))
    ss = np.linspace(0, 1, 41)
    vals = np.array([np.sum(hstrip(np.linalg.eigvals(s*np.outer(v, v.conj()) + 1j*g))) for s in ss])
    d = vals - rhs
    rel = d.min()/max(1.0, abs(rhs))
    if rel < worst: worst = rel; wcase = (M, sc, ss[d.argmin()], d.min())
    tot += 1
    if np.any(np.diff(vals) > 1e-9) and np.any(np.diff(vals) < -1e-9): nonmono += 1
print('worst rel slack', worst, wcase, 'nonmonotone frac', nonmono/tot)
