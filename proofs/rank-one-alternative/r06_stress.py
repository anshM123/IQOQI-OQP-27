# stress test of T >= 0 directly on configurations (1-D form), large scales + clustered, s in (0,1]
import sys; sys.path.insert(0, '../common')
import numpy as np
from fcore import hstrip
from scipy.optimize import brentq, minimize
PI = np.pi
rng = np.random.default_rng(21)
def T(x, y, s):
    M = len(x)
    F = lambda t: np.sum(0.5 + np.arctan((t - y)/x)/PI)
    lo, hi = y.min() - 1e3 - 1e3*abs(y).max(), y.max() + 1e3 + 1e3*abs(y).max()
    gam = np.array([brentq(lambda t: F(t) - j, lo, hi, xtol=1e-12, rtol=1e-15) for j in range(1, M)])
    al = (1 - s)/s
    return np.sum(hstrip(x + 1j*y)) - np.sum(np.maximum(gam, 0)) - al*max(np.sum(x*y), 0)
def unpack(p, M, s):
    w = np.exp(p[:M]); x = s*w/w.sum()
    x = np.clip(x, 1e-12, 1 - 1e-12)
    return x, p[M:]
worst = 1e9
for trial in range(600):
    M = int(rng.integers(3, 8)); s = 1.0 if rng.random() < 0.5 else float(rng.uniform(0.05, 1))
    if s == 1.0 and M > 1:
        pass
    sc = 10**rng.uniform(-0.5, 2.5)
    p0 = np.concatenate([rng.normal(size=M)*2, rng.normal(size=M)*sc])
    if rng.random() < 0.3: p0[M:] = sc*np.sign(rng.normal(size=M)) + rng.normal(size=M)  # clustered
    def fun(p):
        x, y = unpack(p, M, s)
        if np.any(x >= 1): return 1e3
        return T(x, y, s)/max(1.0, np.abs(y).max())
    try:
        r = minimize(fun, p0, method='Nelder-Mead', options={'maxiter': 3000, 'xatol': 1e-9, 'fatol': 1e-13})
    except Exception as e:
        continue
    if r.fun < worst:
        worst = r.fun; wc = (M, s, sc)
print('worst normalized T =', worst, wc)
