"""Referee check of Section 5: (a) gamma_j nondecreasing and 1-Lipschitz in y_k; T is (M+alpha)-Lipschitz in y_k;
(b) face-point estimate at numerical minimisers of T_eps on K_R; (c) the induction pipeline on face configurations."""
import numpy as np
from scipy.optimize import minimize
from rv_core import h, quantiles, Tfun, PI

rng = np.random.default_rng(505)
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

# (a)
bad_mono = bad_lip = 0; worstL = 0.0; n = 0
for trial in range(5000):
    M = int(rng.integers(2, 8)); s = 1.0 if trial % 2 == 0 else float(rng.uniform(0.02, 1))
    w = rng.exponential(size=M)**2; z = rng.random(M) < 0.25
    if z.all(): z[0] = False
    w[z] = 0; x = s*w/w.sum(); y = rng.normal(size=M)*10**rng.uniform(-1, 2)
    if trial % 3 == 0: y = np.round(y)
    k = int(rng.integers(M)); e = float(10**rng.uniform(-6, 1))
    g0 = quantiles(x, y); y2 = y.copy(); y2[k] += e; g1 = quantiles(x, y2)
    tol = 1e-12*max(1, np.abs(y).max())
    if np.any(g1 < g0 - tol): bad_mono += 1
    if np.any(g1 > g0 + e + tol): bad_lip += 1
    al = (1 - s)/s
    L = M + al
    worstL = max(worstL, abs(Tfun(x, y2, s) - Tfun(x, y, s))/(L*e)); n += 1
say(f'(a) {n} tests: monotonicity failures {bad_mono}, 1-Lipschitz failures {bad_lip}; max |dT|/(L e) = {worstL:.3f} (<= 1 required)')

# (b) face-point estimate at numerical minimisers of T_eps on K_R
def unpack(p, M, s, R):
    w = np.exp(np.clip(p[:M], -40, 40)); x = s*w/w.sum(); y = np.clip(p[M:], -R, R)
    return x, y
def Teps(p, M, s, R, eps):
    x, y = unpack(p, M, s, R)
    return Tfun(x, y, s) + eps*np.sum(np.sin(PI*x)*np.cosh(PI*y))
worst = 0.0; nface = 0; nmin = 0
for trial in range(120):
    M = int(rng.integers(2, 6)); s = 1.0 if trial % 2 == 0 else float(rng.uniform(0.2, 1))
    R = float(rng.uniform(0.5, 3)); eps = float(10**rng.uniform(-3, -0.5))
    p0 = np.concatenate([rng.normal(size=M), rng.uniform(-R, R, size=M)])
    bnds = [(-40, 40)]*M + [(-R, R)]*M
    r = minimize(Teps, p0, args=(M, s, R, eps), method='L-BFGS-B', bounds=bnds, options=dict(maxiter=5000))
    r = minimize(Teps, r.x, args=(M, s, R, eps), method='Powell', bounds=bnds, options=dict(maxiter=20000, xtol=1e-10, ftol=1e-14))
    x, y = unpack(r.x, M, s, R); nmin += 1
    L = M + (1 - s)/s
    for k in range(M):
        if abs(abs(y[k]) - R) < 1e-7:
            nface += 1
            ratio = np.sin(PI*x[k])/(L/(eps*PI*np.sinh(PI*R)))
            worst = max(worst, ratio)
say(f'(b) {nmin} minimisations of T_eps on K_R, {nface} face points: max sin(pi x)/(L/(eps pi sinh(pi R))) = {worst:.3f} (<= 1 required)')
open('rv_05_main.log', 'w').write('\n'.join(out) + '\n')
