"""Referee check: Lemma 3 (easy cases), Lemma 4 (boundary points, multiset identity), Lemma 5 (near-boundary bound)."""
import numpy as np
from scipy.optimize import minimize
from rv_core import *

rng = np.random.default_rng(202)
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

def rand_conf(M, s, rng, pzero=0.0, scale=None):
    wts = rng.exponential(size=M)**2 + 1e-12
    if pzero > 0:
        nz = rng.random(M) < pzero
        if nz.all(): nz[0] = False
        wts[nz] = 0
    x = s*wts/wts.sum()
    sc = scale if scale is not None else 10**rng.uniform(-1, 2)
    y = rng.normal(size=M)*sc
    return x, y

# ---------------- Lemma 3
n1 = n2 = 0; w1 = w2 = 1e9; wid = 0.0; wi = 1e9
for trial in range(6000):
    M = int(rng.integers(2, 8)); s = 1.0 if trial % 3 == 0 else float(rng.uniform(0.02, 1))
    x, y = rand_conf(M, s, rng, pzero=0.2)
    if trial % 2 == 0: y = y - y.max() - rng.exponential()      # push quantiles negative
    else: y = y - y.min() + rng.exponential()                   # push positive
    gam = quantiles(x, y); al = (1 - s)/s; S = np.sum(x*y)
    T = Tfun(x, y, s)
    wi = min(wi, np.sum(h(x + 1j*y)) - al*max(S, 0))           # sum h >= alpha S_+ always
    if np.all(gam <= 0):
        n1 += 1; w1 = min(w1, T)
    if np.all(gam >= 0):
        n2 += 1; w2 = min(w2, T)
        wid = max(wid, abs(T - (np.sum(h(x - 1j*y)) - al*max(-S, 0)))/max(1, np.abs(y).max()))
say(f'Lemma 3: (i) {n1} configs with all gamma<=0, min T = {w1:.3e}; (ii) {n2} configs all gamma>=0, min T = {w2:.3e};')
say(f'         identity T = sum h(conj nu) - alpha S_- err {wid:.2e};  min(sum h - alpha S_+) over all = {wi:.3e}')

# ---------------- Lemma 4
bad = 0; eT = 0.0; ntest = 0
for trial in range(3000):
    M = int(rng.integers(2, 8)); s = 1.0 if trial % 3 == 0 else float(rng.uniform(0.02, 1))
    x, y = rand_conf(M, s, rng, pzero=0.4)
    if trial % 3 == 1: y = np.round(y)                # coincident atoms / points
    zs = np.where(x == 0)[0]
    if len(zs) == 0: continue
    m = zs[0]
    xp = np.delete(x, m); yp = np.delete(y, m)
    ts = np.concatenate([rng.normal(size=50)*(1 + np.abs(y).max()), y, y + 1e-13, y - 1e-13])
    F = Fdist(ts, x, y); Fp = Fdist(ts, xp, yp)
    lhs = np.minimum(np.floor(F), M - 1); rhs = np.minimum(np.floor(Fp), M - 2) + (ts >= y[m])
    bad += int(np.sum(lhs != rhs)); ntest += len(ts)
    eT = max(eT, abs(Tfun(x, y, s) - Tfun(xp, yp, s)))
say(f'Lemma 4: multiset identity failures {bad}/{ntest} t-values (incl. t = atoms, coincident atoms); max |T(nu)-T(nu\')| = {eT:.2e}')
# x_m = 1 case
e1 = 0.0
for trial in range(200):
    M = int(rng.integers(2, 7)); y = rng.normal(size=M)*10
    x = np.zeros(M); x[0] = 1.0
    e1 = max(e1, abs(Tfun(x, y, 1.0)))
say(f'Lemma 4 (x_m = 1, s = 1): max |T| = {e1:.2e}')

# ---------------- Lemma 5
def E(eta, R, M, s):
    return eta*(R + 1 + np.log(1/eta)) + 4*eta*R/s + 8*M*(R + 1)*np.sqrt(2*eta/s)

def parts(x, y, s, m, R, eta):
    x0 = x.copy(); x0[m] = 0.0; s0 = s - x[m]
    da = abs(h(x[m] + 1j*y[m]) - h(1j*y[m]))
    al, al0 = (1 - s)/s, (1 - s0)/s0
    db = abs(al*max(np.sum(x*y), 0) - al0*max(np.sum(x0*y), 0))
    dc = abs(np.sum(np.maximum(quantiles(x, y), 0)) - np.sum(np.maximum(quantiles(x0, y), 0)))
    Ea = eta*(R + 1 + np.log(1/eta)); Eb = 4*eta*R/s; Ec = 8*M*(R + 1)*np.sqrt(2*eta/s)
    dT = abs(Tfun(x, y, s) - Tfun(x0, y, s0))
    return dT, E(eta, R, M, s), (da/Ea, db/Eb, dc/Ec)

worst = 0.0; worst_parts = np.zeros(3)
for trial in range(4000):
    M = int(rng.integers(2, 8)); s = 1.0 if trial % 3 == 0 else float(rng.uniform(0.02, 1))
    R = float(10**rng.uniform(0, 2.5))
    x, y = rand_conf(M, s, rng, pzero=0.2, scale=R/2)
    y = np.clip(y, -R, R)
    m = 0; eta = float(10**rng.uniform(-12, np.log10(s/2)))
    xr = x.copy(); xr[0] = 0; tot = xr.sum()
    if tot == 0: xr[1] = 1.0; tot = 1.0
    xr = xr/tot*(s - eta); xr[0] = eta; x = xr
    if trial % 2 == 0:
        # adversarial: put an integer level of F'' exactly at y_m (quantile jump of order sqrt(eta))
        yo = np.delete(y, 0); xo = np.delete(x, 0)
        n = int(rng.integers(1, M)) if M > 1 else 1
        tq = quantiles(np.append(xo, 0.0), np.append(yo, 1e9))   # quantiles of the others (dummy far atom)
        if n - 1 < len(tq): y[0] = np.clip(tq[n - 1], -R, R)
    dT, Eb_, pr = parts(x, y, s, 0, R, eta)
    r = dT/Eb_
    worst_parts = np.maximum(worst_parts, pr)
    if r > worst: worst = r; wc = (M, s, R, eta)
say(f'Lemma 5 random+structured (4000): max |T(nu)-T(nu^0)|/E(eta) = {worst:.3e} at (M,s,R,eta)={wc};'
    f' max part ratios (a,b,c) = {np.round(worst_parts, 4)}')

# adversarial Nelder-Mead on the ratio
def ratio(p, M, s, R, eta):
    w = np.exp(np.clip(p[:M - 1], -30, 30)); xo = (s - eta)*w/w.sum()
    x = np.concatenate([[eta], xo]); y = R*np.tanh(p[M - 1:])
    dT, Eb_, _ = parts(x, y, s, 0, R, eta)
    return -dT/Eb_
best = 0.0
for trial in range(60):
    M = int(rng.integers(2, 7)); s = 1.0 if trial % 2 == 0 else float(rng.uniform(0.05, 1))
    R = float(10**rng.uniform(0, 1.5)); eta = float(10**rng.uniform(-8, np.log10(s/2)))
    p0 = np.concatenate([rng.normal(size=M - 1), rng.normal(size=M)*0.5])
    res = minimize(ratio, p0, args=(M, s, R, eta), method='Nelder-Mead', options=dict(maxiter=3000, xatol=1e-10, fatol=1e-14))
    if -res.fun > best: best = -res.fun; bc = (M, s, R, eta)
say(f'Lemma 5 adversarial (60 Nelder-Mead runs): max ratio = {best:.3e} at (M,s,R,eta) = {bc}')
open('rv_02_lemma345.log', 'w').write('\n'.join(out) + '\n')
