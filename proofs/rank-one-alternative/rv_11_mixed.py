"""Referee: adversarial test of T >= 0 restricted to the NON-trivial region (Lemma 3 does not apply): quantiles of both
signs, min gamma <= -q0 and max gamma >= q0 (q0 = 0.05 * scale), s in (0, 1] (s = 1 is (*) for rank-one B).
Objective T / min(1, |P g v|^2), mixed-sign condition enforced by a barrier.  usage: python rv_11_mixed.py M nstart gmax seed"""
import numpy as np, sys, time
from scipy.optimize import minimize
from rv_core import h, herm_from, PI

M = int(sys.argv[1]); nstart = int(sys.argv[2]); gmax = float(sys.argv[3]); seed = int(sys.argv[4])
rng = np.random.default_rng(seed)
q0 = 0.05*gmax
XMIN = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0

def unpack(p, sfix):
    s = sfix if sfix is not None else 0.005 + 0.995/(1 + np.exp(-np.clip(p[0], -50, 50)))
    v = p[1:M + 1] + 1j*p[M + 1:2*M + 1]; v = v/np.linalg.norm(v)
    g = herm_from(gmax*np.tanh(p[2*M + 1:]), M)
    return s, v, g

def parts(s, v, g):
    P = np.eye(M) - np.outer(v, v.conj())
    lhs = np.sum(h(np.linalg.eigvals(s*np.outer(v, v.conj()) + 1j*g)))
    w = np.linalg.eigvalsh(P @ g @ P)
    # drop the zero eigenvalue belonging to v: spec of PgP on ran P
    k = np.argmin(np.abs(w)); gam = np.delete(w, k)
    T = lhs - np.sum(np.maximum(gam, 0)) - (1 - s)*max(np.real(v.conj() @ g @ v), 0)
    c2 = np.linalg.norm(P @ g @ v)**2
    return T, gam, c2

def obj(p, sfix):
    if not np.all(np.isfinite(p)): return 1e3
    s, v, g = unpack(p, sfix)
    T, gam, c2 = parts(s, v, g)
    bar = max(0.0, q0 - gam.max()) + max(0.0, q0 + gam.min())
    xs = np.linalg.eigvals(s*np.outer(v, v.conj()) + 1j*g).real
    bar += 100.0*max(0.0, XMIN*s - xs.min())          # irreducible: no near-atoms (else Lemma 4 + Lemma 3 make T tiny)
    if c2 < 1e-12: return 1e3
    return T/min(1.0, c2) + 10.0*bar

t0 = time.time()
for sfix in (1.0, None):
    best = (1e9, None)
    for st in range(nstart):
        p0 = np.concatenate([[rng.normal()*2], rng.normal(size=2*M), rng.normal(size=M*M)*rng.choice([0.3, 1.0, 2.0])])
        if st % 3 == 1: p0[0] = -4 - 2*rng.random()
        try:
            r = minimize(obj, p0, args=(sfix,), method='L-BFGS-B', options=dict(maxiter=1500))
            r = minimize(obj, r.x, args=(sfix,), method='Nelder-Mead', options=dict(maxiter=3000*M, maxfev=3000*M, xatol=1e-10, fatol=1e-14))
        except Exception:
            continue
        if r.fun < best[0]: best = (r.fun, r.x)
    s, v, g = unpack(best[1], sfix)
    T, gam, c2 = parts(s, v, g)
    tag = 's=1' if sfix else 's<1'
    xs_ = np.linalg.eigvals(s*np.outer(v, v.conj()) + 1j*g).real
    print(f'[mixed M={M} gmax={gmax} xmin={XMIN} seed={seed} {tag}] min x/s {xs_.min()/s:.3f} min obj {best[0]:.4e}: T = {T:.4e}, s = {s:.4f}, c2 = {c2:.3e}, '
          f'gamma range [{gam.min():.2f}, {gam.max():.2f}], |g| = {np.abs(np.linalg.eigvalsh(g)).max():.1f}', flush=True)
    np.save(f'rv_11_worst_M{M}_g{int(gmax)}_s{seed}_x{XMIN}_{"s1" if sfix else "sub"}.npy', np.concatenate([[s], best[1]]))
    if T < -1e-9:
        print('   CANDIDATE VIOLATION -- check at 50 digits', flush=True)
print(f'   ({time.time() - t0:.0f}s)', flush=True)
