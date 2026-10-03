"""Referee: adversarial test of the s < 1 statement of the Main Theorem (needed for the induction):
   T = sum h(spec(s vv* + i g)) - Tr[(PgP)_+] - (1-s) <v,gv>_+  >= 0,   P = 1 - vv*,
in matrix form (Lemma 1(b)), and in the 1-D configuration form with atoms.  usage: python rv_09_sub.py M nstart gmax seed"""
import numpy as np, sys, time
from scipy.optimize import minimize
from rv_core import h, herm_from, Tfun, quantiles, PI

M = int(sys.argv[1]); nstart = int(sys.argv[2]); gmax = float(sys.argv[3]); seed = int(sys.argv[4])
rng = np.random.default_rng(seed)

def unpack(p):
    s = 0.005 + 0.99/(1 + np.exp(-p[0]))
    v = p[1:M + 1] + 1j*p[M + 1:2*M + 1]; v = v/np.linalg.norm(v)
    g = herm_from(gmax*np.tanh(p[2*M + 1:]), M)
    return s, v, g

def Tmat(s, v, g):
    P = np.eye(M) - np.outer(v, v.conj())
    lhs = np.sum(h(np.linalg.eigvals(s*np.outer(v, v.conj()) + 1j*g)))
    rhs = np.sum(np.maximum(np.linalg.eigvalsh(P @ g @ P), 0)) + (1 - s)*max(np.real(v.conj() @ g @ v), 0)
    return lhs - rhs

def obj_abs(p):
    if not np.all(np.isfinite(p)): return 1e3
    s, v, g = unpack(p)
    return Tmat(s, v, g)/max(1.0, np.abs(np.linalg.eigvalsh(g)).max())

def obj_rel(p):
    if not np.all(np.isfinite(p)): return 1e3
    s, v, g = unpack(p)
    P = np.eye(M) - np.outer(v, v.conj())
    c2 = np.linalg.norm(P @ g @ v)**2
    if c2 < 1e-10: return 1e3
    return Tmat(s, v, g)/min(1.0, c2)

t0 = time.time()
worst = {}
for st in range(nstart):
    p0 = np.concatenate([[rng.normal()*2], rng.normal(size=2*M), rng.normal(size=M*M)*rng.choice([0.3, 1.0, 2.0])])
    if st % 3 == 1: p0[0] = -4 - 2*rng.random()       # small s (alpha large)
    for obj, tag in ((obj_abs, 'abs'), (obj_rel, 'rel')):
        r = minimize(obj, p0, method='L-BFGS-B', options=dict(maxiter=1500))
        r = minimize(obj, r.x, method='Nelder-Mead', options=dict(maxiter=3000*M, maxfev=3000*M, xatol=1e-10, fatol=1e-14))
        if tag not in worst or r.fun < worst[tag][0]:
            worst[tag] = (r.fun, r.x)
for tag, (val, x) in worst.items():
    s, v, g = unpack(x)
    T = Tmat(s, v, g)
    print(f'[sub M={M} gmax={gmax} seed={seed}] worst {tag}: obj {val:.4e}, T = {T:.4e}, s = {s:.4f}, |g| = {np.abs(np.linalg.eigvalsh(g)).max():.2f}', flush=True)
    if T < -1e-9:
        import mpmath as mp
        from rv_core import to_mp, h_mp
        mp.mp.dps = 50
        vm = to_mp(v.reshape(-1, 1)); gm = to_mp(g); sm = mp.mpf(s)
        X = sm*(vm*vm.H) + 1j*gm
        E, _ = mp.eig(X)
        P = mp.eye(M) - vm*vm.H
        w, _ = mp.eighe((P*gm*P + (P*gm*P).H)/2)
        k = mp.re((vm.H*gm*vm)[0, 0])
        T50 = mp.fsum([h_mp(e) for e in E]) - mp.fsum([max(mp.re(e), 0) for e in w]) - (1 - sm)*max(k, 0)
        print('   CANDIDATE; 50-digit T =', mp.nstr(T50, 20), flush=True)
    np.save(f'rv_09_worst_M{M}_g{int(gmax)}_s{seed}_{tag}.npy', x)
print(f'   ({time.time() - t0:.0f}s)', flush=True)
