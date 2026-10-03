"""Referee check of Lemma 7: (1) T_eps <= T~ near nu with equality; (2) holomorphic-derivative bookkeeping
d_x T~ - i d_y T~ (at nu_k) = f_0(nu_k), f_0 = Lemma-6 function with mu = 0; (3) roots-of-unity multiplicity
expansion  T~(pert) - T~(nu) = (1/(n-1)!) Re[f^{(n-1)}(nu*) eta^n] + O(|eta|^{2n})  at 60 digits;
(4) interior local minima of T_eps found numerically satisfy (all gamma <= 0) or (all gamma >= 0)."""
import numpy as np, mpmath as mp, sys
from scipy.optimize import minimize
from rv_core import h, quantiles, Tfun, PI

mp.mp.dps = 60
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

def h_mp(z):
    return -mp.im(mp.polylog(2, mp.exp(-1j*mp.pi*z)))/mp.pi**2
def u_mp(z):
    return mp.sin(mp.pi*mp.re(z))*mp.cosh(mp.pi*mp.im(z))
def F_mp(t, nus):
    return mp.fsum([mp.mpf(1)/2 + mp.atan((t - mp.im(z))/mp.re(z))/mp.pi for z in nus])
def Fp_mp(t, nus):
    return mp.fsum([mp.re(z)/(mp.pi*(mp.re(z)**2 + (t - mp.im(z))**2)) for z in nus])
def gam_mp(nus, j, t0):
    return mp.findroot(lambda t: F_mp(t, nus) - j, mp.mpf(t0), tol=mp.mpf(10)**(-55))

class Setup:
    def __init__(s, nus, sval, eps):
        s.nus = [mp.mpc(z) for z in nus]; s.M = len(nus); s.s = mp.mpf(sval); s.eps = mp.mpf(eps)
        x = np.array([float(mp.re(z)) for z in nus]); y = np.array([float(mp.im(z)) for z in nus])
        g0 = quantiles(x, y)
        s.gam = [gam_mp(s.nus, j + 1, g0[j]) for j in range(s.M - 1)]
        s.I = [j for j in range(s.M - 1) if s.gam[j] > 0]
        s.c = {j: 1/Fp_mp(s.gam[j], s.nus) for j in s.I}
        s.alpha = (1 - s.s)/s.s
        S = mp.fsum([mp.re(z)*mp.im(z) for z in s.nus])
        s.a = s.alpha if S > 0 else mp.mpf(0)
        s.g0 = g0
    def Ttilde(s, nus):
        gs = [gam_mp(nus, j + 1, s.gam[j]) for j in s.I]
        return (mp.fsum([h_mp(z) + s.eps*u_mp(z) for z in nus]) - mp.fsum(gs)
                - s.a*mp.fsum([mp.re(z)*mp.im(z) for z in nus]))
    def Teps(s, nus):
        x = [mp.re(z) for z in nus]
        gs = [gam_mp(nus, j + 1, s.gam[j]) for j in range(s.M - 1)]
        S = mp.fsum([mp.re(z)*mp.im(z) for z in nus])
        return (mp.fsum([h_mp(z) + s.eps*u_mp(z) for z in nus]) - mp.fsum([max(gg, 0) for gg in gs])
                - s.alpha*max(S, 0))
    def f0(s, z):
        return (-mp.log(1 - mp.exp(-1j*mp.pi*z))/mp.pi + s.eps*mp.pi*mp.cos(mp.pi*z)
                + (1j/mp.pi)*mp.fsum([s.c[j]/(z - 1j*s.gam[j]) for j in s.I]) + 1j*s.a*z)

rng = np.random.default_rng(404)

# ---------------- (1),(2) on random configurations
e_grad = 0.0; viol1 = 0; ntests = 0
for trial in range(12):
    M = int(rng.integers(3, 7)); sval = 1.0 if trial % 2 == 0 else float(rng.uniform(0.2, 1))
    w = rng.exponential(size=M) + 0.2; x = sval*w/w.sum(); y = rng.normal(size=M)*3 + 1.0
    st = Setup(x + 1j*y, sval, 0.05)
    if not st.I: continue
    for k in range(M):
        def Tx(t, k=k):
            nus = list(st.nus); nus[k] = mp.mpc(t, mp.im(nus[k])); return st.Ttilde(nus)
        def Ty(t, k=k):
            nus = list(st.nus); nus[k] = mp.mpc(mp.re(nus[k]), t); return st.Ttilde(nus)
        gx = mp.diff(Tx, mp.re(st.nus[k])); gy = mp.diff(Ty, mp.im(st.nus[k]))
        e_grad = max(e_grad, abs(complex(gx - 1j*gy - st.f0(st.nus[k]))))
    T0 = st.Ttilde(st.nus); Te0 = st.Teps(st.nus)
    for rep in range(5):   # random perturbations on the constraint manifold
        d = (rng.normal(size=M) + 1j*rng.normal(size=M))*1e-3; d = d - d.real.mean()
        nus = [z + mp.mpc(complex(dd)) for z, dd in zip(st.nus, d)]
        ntests += 1
        if st.Teps(nus) > st.Ttilde(nus) + mp.mpf(10)**-40: viol1 += 1
    say(f'  M={M} s={sval:.3f} |I|={len(st.I)} a={float(st.a):.3f}: T~ - T_eps at nu = {mp.nstr(T0 - Te0, 3)}')
say(f'(1) T_eps <= T~ near nu: violations {viol1}/{ntests};  (2) max |d_x T~ - i d_y T~ - f_0(nu_k)| = {e_grad:.2e}')

# ---------------- (3) multiplicity expansion with coincident points
for (M, m, sval) in [(4, 2, 1.0), (4, 3, 0.7), (5, 3, 1.0), (6, 4, 0.8)]:
    w = rng.exponential(size=M - m + 1) + 0.3; xs = sval*w/w.sum()
    xstar = xs[0]/m       # m coincident points share x*
    x = np.concatenate([[xstar]*m, xs[1:]]); x = x*sval/x.sum()
    y = np.concatenate([[0.7]*m, rng.normal(size=M - m)*2 + 1.5])
    st = Setup(x + 1j*y, sval, 0.05)
    if not st.I:
        say(f'  (M={M},m={m}) no positive quantile; skipped'); continue
    nstar = st.nus[0]
    for n in range(2, m + 1):
        dn = mp.diff(st.f0, nstar, n - 1)
        lines = []
        for r in [mp.mpf('1e-2'), mp.mpf('1e-3'), mp.mpf('1e-4')]:
            th = mp.mpf(rng.uniform(0, 2*np.pi)); eta = r*mp.expjpi(th/mp.pi)
            wq = [mp.expjpi(2*mp.mpf(q)/n) for q in range(n)]
            nus = list(st.nus)
            for q in range(n): nus[q] = nstar + eta*wq[q]
            D = st.Ttilde(nus) - st.Ttilde(st.nus)
            Lead = mp.re(dn*eta**n)/mp.factorial(n - 1)
            lines.append(f'r={mp.nstr(r,2)}: D={mp.nstr(D,6)} lead={mp.nstr(Lead,6)} |D-lead|/r^(2n)={mp.nstr(abs(D-Lead)/r**(2*n),4)}')
        say(f'(3) M={M} m={m} s={sval} n={n}: ' + ' | '.join(lines))

# ---------------- (4) interior local minima of T_eps
def Teps_np(p, M, sval, eps):
    w = np.exp(np.clip(p[:M], -40, 40)); x = sval*w/w.sum(); y = p[M:]
    return Tfun(x, y, sval) + eps*np.sum(np.sin(PI*x)*np.cosh(PI*np.clip(y, -50, 50)))
found = 0; bad = 0; minT = 1e9
for trial in range(150):
    M = int(rng.integers(3, 6)); sval = 1.0 if trial % 2 == 0 else float(rng.uniform(0.2, 1)); eps = 10**rng.uniform(-3, -1)
    p0 = np.concatenate([rng.normal(size=M), rng.normal(size=M)*2])
    r = minimize(Teps_np, p0, args=(M, sval, eps), method='Nelder-Mead', options=dict(maxiter=20000, xatol=1e-10, fatol=1e-14))
    w = np.exp(np.clip(r.x[:M], -40, 40)); x = sval*w/w.sum(); y = r.x[M:]
    if x.min() < 1e-4 or x.max() > 1 - 1e-4: continue       # boundary minimum (Lemma 4 case)
    found += 1
    g = quantiles(x, y); T = Tfun(x, y, sval); minT = min(minT, T)
    if not (np.all(g <= 1e-7) or np.all(g >= -1e-7)):
        bad += 1; say(f'  interior min with mixed-sign quantiles: M={M} s={sval:.3f} eps={eps:.2e} gamma={g} T={T:.3e}')
say(f'(4) interior local minima found: {found}; with mixed-sign quantiles: {bad}; min T there = {minT:.3e}')
open('rv_04_lemma7.log', 'w').write('\n'.join(out) + '\n')
