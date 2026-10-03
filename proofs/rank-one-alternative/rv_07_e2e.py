"""Referee END-TO-END adversarial tests.
 mode 'rank1'  : (*) defect D(B,g) for B = vv*, M given, g with entries up to gmax (tanh box), clustered starts;
                 objectives D/min(R2, |g_o|_1) (scale-free, R2 = exact 2nd-order prediction) and D/max(1,|g|).
 mode 'allM5'  : same for every rank r = 1..4 at M = 5.
 mode 'dual'   : dual form for PVMs with a rank-one outcome: maximise |Tr(A iT(B))| / sum_k Phi(A_kk,B_kk,C_kk).
 usage: python rv_07_e2e.py mode M nstart gmax seed"""
import numpy as np, sys, time
from scipy.optimize import minimize
from rv_core import h, phip, Lfun, Tri, PI, herm_from, unitary_from, star_defect

mode = sys.argv[1]; M = int(sys.argv[2]); nstart = int(sys.argv[3]); gmax = float(sys.argv[4]); seed = int(sys.argv[5])
rng = np.random.default_rng(seed)

def R2(B, g):
    wB, VB = np.linalg.eigh(B)
    Bv = VB[:, wB > 0.5]; Pv = VB[:, wB <= 0.5]
    if Bv.shape[1] == 0 or Pv.shape[1] == 0: return 0.0
    k, Ek = np.linalg.eigh(Bv.conj().T @ g @ Bv); m, Em = np.linalg.eigh(Pv.conj().T @ g @ Pv)
    cc = Ek.conj().T @ (Bv.conj().T @ g @ Pv) @ Em
    w1 = (1 - 1e-13) + 1j*k[:, None]; w2 = 1e-13 + 1j*m[None, :]
    dd = (phip(w1 + 0*w2) - phip(w2 + 0*w1))/(w1 - w2)
    return float(np.sum(-2*np.real(dd)*np.abs(cc)**2))

def build(p, r):
    U = unitary_from(p[:M*M], M)
    B = U[:, :r] @ U[:, :r].conj().T
    g = herm_from(gmax*np.tanh(p[M*M:]), M)
    return B, g

def obj_ratio(p, r):
    if not np.all(np.isfinite(p)): return 1e3
    B, g = build(p, r)
    D = star_defect(B, g)
    ref = R2(B, g)
    P = np.eye(M) - B
    go = g - B @ g @ B - P @ g @ P
    tr1 = np.sum(np.abs(np.linalg.eigvalsh(go)))
    den = min(ref, tr1)
    if den < 1e-10: return 1e3
    return D/den

def obj_abs(p, r):
    if not np.all(np.isfinite(p)): return 1e3
    B, g = build(p, r)
    return star_defect(B, g)/max(1.0, np.abs(np.linalg.eigvalsh(g)).max())

def start(r):
    p = np.concatenate([rng.normal(size=M*M)*2, rng.normal(size=M*M)*0.7])
    kind = rng.integers(4)
    if kind == 1:   # clustered spectrum of g: diagonal entries near a few cluster centres, small off-diagonal
        cent = rng.choice([-1, 1], size=M)*rng.uniform(0.2, 1)*0.9
        p[M*M:M*M + M] = np.arctanh(np.clip(cent + 1e-3*rng.normal(size=M), -0.999, 0.999))
        p[M*M + M:] *= 0.05
    if kind == 2:   # one huge eigenvalue (~ gmax), rest O(1)
        p[M*M:] = rng.normal(size=M*M)*0.02
        p[M*M + int(rng.integers(M))] = 3.0
    if kind == 3:   # large couplings
        p[M*M:] = rng.normal(size=M*M)*2.0
    return p

def run_star(ranks):
    worst = (1e9, None); worst_abs = (1e9, None)
    for st in range(nstart):
        r = int(ranks[st % len(ranks)])
        p0 = start(r)
        for obj, tag in ((obj_ratio, 'ratio'), (obj_abs, 'abs')):
            try:
                res = minimize(obj, p0, args=(r,), method='L-BFGS-B', options=dict(maxiter=1500))
                res = minimize(obj, res.x, args=(r,), method='Nelder-Mead',
                               options=dict(maxiter=2500*M, maxfev=2500*M, xatol=1e-10, fatol=1e-14))
            except Exception as e:
                continue
            if tag == 'ratio' and res.fun < worst[0]: worst = (res.fun, (r, res.x))
            if tag == 'abs' and res.fun < worst_abs[0]: worst_abs = (res.fun, (r, res.x))
    for (val, dat), tag in ((worst, 'ratio'), (worst_abs, 'abs')):
        if dat is None: continue
        r, x = dat
        B, g = build(x, r)
        D = star_defect(B, g)
        print(f'[{mode} M={M} gmax={gmax} seed={seed}] worst {tag} objective {val:.4e}: rank {r}, D = {D:.4e}, '
              f'R2 = {R2(B, g):.3e}, |g| = {np.abs(np.linalg.eigvalsh(g)).max():.2f}', flush=True)
        np.save(f'rv_07_worst_{mode}_M{M}_g{int(gmax)}_s{seed}_{tag}.npy', np.concatenate([[r, gmax], x]))
        if D < -1e-9:
            import mpmath as mp
            from rv_core import star_defect_mp
            mp.mp.dps = 50
            print('   CANDIDATE VIOLATION; 50-digit defect =', mp.nstr(star_defect_mp(B, g), 20), flush=True)

def run_dual():
    def ratio(p, ranks, slot):
        U = unitary_from(p, M)
        rA, rB, rC = ranks
        A = U[:, :rA] @ U[:, :rA].conj().T; B = U[:, rA:rA + rB] @ U[:, rA:rA + rB].conj().T
        C = np.eye(M) - A - B
        lhs = np.trace(A @ (1j*Tri(B))).real
        a, b, c = np.real(np.diag(A)), np.real(np.diag(B)), np.real(np.diag(C))
        rhs = np.sum(Lfun(a) + Lfun(b) + Lfun(c))
        if rhs < 1e-12: return 0.0
        return -abs(lhs)/rhs
    best = (0, None)
    pats = []
    for rk in range(0, M):           # one outcome of rank 1, in each of the three slots
        rest = M - 1 - rk
        pats += [(1, rk, rest), (rk, 1, rest), (rk, rest, 1)]
    pats = sorted(set(q for q in pats if min(q) >= 1))
    for st in range(nstart):
        ranks = pats[st % len(pats)]
        p0 = rng.normal(size=M*M)*rng.choice([0.5, 1.5, 3.0])
        res = minimize(ratio, p0, args=(ranks, 0), method='L-BFGS-B', options=dict(maxiter=2000))
        res = minimize(ratio, res.x, args=(ranks, 0), method='Nelder-Mead', options=dict(maxiter=4000*M, maxfev=4000*M, xatol=1e-10, fatol=1e-14))
        if -res.fun > best[0]: best = (-res.fun, (ranks, res.x))
    print(f'[dual M={M} seed={seed}] max |Tr(A iT(B))| / sum Phi = {best[0]:.6f} at ranks {best[1][0]}', flush=True)
    np.save(f'rv_07_worst_dual_M{M}_s{seed}.npy', np.concatenate([list(best[1][0]), best[1][1]]))

t0 = time.time()
if mode == 'rank1': run_star([1])
elif mode == 'allM5': run_star([1, 2, 3, 4])
elif mode == 'dual': run_dual()
print(f'   ({time.time() - t0:.0f}s)', flush=True)
