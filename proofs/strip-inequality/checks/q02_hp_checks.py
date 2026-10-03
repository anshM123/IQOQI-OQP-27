"""q02: high-precision (mpmath) checks of the closed form nu_2 = (1/2pi) sum |Im x_i| on 1D slices.
  (i)  tau-marginal:   int_R nu_2(s,tau) ds = ||B g P||_F^2           (vertical direction: NOT one of the Radon data used in the proof)
  (ii) Radon slices:   int_0^1 nu_2(w + xi tau, tau) dtau = U_xi(w)   (U_xi = convex-order potential of spec(g - xi P) vs pinched)
Breakpoints (where a pair of real roots collides) are located on a float grid and refined by bisection in mp; tanh-sinh on pieces.
usage: python q02_hp_checks.py [dps] [which]"""
import numpy as np, mpmath as mp, sys, time
from q_core import MPConf, F_float
sys.path.insert(0, '../../common')

DPS, WHICH = 50, None
if __name__ == "__main__":
    DPS = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    WHICH = sys.argv[2].split(',') if len(sys.argv) > 2 else None

# ------------------------------------------------------------------ configurations
def herm_from_params(p, M):
    Hm = np.zeros((M, M), complex); iu = np.triu_indices(M, 1); n = len(iu[0])
    Hm[np.diag_indices(M)] = p[:M]; Hm[iu] = p[M:M+n] + 1j*p[M+n:M+2*n]
    return Hm + np.triu(Hm, 1).conj().T

def unitary_from_params(p, M):
    w, V = np.linalg.eigh(herm_from_params(p, M)); return (V*np.exp(1j*w)) @ V.conj().T

def conf_t03():
    d = np.load('../../common/t03_CM_counterexample_M3.npy'); r = int(d[0]); gmax = d[1]; x = d[2:]; M = 3
    U = unitary_from_params(x[:M*M], M); B = U[:, :r] @ U[:, :r].conj().T
    g = herm_from_params(gmax*np.tanh(x[M*M:]), M); return g, B

def conf_t59():
    """clustered rank-one configuration of Qf-X19 (eigenvalues of B+ig ~ 1/3 + 23.07 i), built in Schur form g = diag(y) + i T(B)."""
    p = np.load('../../common/t59_best_M3_s0_Y30.npy'); M = 3; Y = 30.0
    e = np.exp(p[:M] - p[:M].max()); x = e/e.sum(); x = np.clip(x, 1e-9, 1); x = x/x.sum()
    y = Y*np.tanh(p[M:2*M]); lam = Y*np.tanh(p[-1])
    v = np.sqrt(x); B = np.outer(v, v).astype(complex)
    S = np.sign(np.subtract.outer(np.arange(M), np.arange(M)))
    g = np.diag(y - lam) + 1j*S*B           # shift by lam (threshold -> 0)
    return g, B

def conf_rand(M, r, scale, seed, big=None):
    rng = np.random.default_rng(seed)
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); Q, _ = np.linalg.qr(Z); B = Q[:, :r] @ Q[:, :r].conj().T
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); W, _ = np.linalg.qr(Z)
    ev = rng.normal(size=M)*scale
    if big is not None:
        ev[-1] = big                         # one huge eigenvalue (the t03 mechanism)
    g = (W*ev) @ W.conj().T; g = (g + g.conj().T)/2
    return g, B

def conf_cluster(M, r, seed, centre=40.0, spread=1e-3, off=3.0):
    """clustered spectrum of g (all eigenvalues within 'spread' of 'centre') plus one far eigenvalue 'off'."""
    rng = np.random.default_rng(seed)
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); Q, _ = np.linalg.qr(Z); B = Q[:, :r] @ Q[:, :r].conj().T
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); W, _ = np.linalg.qr(Z)
    ev = centre + spread*rng.normal(size=M); ev[0] = off
    g = (W*ev) @ W.conj().T; g = (g + g.conj().T)/2
    return g, B

CONFS = {
    't03':      conf_t03,
    't59':      conf_t59,
    'r3_1':     lambda: conf_rand(3, 1, 1.0, 11),
    'r3_2big':  lambda: conf_rand(3, 2, 2.0, 12, big=150.0),
    'r4_2big':  lambda: conf_rand(4, 2, 5.0, 13, big=-300.0),
    'r4_1':     lambda: conf_rand(4, 1, 30.0, 14),
    'c4_2':     lambda: conf_cluster(4, 2, 15),
    'r5_2':     lambda: conf_rand(5, 2, 60.0, 16),
}

# ------------------------------------------------------------------ path integration with breakpoints
def count_float(g, B, s, tau, rel=1e-7):
    M = g.shape[0]; P = np.eye(M) - B
    x = np.linalg.eigvals((P/(1 - tau) - B/tau) @ (g - s*np.eye(M)))
    sc = max(1.0, np.max(np.abs(x)))
    return int(np.sum(np.abs(x.imag) > rel*sc))

def count_mp(C, s, tau):
    if not (0 < tau < 1):
        return 0
    ev = C.roots(s, tau); thr = mp.mpf(10)**(-(mp.mp.dps*2)//3)
    sc = max([mp.mpf(1)] + [abs(e) for e in ev])
    return sum(1 for e in ev if abs(mp.im(e)) > thr*sc)

def path_integral(C, path, u0, u1, ngrid):
    """int_{u0}^{u1} F(path(u)) du ;  path(u) -> (s,tau) as mp numbers."""
    g, B = C.gf, C.Bf
    L = u1 - u0
    us = [mp.mpf(u0) + L*mp.mpf(10)**(-25)] + [mp.mpf(u) for u in np.linspace(float(u0), float(u1), ngrid)[1:-1]] \
         + [mp.mpf(u1) - L*mp.mpf(10)**(-25)]
    cnt = []
    for k, u in enumerate(us):
        s, t = path(u)
        if k == 0 or k == len(us) - 1:
            cnt.append(count_mp(C, s, t))          # near-endpoint counts in mp (float cannot resolve 1e-25 insets)
        else:
            cnt.append(count_float(g, B, float(s), float(t)) if 0 < float(t) < 1 else 0)
    bps = [mp.mpf(u0)]
    for k in range(len(us) - 1):
        if cnt[k] != cnt[k + 1]:
            a, b = us[k], us[k + 1]
            ca = count_mp(C, *path(a))
            for _ in range(int(mp.mp.dps*3.5)):
                m = (a + b)/2
                if count_mp(C, *path(m)) == ca: a = m
                else: b = m
            bps.append((a + b)/2)
    bps.append(mp.mpf(u1))
    tot = mp.mpf(0); errt = mp.mpf(0)
    for a, b in zip(bps[:-1], bps[1:]):
        val, err = mp.quad(lambda u: C.F(*path(u)), [a, b], error=True, maxdegree=10)
        tot += val; errt += err
    return tot, errt, len(bps) - 2

# ------------------------------------------------------------------ main
if __name__ == "__main__":
    names = WHICH or list(CONFS)
    for name in names:
        g, B = CONFS[name]()
        C = MPConf(g, B, dps=DPS)
        M = C.M; t0 = time.time()
        print(f"=== {name}: M={M} r={C.r}  spec g = {np.round(np.linalg.eigvalsh(g), 4)}   (dps={DPS})", flush=True)
        lo, hi = C.eg[0], C.eg[-1]
        fro = C.frob_BgP()
        worst = mp.mpf(0)
        for tau in [mp.mpf('0.137'), mp.mpf('0.5'), mp.mpf('0.911')]:
            val, err, nb = path_integral(C, lambda u, tau=tau: (u, tau), lo, hi, 20001)
            dev = abs(val - fro)/fro; worst = max(worst, dev)
            print(f"  tau-marginal tau={mp.nstr(tau,4)}: int = {mp.nstr(val, 20)}  ||BgP||^2 = {mp.nstr(fro, 20)}  rel.dev = {mp.nstr(dev, 3)}  (quad err {mp.nstr(err,2)}, {nb} bps)", flush=True)
        # Radon slices: choose xi and w where U is not small
        rng = np.random.default_rng(7)
        for k in range(3):
            xi = mp.mpf(float(rng.normal()*max(1.0, float(hi - lo))/2))
            lam = sorted(np.linalg.eigvalsh(g - float(xi)*(np.eye(M) - B)))
            w = mp.mpf(float(lam[0] + (lam[-1] - lam[0])*rng.uniform(0.2, 0.8)))
            Uv = C.U(xi, w)
            val, err, nb = path_integral(C, lambda u, xi=xi, w=w: (w + xi*u, u), mp.mpf(0), mp.mpf(1), 20001)
            dev = abs(val - Uv)/max(abs(Uv), mp.mpf(10)**(-DPS//2)); worst = max(worst, dev)
            print(f"  Radon xi={mp.nstr(xi,5)} w={mp.nstr(w,6)}: int = {mp.nstr(val, 20)}  U = {mp.nstr(Uv, 20)}  rel.dev = {mp.nstr(dev, 3)}  (quad err {mp.nstr(err,2)}, {nb} bps)", flush=True)
        print(f"  --> worst relative deviation {mp.nstr(worst, 3)}   [{time.time()-t0:.0f}s]", flush=True)
