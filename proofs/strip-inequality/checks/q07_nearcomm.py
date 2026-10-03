"""q07: NEAR-COMMUTING stress test (g = g_d + eps g_o, eps = 1e-3, |g_d| ~ 50-150): nu_2 lives on thin curved strips there, which a float
grid misses (q04 [2] 'nearcomm' reported deviations 1.0 / 0.59 for that reason).  Here ALL breakpoints are the real roots of the
x-discriminant along the path (a polynomial of degree <= M(M-1) in the path parameter; Chebyshev interpolation at high precision +
polyroots), and the integrals are done by tanh-sinh in mpmath.
usage: python q07_nearcomm.py dps"""
import numpy as np, mpmath as mp, sys, time
from q_core import MPConf, breakpoints

def make(seed, M, r, eps):
    rng = np.random.default_rng(seed)
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); Q, _ = np.linalg.qr(Z); B = Q[:, :r] @ Q[:, :r].conj().T
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); G = 50*(G + G.conj().T)/2
    P = np.eye(M) - B; gd = B @ G @ B + P @ G @ P; go = G - gd; g = gd + eps*go
    return (g + g.conj().T)/2, B

def integ(C, path, u0, u1, deg):
    bps = breakpoints(lambda u: C.disc(*path(u)), u0, u1, deg + 4)
    edges = [u0] + bps + [u1]; tot = mp.mpf(0); err = mp.mpf(0)
    for a, b in zip(edges[:-1], edges[1:]):
        if b - a > mp.mpf(10)**(-mp.mp.dps + 5):
            v, e = mp.quad(lambda u: C.F(*path(u)), [a, b], error=True, maxdegree=10); tot += v; err += e
    return tot, err, len(bps)

if __name__ == "__main__":
    dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    for (seed, M, r) in [(0, 3, 1), (1, 3, 2), (2, 4, 2), (3, 4, 1)]:
        g, B = make(seed, M, r, 1e-3); C = MPConf(g, B, dps=dps); mp.mp.dps = dps; t0 = time.time()
        deg = M*(M - 1); fro = C.frob_BgP(); lo, hi = C.eg[0], C.eg[-1]
        print(f"=== seed {seed} M={M} r={r}: spec g = {np.round(np.linalg.eigvalsh(g), 3)}  ||BgP||^2 = {mp.nstr(fro, 8)}", flush=True)
        worst = mp.mpf(0)
        for tau in [mp.mpf('0.2718'), mp.mpf('0.7071')]:
            v, e, nb = integ(C, lambda u, tau=tau: (u, tau), lo, hi, deg)
            dev = abs(v - fro)/fro; worst = max(worst, dev)
            print(f"  marginal tau={mp.nstr(tau,4)}: {mp.nstr(v, 16)} vs {mp.nstr(fro, 16)}  rel.dev {mp.nstr(dev, 3)}  ({nb} bps, qerr {mp.nstr(e,2)})", flush=True)
        rng = np.random.default_rng(50 + seed)
        for _ in range(3):
            xi = mp.mpf(float(rng.normal()*60))
            lam = sorted(np.linalg.eigvalsh(g - float(xi)*(np.eye(M) - B)))
            w = mp.mpf(float(lam[0] + (lam[-1] - lam[0])*rng.uniform(0.2, 0.8)))
            Uv = C.U(xi, w)
            v, e, nb = integ(C, lambda u, xi=xi, w=w: (w + xi*u, u), mp.mpf(0), mp.mpf(1), deg)
            dev = abs(v - Uv)/max(abs(Uv), mp.mpf(10)**-25); worst = max(worst, dev)
            print(f"  Radon xi={mp.nstr(xi,5)} w={mp.nstr(w,6)}: {mp.nstr(v, 16)} vs U = {mp.nstr(Uv, 16)}  rel.dev {mp.nstr(dev, 3)}  ({nb} bps, qerr {mp.nstr(e,2)})", flush=True)
        print(f"  --> worst {mp.nstr(worst, 3)}  [{time.time()-t0:.0f}s]", flush=True)
