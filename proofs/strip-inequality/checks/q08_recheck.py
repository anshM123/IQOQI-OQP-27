"""q08: recheck of the three weaker numerical results with EXACT breakpoints (real roots of the x-discriminant, q_core.breakpoints):
 (1) q02 'c4_2' (clustered spec g within 1.3e-3 of 40): tau-marginals at tau = 0.137, 0.911 (q02 grid gave 1.5e-9, 5.9e-10);
 (2) q06 case M=4, spec B = (0, 0.6, 0.6, 1): Radon slice xi = 25.029, w = 0.855447 (q06 gave 5.5e-8, interior line not a breakpoint);
 (3) near-commuting M = 5, 6 (q04 [7] gave O(0.1) because a float grid misses the thin windows).
usage: python q08_recheck.py dps"""
import numpy as np, mpmath as mp, sys, time
from q_core import MPConf, breakpoints
from q02_hp_checks import CONFS
from q06_generalB_hp import setup, GB
from q07_nearcomm import make, integ

def integ_gb(C, path, u0, u1, deg, extra):
    def disc(u):
        s, t = path(u); M = C.M
        ev = C.roots(s, t)
        lead = mp.mpf(1)
        for b, V in zip(C.bs, C.Pis):
            lead *= (b - t)**V.cols
        pr = mp.mpf(1)
        for i in range(M):
            for j in range(i + 1, M):
                pr *= (ev[i] - ev[j])**2
        return mp.re(lead**(2*M - 2)*pr)
    bps = breakpoints(disc, u0, u1, deg + 4)
    edges = sorted(set([u0] + bps + [mp.mpf(e) for e in extra] + [u1])); tot = mp.mpf(0); err = mp.mpf(0)
    for a, b in zip(edges[:-1], edges[1:]):
        if b - a > mp.mpf(10)**(-mp.mp.dps + 5):
            v, e = mp.quad(lambda u: C.F(*path(u)), [a, b], error=True, maxdegree=10); tot += v; err += e
    return tot, err, len(bps)

if __name__ == "__main__":
    dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    # (1)
    g, B = CONFS['c4_2'](); C = MPConf(g, B, dps=dps); mp.mp.dps = dps; M = C.M; fro = C.frob_BgP()
    for tau in [mp.mpf('0.137'), mp.mpf('0.911')]:
        t0 = time.time(); v, e, nb = integ(C, lambda u, tau=tau: (u, tau), C.eg[0], C.eg[-1], M*(M - 1))
        print(f"(1) c4_2 marginal tau={mp.nstr(tau,4)}: {mp.nstr(v, 20)} vs {mp.nstr(fro, 20)} rel.dev {mp.nstr(abs(v-fro)/fro, 3)} ({nb} bps, qerr {mp.nstr(e,2)}) [{time.time()-t0:.0f}s]", flush=True)
    # (2)
    bs = [0.0, 0.6, 1.0]; A, U, lab = setup(2, 4, bs, [1, 2, 1], 20.0); mp.mp.dps = dps; Cg = GB(A, U, lab, bs)
    xi = mp.mpf(25.029); w = mp.mpf(0.855447)
    # use the same float values as q06 printed (rounded); recompute U at these values
    Uv = Cg.U(xi, w); t0 = time.time()
    v, e, nb = integ_gb(Cg, lambda u: (w + xi*u, u), Cg.bs[0], Cg.bs[-1], 12, [Cg.bs[1]])
    print(f"(2) general B (0,0.6,0.6,1): Radon {mp.nstr(v, 20)} vs U {mp.nstr(Uv, 20)} rel.dev {mp.nstr(abs(v-Uv)/Uv, 3)} ({nb} bps, qerr {mp.nstr(e,2)}) [{time.time()-t0:.0f}s]", flush=True)
    # (3)
    for (seed, M, r) in [(10, 5, 2), (11, 6, 2), (12, 6, 3)]:
        g, B = make(seed, M, r, 1e-3); C = MPConf(g, B, dps=dps); mp.mp.dps = dps; fro = C.frob_BgP(); t0 = time.time()
        v, e, nb = integ(C, lambda u: (u, mp.mpf('0.3819')), C.eg[0], C.eg[-1], M*(M - 1))
        msg = f"(3) nearcomm M={M} r={r}: marginal {mp.nstr(v, 16)} vs {mp.nstr(fro, 16)} rel.dev {mp.nstr(abs(v-fro)/fro, 3)} ({nb} bps)"
        rng = np.random.default_rng(seed); xi = mp.mpf(float(rng.normal()*60))
        lam = sorted(np.linalg.eigvalsh(g - float(xi)*(np.eye(M) - B))); w = mp.mpf(float(lam[0] + (lam[-1] - lam[0])*0.43))
        Uv = C.U(xi, w); v, e, nb = integ(C, lambda u: (w + xi*u, u), mp.mpf(0), mp.mpf(1), M*(M - 1))
        print(msg + f";  Radon {mp.nstr(v, 16)} vs U {mp.nstr(Uv, 16)} rel.dev {mp.nstr(abs(v-Uv)/Uv, 3)} ({nb} bps) [{time.time()-t0:.0f}s]", flush=True)
