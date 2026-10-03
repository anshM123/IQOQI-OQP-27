# rf_01: item 5 / Lemma 1(e) / Lemma 2 -- check (1/2pi^2) int_R log|p_{s,tau}(xi)/q_{s,tau}(xi)| dxi = F(s,tau).
# p, q: coefficients obtained from DETERMINANTS det(g - s - xi(P - tau)), det(g_d - s - xi(P - tau)) at M+1 nodes
# (Vandermonde solve, 40 digits; independent of any eigen-solver), evaluated by Horner on [-L, L];
# tails |xi| > L by the root-product form (cancellation-free).  Quadrature: mpmath tanh-sinh at 20 digits,
# breakpoints at all real roots of p and q and at Re of the non-real roots of p.
import numpy as np, mpmath as mp, time
from rf_core import rand_inst, F_vals

rng = np.random.default_rng(20261002)


def coeffs_from_dets(Gm, Tm, s, M):
    I = mp.eye(M)
    nodes = [mp.mpf(k) - mp.mpf(M)/2 for k in range(M + 1)]
    vals = [mp.det(Gm - s*I - xi*Tm) for xi in nodes]
    V = mp.matrix([[xi**j for j in range(M + 1)] for xi in nodes])
    return mp.lu_solve(V, mp.matrix(vals))           # c_0..c_M (ascending)


def horner(c, xi):
    v = mp.mpf(0)
    for j in range(len(c) - 1, -1, -1):
        v = v*xi + c[j]
    return v


def check(B, g, s, tau):
    M = B.shape[0]
    with mp.workdps(40):
        Bm = mp.matrix(B.tolist()); gm = mp.matrix(g.tolist()); I = mp.eye(M); Pm = I - Bm
        gd = Bm*gm*Bm + Pm*gm*Pm
        s = mp.mpf(s); tau = mp.mpf(tau); Tm = Pm - tau*I
        cp = coeffs_from_dets(gm, Tm, s, M); cq = coeffs_from_dets(gd, Tm, s, M)
        xs = mp.polyroots([cp[j] for j in range(M, -1, -1)], maxsteps=200, extraprec=200)
        ys = mp.polyroots([cq[j] for j in range(M, -1, -1)], maxsteps=200, extraprec=200)
        r = int(round(np.trace(B).real))
        lead_formula = (-1)**M*(1 - tau)**(M - r)*(-tau)**r
        lead_err = max(abs(cp[M] - lead_formula), abs(cq[M] - lead_formula))
        sum_err = abs(cp[M - 1] - cq[M - 1])                       # equal root sums <=> equal x^{M-1} coefficients
        ys_im = max(abs(mp.im(y)) for y in ys)                       # Lemma 1(d): q real-rooted
        ys = [mp.re(y) for y in ys]
        F_mp = mp.fsum(abs(mp.im(x)) for x in xs)/(2*mp.pi)
        nonreal = sum(1 for x in xs if abs(mp.im(x)) > mp.mpf(10)**-25)
    with mp.workdps(20):
        f_mid = lambda xi: mp.log(abs(horner(cp, xi))) - mp.log(abs(horner(cq, xi)))

        def f_tail(xi):
            t = mp.mpf(0)
            for x in xs:
                z = x/xi; t += mp.log1p(-2*mp.re(z) + abs(z)**2)/2
            for y in ys:
                z = y/xi; t -= mp.log1p(-2*z + z**2)/2
            return t
        R = max(max(abs(x) for x in xs), max(abs(y) for y in ys)); L = 3*R + 1
        pts = sorted(set([mp.re(x) for x in xs] + list(ys)))
        pts = [-L] + [p for p in pts if -L < p < L] + [L]
        I_mid = mp.quad(f_mid, pts, maxdegree=7)
        I_tail = mp.quad(f_tail, [L, mp.inf]) + mp.quad(f_tail, [-mp.inf, -L])
        val = (I_mid + I_tail)/(2*mp.pi**2)
    Fd = F_vals(B, g, np.array([float(s)]), float(tau))[0]
    return dict(F_mp=F_mp, backproj=val, diff=val - F_mp, F_double=Fd, lead=lead_err, sumdiff=sum_err, qim=ys_im,
                nonreal=nonreal)


if __name__ == "__main__":
    print("(1/2pi^2) int log|p/q| dxi  vs  F = (1/2pi) sum|Im x_i|")
    for trial in range(15):
        M = int(rng.integers(3, 7)); r = int(rng.integers(1, M)); sc = [1.0, 5.0, 30.0][trial % 3]
        B, g = rand_inst(M, r, sc, rng)
        ev = np.linalg.eigvalsh(g)
        s = ev[0] + (ev[-1] - ev[0])*rng.uniform(0.05, 0.95); tau = rng.uniform(0.02, 0.98)
        t0 = time.time(); d = check(B, g, s, tau)
        print(f"M={M} r={r} sc={sc:5.1f} s={s:+9.4f} tau={tau:.4f} #nonreal={d['nonreal']}: F={mp.nstr(d['F_mp'], 16)}"
              f"  backproj-F={mp.nstr(d['diff'], 3)}  |F_double-F|={abs(d['F_double'] - float(d['F_mp'])):.1e}"
              f"  lead-coef err={mp.nstr(d['lead'], 3)}  x^(M-1)-coef diff={mp.nstr(d['sumdiff'], 3)}"
              f"  max|Im y|={mp.nstr(d['qim'], 3)} ({time.time()-t0:.1f}s)", flush=True)
