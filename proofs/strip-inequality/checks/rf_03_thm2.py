# rf_03: item 7 + item 8(ii),(iii) -- Theorem 2: defect(lam) := sum_{nu in spec(B+ig)} h_lam(nu) - Tr[(P(g-lam)P)_+]
#        equals V(lam) = int_0^1 int_R K_{1-tau}(s - lam) F(s,tau) ds dtau  (>= 0).
# defect: mpmath (eigenvalues of B + ig at 40 digits, Li2 with inversion for |z| > 1); V: double-precision adaptive
# quadrature (rf_core.V_lams).  Also: Lemma 5 (Laplace transform of K_X at complex a) and Lemma 6 (Poisson integral).
import sys, time
import numpy as np, mpmath as mp
from rf_core import rand_inst, rand_unitary, decode_t03, defect_mp, V_lams, h_mp_mpc


def lemma56():
    mp.mp.dps = 25
    print("Lemma 5: int e^{-au} K_X(u) du vs sin(a(1-X))/sin a")
    for X, a in [(0.3, 0.7 + 0.4j), (0.8, -2.5 + 3.0j), (0.05, 3.0 - 1.0j), (0.5, 2.9), (0.97, -3.1 + 0.2j)]:
        X = mp.mpf(X); a = mp.mpc(a)
        K = lambda u: mp.sin(mp.pi*X)/(2*(mp.cosh(mp.pi*u) - mp.cos(mp.pi*X)))
        lhs = mp.quad(lambda u: mp.exp(-a*u)*K(u), [-mp.inf, -1, 0, 1, mp.inf])
        rhs = mp.sin(a*(1 - X))/mp.sin(a)
        print(f"   X={mp.nstr(X, 3)} a={mp.nstr(a, 4)}: |lhs - rhs| = {mp.nstr(abs(lhs - rhs), 3)}  (rhs = {mp.nstr(rhs, 12)})")
    print("Lemma 6: h_lam(X+iY) vs int (w - lam)_+ K_X(Y - w) dw")
    for X, Y, lam in [(0.3, 0.4, 1.0), (0.7, 2.5, -0.3), (0.02, 1.3, 0.9), (0.95, -1.0, -3.0), (0.5, 40.0, 1.5)]:
        X = mp.mpf(X); Y = mp.mpf(Y); lam = mp.mpf(lam)
        K = lambda u: mp.sin(mp.pi*X)/(2*(mp.cosh(mp.pi*u) - mp.cos(mp.pi*X)))
        rhs = mp.quad(lambda w: (w - lam)*K(Y - w), [lam, Y, mp.inf] if Y > lam else [lam, mp.inf])
        lhs = h_mp_mpc(mp.mpc(X, Y), lam, 25)
        print(f"   z={mp.nstr(X, 3)}+i{mp.nstr(Y, 4)} lam={mp.nstr(lam, 3)}: h = {mp.nstr(lhs, 15)}  |h - Poisson| = {mp.nstr(abs(lhs - rhs), 3)}")


def run(name, B, g, lams):
    t0 = time.time()
    V, err, nev = V_lams(B, g, lams)
    print(f"{name}: spec g = {np.round(np.linalg.eigvalsh(g), 4)}  ({nev} tau-slices, quad est {err:.1e}, {time.time()-t0:.0f}s)", flush=True)
    worst = 0
    for lam, v in zip(lams, V):
        d, _ = defect_mp(B, g, lam)
        d = float(d); worst = max(worst, abs(d - v))
        print(f"    lam={lam:+10.4f}: defect = {d:.14e}   V = {v:.14e}   diff = {d - v:+.1e}   rel {abs(d - v)/max(abs(d), 1e-300):.1e}", flush=True)
    return worst


def herm_with_spec(spec, rng):
    U = rand_unitary(len(spec), rng)
    return (U*np.asarray(spec)) @ U.conj().T


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = np.random.default_rng(31415)
    if which in ("all", "lem"):
        lemma56()
    if which in ("all", "t03", "t03a", "t03b"):
        d = np.load('../../common/t03_CM_counterexample_M3.npy')
        B, g, r = decode_t03(d)
        L1 = [-6.0, -2.95, -2.2, 0.0, 0.597, 3.0, 8.5]; L2 = [30.0, 68.405, 68.7, 75.0, 77.4, 80.0]
        lams = L1 + L2 if which in ("all", "t03") else (L1 if which == "t03a" else L2)
        run("t03 (M=3, rank 1; spec PgP = -2.2338, 68.7047)", B, g, lams)
    if which in ("all", "big"):
        B, g = rand_inst(3, 2, 1.0, rng); g = herm_with_spec([-40.0, 3.0, 100.0], rng)
        run("big M=3 r=2 spec(-40,3,100)", B, g, [-41.0, -20.0, 0.0, 2.5, 50.0, 99.0, 104.0])
        B, _ = rand_inst(4, 2, 1.0, rng); g = herm_with_spec([-60.0, -59.5, 12.0, 95.0], rng)
        run("big M=4 r=2 spec(-60,-59.5,12,95)", B, g, [-61.0, -59.7, 0.0, 12.3, 60.0, 94.0])
        B, _ = rand_inst(5, 3, 1.0, rng); g = herm_with_spec([-30.0, 0.0, 0.001, 0.002, 88.0], rng)
        run("big+cluster M=5 r=3 spec(-30,0,.001,.002,88)", B, g, [-29.0, -0.5, 0.0015, 1.0, 87.5])
        B, _ = rand_inst(4, 1, 1.0, rng); g = herm_with_spec([-150.0, 1.0, 2.0, 150.0], rng)
        run("big M=4 r=1 spec(-150,1,2,150)", B, g, [-140.0, 0.0, 1.5, 3.0, 149.0])
    if which in ("all", "m6"):
        B, g = rand_inst(6, 3, 1.0, rng)
        run("M=6 r=3 random (scale 1)", B, g, [-3.0, -1.0, 0.0, 0.7, 2.0, 4.0])
        B, g = rand_inst(6, 2, 8.0, rng)
        run("M=6 r=2 random (scale 8)", B, g, [-20.0, -5.0, 0.0, 6.0, 25.0])
