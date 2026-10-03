# rf_02: item 8(i) -- Theorem 1 identity  D(a,t)/a^2 = int_0^1 int_R e^{as - t tau} F(s,tau) ds dtau  at complex (a,t),
# M = 3..5, every rank r = 1..M-1.  Inner s-integral: adaptive G7/K15 between the exact branch points of F (rf_core);
# outer tau-integral: scipy quad_vec (adaptive GK21).  D is computed with mpmath expm (30 digits).
import sys, time
import numpy as np, mpmath as mp
from scipy.integrate import quad_vec
from rf_core import rand_inst, adaptive_slice, D_mp

AT = [(0.7 + 0.3j, 1.1 - 0.4j), (-1.3 + 0.8j, -0.5 + 2.0j), (0.4 - 1.5j, 3.0 + 1.0j), (2.0, -1.5),
      (1.2j, 0.3j), (-0.9 - 0.2j, 4.0j), (0.05 + 0.02j, -6.0 + 1.0j)]


def lhs_rhs(B, g, AT, epsrel=1e-11):
    avec = np.array([a for a, _ in AT], dtype=complex); tvec = np.array([t for _, t in AT], dtype=complex)
    n = len(AT)

    def integrand(tau):
        J, _, _ = adaptive_slice(B, g, tau, lambda s: np.exp(np.outer(s, avec)), n, tol=1e-12)
        v = np.exp(-tvec*tau)*J
        return np.concatenate([v.real, v.imag])
    res, err, info = quad_vec(integrand, 0.0, 1.0, epsabs=1e-13, epsrel=epsrel, limit=4000, quadrature='gk21',
                              norm='max', full_output=True)
    pred = res[:n] + 1j*res[n:]
    exact = np.array([complex(D_mp(B, g, a, t)/mp.mpc(a)**2) for a, t in AT])
    return pred, exact, err, info.neval


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    rng = np.random.default_rng(seed)
    cases = [(3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3), (5, 4)]
    worst = 0
    for M, r in cases:
        sc = 1.0 if (M + r) % 2 else 2.5
        B, g = rand_inst(M, r, sc, rng)
        t0 = time.time()
        pred, exact, err, nev = lhs_rhs(B, g, AT)
        rel = np.abs(pred - exact)/np.abs(exact)
        worst = max(worst, rel.max())
        print(f"M={M} r={r} scale={sc}: max rel.err over {len(AT)} complex (a,t) = {rel.max():.2e}  (quad est {err:.1e}, "
              f"{nev} tau-slices, {time.time()-t0:.0f}s)", flush=True)
        for (a, t), p, e in zip(AT, pred, exact):
            print(f"     a={a!s:>14} t={t!s:>12}: D/a^2 = {e.real:+.13e}{e.imag:+.13e}i   int e^(as-t tau)F = "
                  f"{p.real:+.13e}{p.imag:+.13e}i   rel {abs(p - e)/abs(e):.1e}", flush=True)
    print(f"WORST relative error: {worst:.2e}")
