# rf_02b: Theorem 1 stress tests: the t03 configuration (spec g up to 77.4), large |t| (strong cancellation in D),
# large |a|, and M = 6.  Same machinery as rf_02 (own code).
import time
import numpy as np, mpmath as mp
from rf_core import rand_inst, decode_t03
from rf_02_thm1 import lhs_rhs


def report(name, B, g, AT):
    t0 = time.time()
    pred, exact, err, nev = lhs_rhs(B, g, AT)
    rel = np.abs(pred - exact)/np.abs(exact)
    print(f"{name}: max rel.err = {rel.max():.2e} ({nev} tau-slices, {time.time()-t0:.0f}s)", flush=True)
    for (a, t), p, e in zip(AT, pred, exact):
        print(f"     a={a!s:>14} t={t!s:>12}: D/a^2 = {e.real:+.13e}{e.imag:+.13e}i   integral = {p.real:+.13e}{p.imag:+.13e}i"
              f"   rel {abs(p - e)/abs(e):.1e}", flush=True)
    return rel.max()


if __name__ == "__main__":
    worst = 0
    d = np.load('../../common/t03_CM_counterexample_M3.npy'); B, g, r = decode_t03(d)
    AT = [(0.05 + 1.0j, 0.5 - 1.0j), (0.02 - 0.3j, -3.0 + 2.0j), (-0.1 + 0.05j, 7.0j), (0.08, 2.0), (-0.07, -4.0), (0.6j, 25.0)]
    worst = max(worst, report("t03 (M=3, r=1, spec to 77.4)", B, g, AT))
    rng = np.random.default_rng(99)
    B, g = rand_inst(4, 2, 1.0, rng)
    AT = [(0.8 + 0.2j, 30.0), (0.8 + 0.2j, -30.0), (-1.1, 60.0 + 5.0j), (4.0 - 2.0j, 1.0 + 1.0j), (0.3j, -45.0 + 10.0j)]
    worst = max(worst, report("M=4 r=2, large |t|, large |a|", B, g, AT))
    B, g = rand_inst(6, 3, 1.0, rng)
    AT = [(0.7 + 0.3j, 1.1 - 0.4j), (-1.3 + 0.8j, -0.5 + 2.0j), (1.2j, 0.3j), (2.0, -1.5)]
    worst = max(worst, report("M=6 r=3", B, g, AT))
    B, g = rand_inst(6, 1, 3.0, rng)
    worst = max(worst, report("M=6 r=1 (scale 3)", B, g, AT))
    print(f"WORST relative error: {worst:.2e}")
