"""
d3_global.py -- numerical global search for the KL strength over rank-one PVMs on Phi_3 with an UNBIASED entry into
the nonlocal region: (1) Haar-random bases, (2) seesaw maximisation of a random Gaussian Bell functional (random
coefficients on the 36 cells) until the correlation is nonlocal, (3) monotone linearise-and-seesaw KL ascent
(search.kl_ascent), (4) S^COR at the end point (exponentiated-gradient over setting distributions).
usage: python d3_global.py nstarts seed
"""
import sys
import numpy as np
sys.path.insert(0, ".")
from bell22d import probs_pure, maxent, kl_strength, cglmp_I
from search import seesaw, kl_ascent, haar_unitary

LOG2 = np.log(2)
d = 3
S_DKZ = 0.0577830254933


def s_cor(q, iters=200, eta=2.0):
    s = np.full(4, 0.25)
    w = None
    best = -1.0
    for _ in range(iters):
        r = kl_strength(q, sigma=s.reshape(2, 2), w0=w)
        w = r["w"]
        p = r["p"]
        g = np.array([np.sum(np.where(q[x, y] > 0, q[x, y] * np.log(np.maximum(q[x, y], 1e-300) /
                                                                     np.maximum(p[x, y], 1e-300)), 0))
                      for x in range(2) for y in range(2)])
        best = max(best, r["lb"])
        s = s * np.exp(eta * (g - g @ s))
        s /= s.sum()
    return best


if __name__ == "__main__":
    nst, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = np.random.default_rng(seed)
    vals = []
    for st in range(nst):
        for attempt in range(50):
            A = [haar_unitary(d, rng) for _ in range(2)]
            B = [haar_unitary(d, rng) for _ in range(2)]
            psi = maxent(d)
            c = rng.normal(size=(2, 2, d, d))
            psi, A, B = seesaw(c, psi, A, B, rounds=20, inner=10)
            if kl_strength(probs_pure(psi, A, B))["kl"] > 1e-9:
                break
        val, psi, A, B, r = kl_ascent(psi, A, B, maxit=400)
        q = probs_pure(psi, A, B)
        sc = s_cor(q)
        vals.append((val / LOG2, sc / LOG2))
        print(f"start {st:3d} (entry attempts {attempt + 1}): S^UNI = {val / LOG2:.10f}  S^COR >= {sc / LOG2:.10f} bits  "
              f"I_CGLMP = {cglmp_I(q):.6f}", flush=True)
    v = np.array(vals)
    print(f"SUMMARY seed {seed}: {nst} starts; max S^UNI {v[:, 0].max():.10f}, max S^COR {v[:, 1].max():.10f}; "
          f"#S^UNI within 1e-7 of DKZ_3: {np.sum(np.abs(v[:, 0] - S_DKZ) < 1e-7)}; "
          f"#above DKZ_3 + 1e-9: {np.sum(v[:, 0] > S_DKZ + 1e-9)} (UNI), {np.sum(v[:, 1] > S_DKZ + 1e-9)} (COR); "
          f"distinct S^UNI values (6 dp): {np.unique(np.round(v[:, 0], 6))}")
