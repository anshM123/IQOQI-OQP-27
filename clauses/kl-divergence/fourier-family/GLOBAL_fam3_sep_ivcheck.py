"""
GLOBAL_fam3_sep_ivcheck.py -- independent spot-check (mpmath interval arithmetic, separate code) of the boxes of the
Theorem F3 certificates that were certified by the separable bound (method 3): for a box c +- h and the stored
constant model w (27 reduced weights), F(z) <= (1/4) sum_l sup_{phi in I_l} D(Q(phi) || P_l) (S^UNI), resp.
max_l sup ... (S^COR), with each sup bounded on pieces of the phase interval by convexity of x log(x/P).
usage: python GLOBAL_fam3_sep_ivcheck.py [uni|cor] nsample [seed]
"""
import sys
import itertools
import numpy as np
import mpmath
from mpmath import iv

iv.dps = 30
L = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 1, 1)]
TRIP = list(itertools.product(range(3), repeat=3))


def hit(lam):
    al, b0, b1 = lam
    return [b0 % 3, b1 % 3, (b0 - al) % 3, (b1 - al) % 3]


def xlogx_over_P(lo, hi, logP):
    """sup over x in [lo, hi] (0 <= lo) of x (log x - log P): convex in x, value 0 at x = 0 -> endpoint maximum."""
    vals = []
    for x in (lo, hi):
        if x == 0:
            vals.append(iv.mpf(0))
        else:
            xi = iv.mpf(x)
            vals.append(xi * (iv.log(xi) - logP))
    return max(v.b for v in vals)


def link_sup(c, h, l, P, piece=0.004):
    phc = sum(L[l][i] * mpmath.mpf(float(c[i])) for i in range(3))
    r = sum(abs(L[l][i]) * mpmath.mpf(float(h[i])) for i in range(3))
    n = max(1, int(mpmath.ceil(2 * r / piece)))
    logP = [iv.log(P[m]) for m in range(3)]
    best = None
    for k in range(n):
        J = iv.mpf([phc - r + 2 * r * k / n, phc - r + 2 * r * (k + 1) / n])
        s = mpmath.mpf(0)
        for m in range(3):
            psi = J + 2 * iv.pi * m / 3
            K = (3 + 4 * iv.cos(psi) + 2 * iv.cos(2 * psi)) / 9
            lo = max(K.a, 0)
            hi = min(K.b, 1)
            s += xlogx_over_P(lo, hi, logP[m])
        best = s if best is None or s > best else best
    return best


def main():
    mode = sys.argv[1]
    nsample = int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    import os
    import glob
    if mode == "cor" and not os.path.exists("GLOBAL_fam3COR_cert.npz"):
        Ds = [np.load(f) for f in sorted(glob.glob("GLOBAL_fam3COR_cert_part*of*.npz"))]
        rows = np.concatenate([d["rows"] for d in Ds])
        models = np.concatenate([d["models"] for d in Ds])
    else:
        D = np.load("GLOBAL_fam3BB_cert.npz" if mode == "uni" else "GLOBAL_fam3COR_cert.npz")
        rows, models = D["rows"], D["models"]
    s3 = iv.sqrt(3)
    beta = ((16 + 24 * s3) - iv.sqrt(3280 - 960 * s3)) / 54
    Qlev = [2 * (2 + s3) / 9, 2 * (2 - s3) / 9, iv.mpf(1) / 9]
    S0 = sum(Qlev[k] * iv.log(1 + beta * (iv.mpf(1) / 2 - k)) for k in range(3))
    idx = np.nonzero(rows[:, 6] == 3)[0]
    rng = np.random.default_rng(seed)
    pick = rng.choice(idx, size=min(nsample, len(idx)), replace=False)
    worst = None
    ok = True
    for k in pick:
        c, h, w = rows[k, :3], rows[k, 3:6], models[k, :27]
        wv = [iv.mpf(float(x)) for x in w]
        assert all(x.a >= 0 for x in wv) and sum(wv).b <= 1
        P = [[iv.mpf(0)] * 3 for _ in range(4)]
        for lam in range(27):
            for l in range(4):
                P[l][hit(TRIP[lam])[l]] += wv[lam]
        sups = [link_sup(c, h, l, P[l]) for l in range(4)]
        ub = sum(sups) / 4 if mode == "uni" else max(sups)
        gap = S0.a - ub
        ok &= gap > 0
        worst = gap if worst is None else min(worst, gap)
    print(f"[{mode}] separable boxes re-checked independently: {len(pick)} of {len(idx)} (random sample, seed {seed}); "
          f"all below S0: {ok}; smallest gap {mpmath.nstr(worst, 4)} nats")


if __name__ == "__main__":
    main()
