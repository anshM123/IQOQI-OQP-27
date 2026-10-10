"""
GLOBAL_fam3_recheck.py -- re-check of the certificates of Theorem F3 (GLOBAL_NOTES.md Sec. 4):
  uni: GLOBAL_fam3BB_cert.npz  (S^UNI),   cor: GLOBAL_fam3COR_cert.npz  (S^COR, hence S^UC).
  (1) exact tiling: the certified boxes (dyadic centres and half-widths, read as Fractions) are exactly the leaves
      of the bisection tree grown from the 729 root boxes of [0, 9/4]^3 (each internal box split at its first widest
      coordinate), every leaf used once;  hence they cover [0, 9/4]^3, which contains the fundamental domain
      [0, 2 pi/3]^3 of F3 under the translations (2 pi/3) Z^3;
  (2) the local cubes are re-certified (exact copy model, arb Hessian enclosure negative definite) and every
      method-0 box is checked to lie inside one of them;
  (3) every other box: its upper bound is recomputed from the stored model and checked to be < S0 = S(DKZ_3).
usage: python GLOBAL_fam3_recheck.py [uni|cor] [stride]
"""
import sys
import time
from fractions import Fraction
import numpy as np
from flint import arb
import GLOBAL_fam3BB as G


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "uni"
    stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    import os
    import glob
    if mode == "cor" and not os.path.exists("GLOBAL_fam3COR_cert.npz"):
        files = sorted(glob.glob("GLOBAL_fam3COR_cert_part*of*.npz"))      # a run split into disjoint parts
        Ds = [np.load(f) for f in files]
        rows = np.concatenate([d["rows"] for d in Ds])
        models = np.concatenate([d["models"] for d in Ds])
        cubes_rho = Ds[0]["cubes"]
        print(f"[cor] certificate parts: {files}", flush=True)
    else:
        D = np.load("GLOBAL_fam3BB_cert.npz" if mode == "uni" else "GLOBAL_fam3COR_cert.npz")
        rows, models, cubes_rho = D["rows"], D["models"], D["cubes"]
    n = len(rows)
    t0 = time.time()
    # ------------------------------------------------------------------ (1) tiling
    leaves = {}
    for k in range(n):
        key = tuple(Fraction(float(x)) for x in rows[k, :6])
        assert key not in leaves, "duplicate box"
        leaves[key] = k
    used = np.zeros(n, bool)
    eighth = Fraction(1, 8)
    stack = []
    for i0 in range(9):
        for i1 in range(9):
            for i2 in range(9):
                stack.append(((2 * i0 + 1) * eighth, (2 * i1 + 1) * eighth, (2 * i2 + 1) * eighth,
                              eighth, eighth, eighth))
    nodes = 0
    while stack:
        b = stack.pop()
        nodes += 1
        if b in leaves:
            assert not used[leaves[b]]
            used[leaves[b]] = True
            continue
        c = list(b[:3]); h = list(b[3:])
        assert max(h) > Fraction(1, 2 ** 40), "tree too deep: a region is not covered by the certificate"
        i = h.index(max(h))
        h2 = list(h); h2[i] = h[i] / 2
        for s in (-1, 1):
            c2 = list(c); c2[i] = c[i] + s * h2[i]
            stack.append(tuple(c2) + tuple(h2))
    vol = sum(Fraction(float(rows[k, 3])) * Fraction(float(rows[k, 4])) * Fraction(float(rows[k, 5])) * 8
              for k in range(n))
    print(f"[{mode}] (1) tiling: {n} leaves, all used exactly once: {bool(used.all())}; tree nodes {nodes}; total "
          f"volume {vol} = (9/4)^3: {vol == Fraction(9, 4) ** 3}  [{time.time() - t0:.0f}s]", flush=True)
    assert used.all() and vol == Fraction(9, 4) ** 3
    # ------------------------------------------------------------------ (2) cubes
    if mode == "uni":
        copies = G.load_copies()
        certify = lambda cp, r: G.certify_cube(cp, r)[0]
    else:
        import GLOBAL_fam3COR as C
        copies = C.copy_cor_models()
        certify = C.certify_cor_cube
    cubes = []
    for cp, rho in zip(copies, cubes_rho[:, 0]):
        assert certify(cp, float(rho))
        cubes.append(([(cp["z_arb"][i] - float(rho)).upper() for i in range(3)],
                      [(cp["z_arb"][i] + float(rho)).lower() for i in range(3)]))
    print(f"[{mode}] (2) local cubes re-certified: radii {[float(r) for r in cubes_rho[:, 0]]}", flush=True)
    # ------------------------------------------------------------------ (3) bounds
    cnt = {0: 0, 1: 0, 2: 0, 3: 0}
    worst = None
    for k in range(0, n, stride):
        c = rows[k, :3].copy(); h = rows[k, 3:6].copy(); meth = int(rows[k, 6])
        cp_i = int(rows[k, 8])
        if meth == 0:
            ok = any(all((arb(float(c[i])) - arb(float(h[i]))) >= lo[i] and (arb(float(c[i])) + arb(float(h[i]))) <= hi[i]
                         for i in range(3)) for (lo, hi) in cubes)
            assert ok, f"box {k} not inside a cube"
        else:
            w = models[k, :27]
            M = models[k, 27:].reshape(27, 3)
            if mode == "uni":
                ub = (G.copy_taylor_ub(copies[cp_i], c, h) if meth == 1 else
                      (G.box_ub(c, h, w, M) if meth == 2 else G.separable_ub(c, h, w)))
            else:
                ub = (C.copy_cor_ub(copies[cp_i], c, h) if meth == 1 else
                      (C.cor_taylor_ub(c, h, w, M) if meth == 2 else C.cor_separable_ub(c, h, w)))
            assert ub is not None and ub < G.S0, f"box {k}: bound not below S0"
            gap = float((G.S0 - ub).lower())
            worst = gap if worst is None else min(worst, gap)
        cnt[meth] += 1
    print(f"[{mode}] (3) bounds re-checked (stride {stride}): by method {cnt} (0 cube, 1 copy model, 2 Taylor, "
          f"3 separable); smallest gap S0 - UB {worst:.3e} nats  [{time.time() - t0:.0f}s]", flush=True)
    print(f"[{mode}] CERTIFICATE RE-CHECKED" if stride == 1 else f"[{mode}] PARTIAL RE-CHECK PASSED")


if __name__ == "__main__":
    main()
