# rf_05: the two configurations where the AUTHOR'S OWN log (Q_2bmv/q03_defect_check.log) shows a mismatch between the
# defect and V(lam) that PROOF.md s.6 does not report:  r3_2big (lam = eP.max() - 0.3: diff 2.46e-3) and c4_2 (diff 5e-8, 1.4e-8).
# Configurations rebuilt here with the same RNG calls as Q_2bmv/q02_hp_checks.py (data only; no code imported from Q_2bmv).
import sys, time
import numpy as np, mpmath as mp
from rf_core import defect_mp, V_lams, crit_values, compressions


def conf_rand(M, r, scale, seed, big=None):
    rng = np.random.default_rng(seed)
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); Q, _ = np.linalg.qr(Z); B = Q[:, :r] @ Q[:, :r].conj().T
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); W, _ = np.linalg.qr(Z)
    ev = rng.normal(size=M)*scale
    if big is not None:
        ev[-1] = big
    g = (W*ev) @ W.conj().T; g = (g + g.conj().T)/2
    return g, (B + B.conj().T)/2


def conf_cluster(M, r, seed, centre=40.0, spread=1e-3, off=3.0):
    rng = np.random.default_rng(seed)
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); Q, _ = np.linalg.qr(Z); B = Q[:, :r] @ Q[:, :r].conj().T
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); W, _ = np.linalg.qr(Z)
    ev = centre + spread*rng.normal(size=M); ev[0] = off
    g = (W*ev) @ W.conj().T; g = (g + g.conj().T)/2
    return g, (B + B.conj().T)/2


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "r3_2big"
    g, B = conf_rand(3, 2, 2.0, 12, big=150.0) if which == "r3_2big" else conf_cluster(4, 2, 15)
    M = g.shape[0]; P = np.eye(M) - B
    eP = np.linalg.eigvalsh(P @ g @ P)
    lams = [float(np.median(np.linalg.eigvalsh(g))), float(eP.max()) - 0.3]
    bb, pp = compressions(B, g)
    print(f"=== {which}: spec g = {np.linalg.eigvalsh(g)}, spec BgB = {bb}, spec PgP = {pp}, ||BgP||^2 = {np.linalg.norm(B@g@P)**2:.6f}")
    print(f"    author's lam values: {lams}")
    t0 = time.time(); stats = {}
    V, err, nev = V_lams(B, g, lams, stats=stats)
    print(f"    V done: {nev} slices, quad est {err:.1e}, capped slices {stats['capped']}, {time.time()-t0:.0f}s", flush=True)
    for lam, v in zip(lams, V):
        d, _ = defect_mp(B, g, lam)
        print(f"    lam={lam:.5f}: defect = {mp.nstr(d, 16)}   V = {v:.14f}   diff = {float(d) - v:+.2e}", flush=True)
