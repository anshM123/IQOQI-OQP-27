"""Local certificate at a DKZ copy (production): g <= S0 on the Gram-Schmidt cube |z|_inf <= R, with equality only at
z = 0.  Chart Bt(z) = Btc Q(z) (nash_core3.gs_jets / nash_tmbound.gs_bt).
  - star cube |z|_inf <= r_s: Taylor model of g with the copy-anchored kernel K(z) = Kc + Mz z (exact KKT kernel),
    g(0) = S0, grad g(0) = 0 exactly, so g(z) <= S0 - (lam/2)|z|^2 + A3 |z|_inf^3 + K4 |z|_inf^4 < S0;
  - every other box: Taylor-model bound (nash_tmbound.g_bound) with the anchored kernel where it stays >= 0 on the box,
    otherwise a per-box kernel model (EM at the centre, first-order slope, dyadic, exact zero b-sums).
Output: nash_local_gs_<key>.json (certificate summary) and nash_local_gs_<key>_leaves.npy (certified leaves).
usage: python nash_local_gs2.py d f1 f2 R"""
import sys
import json
import time
import numpy as np

import nash_iv as V
from nash_iv import IV
import nash_core as C
import nash_core3 as T3
import nash_tmbound as TB
import nash_copies as P
import nash_local_gs as G


def star_radius(cp, Btc, Mz, rho):
    """certified r (sup norm, z units) with g < S0 on 0 < |z|_inf <= r, using the TM over the cube of radius rho."""
    c = np.zeros((1, 6))
    h = rho * np.ones((1, 6))
    _, knn = G.kernel_at(cp, Mz, c, h)
    if not knn[0]:
        return 0.0, None
    qs = TB.q_tms(TB.gs_bt(c, h, Btc))
    Kc = IV(cp.K.lo.reshape(1, 27), cp.K.hi.reshape(1, 27)).reshape(1, 3, 3, 3)
    p_c, dp = C.p_model(Kc, Mz[None])
    ub, parts = TB.g_bound(qs, p_c, dp, h, return_parts=True)
    if parts is None or not parts["allgood"][0]:
        return 0.0, None
    G0ok = bool(parts["G0"].lo[0] <= C.S0.hi and C.S0.lo <= parts["G0"].hi[0])
    gmax = float(parts["g"].mag().max())
    Hs = T3.full_from_packed(parts["H"])
    lam = 0.98 * np.linalg.eigvalsh(-Hs.mid()[0])[0]
    A = IV(-Hs.hi, -Hs.lo)
    dd = np.arange(6)
    A.lo[:, dd, dd] = V.dn(-Hs.hi[:, dd, dd] - lam)
    A.hi[:, dd, dd] = V.up(-Hs.lo[:, dd, dd] - lam)
    ok, _ = T3.chol(A)
    if not ok[0]:
        return 0.0, None
    A3 = float(parts["cub"][0])
    K4 = float(parts["K"][0])
    # largest r_s in (0, 1] with lam/2 - A3 r_s - K4 r_s^2 > 0 (s-units), rounded down safely
    disc = A3 * A3 + 2.0 * K4 * lam
    rs = (-A3 + np.sqrt(disc)) / (2 * K4) if K4 > 0 else 0.5 * lam / A3
    rs = min(1.0, 0.99 * rs)
    # verify the inequality at rs with interval arithmetic
    chk = (IV(0.5) * IV(lam) - IV(A3) * IV(rs) - IV(K4) * IV(rs) * IV(rs)).lo
    if chk <= 0:
        return 0.0, None
    info = dict(rho=rho, lam_s=lam, A3=A3, K4=K4, rs=rs, G0_contains_S0=G0ok, grad_max=gmax)
    return rs * rho, info


def per_box_kernels(Btc, c, h, chart):
    cv, cg, _, _ = T3.q3(chart(c, c, False))
    q = np.maximum(cv.mid(), 0.0).reshape(-1, 2, 3, 3)
    K = C.clean_kernel(C.em_kernel(q, iters=600))
    M = C.clean_slope(C.kernel_slope(cv.mid(), cg.mid(), K), K, h)
    return K, M


def bound_boxes(cp, Btc, Mz, chart, lo, hi):
    c, h = C.box_geometry(lo, hi)
    N = lo.shape[0]
    Kanc, knn = G.kernel_at(cp, Mz, c, h)
    ub = np.full(N, np.inf)
    qs = TB.q_tms(TB.gs_bt(c, h, Btc))
    if np.any(knn):
        idx = np.nonzero(knn)[0]
        p_c, dp = C.p_model(Kanc[idx], np.repeat(Mz[None], len(idx), 0))
        sub = [TB.T.TM(q.c[idx], q.K[idx]) for q in qs]
        ub[idx] = TB.g_bound(sub, p_c, dp, h[idx])
    need = ub >= C.S0.lo
    if np.any(need):
        idx = np.nonzero(need)[0]
        K, M = per_box_kernels(Btc, c[idx], h[idx], chart)
        p_c, dp = C.p_model(K, M)
        sub = [TB.T.TM(q.c[idx], q.K[idx]) for q in qs]
        ub[idx] = np.minimum(ub[idx], TB.g_bound(sub, p_c, dp, h[idx]))
    return ub


def run(key, R, log, batch=1500, max_boxes=20_000_000):
    cp = P.Copy(key)
    Btc = G.copy_basis(cp)
    Mz = G.slope_z(cp, Btc)
    chart = G.make_chart(Btc)
    best, binfo = 0.0, None
    for rho in (0.003, 0.004, 0.005, 0.006, 0.008):
        r, info = star_radius(cp, Btc, Mz, rho)
        log(f"star rho {rho}: r = {r:.5f} {info}")
        if r > best:
            best, binfo = r, info
    r_s = best
    log(f"copy {key}: star radius {r_s:.5f}; local B&B over |z|_inf <= {R}")
    lo_q = np.array([-R * np.ones(6)])
    hi_q = np.array([R * np.ones(6)])
    leaves = []
    done = 0
    t0 = tl = time.time()
    worst = -np.inf
    while lo_q.shape[0]:
        lo, hi = lo_q[-batch:], hi_q[-batch:]
        lo_q, hi_q = lo_q[:-batch], hi_q[:-batch]
        inside = np.all((lo >= -r_s) & (hi <= r_s), axis=1)
        ok = inside.copy()
        todo = np.nonzero(~inside)[0]
        if len(todo):
            ub = bound_boxes(cp, Btc, Mz, chart, lo[todo], hi[todo])
            good = ub < C.S0.lo
            ok[todo] = good
            if np.any(good):
                worst = max(worst, float(np.max(ub[good] - C.S0.lo)))
        done += lo.shape[0]
        leaves.append(np.concatenate([lo[ok], hi[ok], inside[ok, None].astype(float)], axis=1))
        bad = np.nonzero(~ok)[0]
        if len(bad):
            l2, h2 = lo[bad], hi[bad]
            w = h2 - l2
            k = np.argmax(w, axis=1)
            rr = np.arange(len(bad))
            if np.min(w[rr, k]) < 1e-7:
                log("FAIL: box too small", l2[0].tolist(), h2[0].tolist())
                return False, None
            mid = 0.5 * (l2[rr, k] + h2[rr, k])
            a_hi = h2.copy()
            a_hi[rr, k] = mid
            b_lo = l2.copy()
            b_lo[rr, k] = mid
            lo_q = np.concatenate([lo_q, l2, b_lo])
            hi_q = np.concatenate([hi_q, a_hi, h2])
        if done > max_boxes:
            log("FAIL: too many boxes")
            return False, None
        if time.time() - tl > 120:
            tl = time.time()
            log(f"  processed {done}, queue {lo_q.shape[0]}, {time.time() - t0:.0f} s, worst {worst:.2e}")
    arr = np.concatenate(leaves)
    log(f"DONE copy {key}: {done} boxes processed, {arr.shape[0]} leaves, worst ub - S0 = {worst:.3e}, "
        f"{time.time() - t0:.0f} s")
    xc = dict(lo=cp.x.lo.tolist(), hi=cp.x.hi.tolist())
    return True, dict(key=list(key), R=R, star_radius=r_s, star_info=binfo, processed=done, leaves=int(arr.shape[0]),
                      worst=worst, xc=xc, Btc_re_lo=Btc[0].lo.tolist(), Btc_re_hi=Btc[0].hi.tolist(),
                      Btc_im_lo=Btc[1].lo.tolist(), Btc_im_hi=Btc[1].hi.tolist()), arr


if __name__ == "__main__":
    key = tuple(int(a) for a in sys.argv[1:4])
    R = float(sys.argv[4]) if len(sys.argv) > 4 else 0.1
    tag = f"{key[0]}_{key[1]}_{key[2]}"
    logf = open(f"logs/nash_local_gs_{tag}.log", "a")

    def log(*a):
        s = " ".join(str(x) for x in a)
        print(s, flush=True)
        logf.write(s + "\n")
        logf.flush()
    res = run(key, R, log)
    if res[0]:
        _, summary, arr = res
        with open(f"nash_local_gs_{tag}.json", "w") as f:
            json.dump(summary, f, indent=1, default=float)
        np.save(f"nash_local_gs_{tag}_leaves.npy", arr)
        log("saved certificate")
