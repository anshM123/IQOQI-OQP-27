"""Local certificate at a DKZ copy in the Gram-Schmidt (LU) chart  Bt(z) = Btc Q(z),  z = strictly lower part of the
unit lower LU factor of Btc^H Bt (column-phase invariant; inverse map explicit, see nash_core3.z_of_box).
Kernel model anchored at the copy: K(z) = Kc + Mz z (Kc exact KKT kernel, Mz dyadic, zero b-sums on supp Kc), so
g(0) = S0 and grad g(0) = 0 exactly.  Certifies g <= S0 on the cube |z|_inf <= R (star cube + local B&B).
usage: python nash_local_gs.py d f1 f2 R"""
import sys
import time
import json
import numpy as np

import nash_iv as V
from nash_iv import IV
import nash_core as C
import nash_core3 as T3
import nash_copies as P


def copy_basis(cp):
    """rigorous enclosure (re, im) of the copy's basis Btc = CKM(x_c), x_c exact (interval)."""
    B = T3.bt3(cp.x.lo[None], cp.x.hi[None], point=False, order3=False)
    re = IV(np.array([[B[r][c].re.v.lo[0] for c in range(3)] for r in range(3)]),
            np.array([[B[r][c].re.v.hi[0] for c in range(3)] for r in range(3)]))
    im = IV(np.array([[B[r][c].im.v.lo[0] for c in range(3)] for r in range(3)]),
            np.array([[B[r][c].im.v.hi[0] for c in range(3)] for r in range(3)]))
    return re, im


def slope_z(cp, Btc):
    z0 = np.zeros((1, 6))
    qv, qg, _, _ = T3.q3(T3.gs_jets(z0, z0, Btc, order3=False))
    M = C.kernel_slope(qv.mid(), qg.mid(), cp.K.mid()[None], supp_tol=0.0)[0]
    Mz = np.round(M / 2.0 ** -30) * 2.0 ** -30
    Mz = Mz.reshape(9, 3, 6)
    supp = cp.supp.reshape(9, 3)
    Mz[~supp] = 0.0
    for blk in range(9):
        sb = np.nonzero(supp[blk])[0]
        if len(sb):
            Mz[blk, sb[0]] = -(Mz[blk].sum(axis=0) - Mz[blk, sb[0]])
    assert np.all(Mz.sum(axis=1) == 0.0)
    return Mz.reshape(27, 6)


def kernel_at(cp, Mz, cz, hz):
    N = cz.shape[0]
    Kc = IV(np.repeat(cp.K.lo.reshape(1, 27), N, 0), np.repeat(cp.K.hi.reshape(1, 27), N, 0))
    Mi = IV(np.repeat(Mz[None], N, 0))
    Kcen = Kc + V.isum(Mi * IV(cz)[:, None, :], axis=2)
    span = V.isum(Mi * IV(-hz, hz)[:, None, :], axis=2)
    ok = np.all(((Kcen + span).lo >= 0) | ~cp.supp.reshape(1, 27), axis=1)
    return Kcen.reshape(N, 3, 3, 3), ok


def make_chart(Btc):
    return lambda lo, hi, order3: T3.gs_jets(lo, hi, Btc, order3=order3)


def star(cp, Btc, Mz, rho):
    chart = make_chart(Btc)
    z0 = np.zeros((1, 6))
    Kc = IV(cp.K.lo.reshape(1, 3, 3, 3), cp.K.hi.reshape(1, 3, 3, 3))
    _, parts = T3.box_bound3(z0, z0, None, Mz[None], Kint=Kc, return_parts=True, chart=chart)
    H = T3.full_from_packed(parts["H"])
    lam = 0.98 * np.linalg.eigvalsh(-H.mid()[0])[0]
    A = IV(-H.hi, -H.lo)
    dd = np.arange(6)
    A.lo[:, dd, dd] = V.dn(-H.hi[:, dd, dd] - lam)
    A.hi[:, dd, dd] = V.up(-H.lo[:, dd, dd] - lam)
    ok, _ = T3.chol(A)
    chk = (bool(parts["F"].lo[0] <= C.S0.hi and C.S0.lo <= parts["F"].hi[0]), float(parts["G"].mag().max()))
    if not ok[0]:
        return 0.0, lam, np.inf, chk
    lo, hi = -rho * np.ones((1, 6)), rho * np.ones((1, 6))
    Kcen, knn = kernel_at(cp, Mz, np.zeros((1, 6)), rho * np.ones((1, 6)))
    _, p2 = T3.box_bound3(lo, hi, None, Mz[None], Kint=Kcen, return_parts=True, chart=chart)
    if p2["good"][0] < 18 or not knn[0]:
        return 0.0, lam, np.inf, chk
    K3 = float(V.isum(IV(p2["T"].mag()) * IV(T3.MULT / 6.0), axis=1).hi[0])
    return min(rho, 0.999 * lam / (2 * K3)), lam, K3, chk


def local_bb(cp, Btc, Mz, R, r_star, batch=2000, max_boxes=3_000_000, log=print):
    chart = make_chart(Btc)
    S0lo = C.S0.lo
    lo_q = np.array([-R * np.ones(6)])
    hi_q = np.array([R * np.ones(6)])
    done = cert = 0
    t0 = tl = time.time()
    worst = -np.inf
    while lo_q.shape[0]:
        lo, hi = lo_q[-batch:], hi_q[-batch:]
        lo_q, hi_q = lo_q[:-batch], hi_q[:-batch]
        inside = np.all((lo >= -r_star) & (hi <= r_star), axis=1)
        ok = inside.copy()
        todo = np.nonzero(~inside)[0]
        if len(todo):
            c, h = C.box_geometry(lo[todo], hi[todo])
            Kcen, knn = kernel_at(cp, Mz, c, h)
            ub = T3.box_bound3(lo[todo], hi[todo], None, np.repeat(Mz[None], len(todo), 0), Kint=Kcen, chart=chart)
            good = knn & (ub < S0lo)
            ok[todo] = good
            if np.any(good):
                worst = max(worst, float(np.max(ub[good] - S0lo)))
        done += lo.shape[0]
        cert += int(ok.sum())
        bad = np.nonzero(~ok)[0]
        if len(bad):
            l2, h2 = lo[bad], hi[bad]
            w = h2 - l2
            k = np.argmax(w, axis=1)
            r = np.arange(len(bad))
            if np.min(w[r, k]) < 1e-6:
                log("box too small; stopping")
                return False, done, cert
            mid = 0.5 * (l2[r, k] + h2[r, k])
            a_hi = h2.copy()
            a_hi[r, k] = mid
            b_lo = l2.copy()
            b_lo[r, k] = mid
            lo_q = np.concatenate([lo_q, l2, b_lo])
            hi_q = np.concatenate([hi_q, a_hi, h2])
        if done > max_boxes:
            log("too many boxes")
            return False, done, cert
        if time.time() - tl > 60:
            tl = time.time()
            log(f"  processed {done}, certified {cert}, queue {lo_q.shape[0]}, {time.time() - t0:.0f} s")
    log(f"  local B&B done: {done} boxes, {cert} certified leaves, {time.time() - t0:.0f} s; worst ub - S0 = {worst:.3e}")
    return True, done, cert


if __name__ == "__main__":
    key = tuple(int(a) for a in sys.argv[1:4]) if len(sys.argv) > 3 else (6, 4, 14)
    R = float(sys.argv[4]) if len(sys.argv) > 4 else 0.1
    cp = P.Copy(key)
    Btc = copy_basis(cp)
    Mz = slope_z(cp, Btc)
    best = 0.0
    for rho in (0.005, 0.01, 0.02, 0.04, 0.08):
        r, lam, K3, chk = star(cp, Btc, Mz, rho)
        print(f"copy {key}: star rho {rho}: r = {r:.5f} (lam {lam:.4f}, K3 {K3:.3f}); checks {chk}", flush=True)
        best = max(best, r)
    print(f"star radius {best:.5f}; local B&B to R = {R}", flush=True)
    if len(sys.argv) > 5 and sys.argv[5] == "star_only":
        sys.exit(0)
    ok, n, ncert = local_bb(cp, Btc, Mz, R, best, log=lambda *a: print(*a, flush=True))
    print(f"RESULT copy {key}: R = {R}, star {best:.5f}, success {ok}, boxes {n}", flush=True)
