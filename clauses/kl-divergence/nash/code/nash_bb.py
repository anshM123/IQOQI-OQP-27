"""Global branch-and-bound for  max_B Phi(A*, B; mu*) <= S0  over Bob's bases (CKM coordinates).

Domain D = [0, pi/2]^3 x [0, pi] x [0, 2pi/3] x [0, 2pi] (complex conjugation and Z = diag(1, w, w^2) reduce the
phases), restricted to R = {|Bt00| >= |Bt01| >= |Bt02|} (column permutations).  A box is
  - discarded if it lies outside R (rigorous),
  - certified if it lies inside one of the local parallelepipeds P_c = {x : |S_c (x - x_c)|_inf <= R_c} certified by
    nash_local.py around the DKZ copies,
  - certified if the second-order box bound (nash_core.box_bound) or, for small boxes, the third-order bound
    (nash_core3.box_bound3) with a per-box linear kernel model is < S0,
  - otherwise bisected.
usage: python nash_bb.py part nparts [max_boxes]"""
import sys
import time
import math
import json
import numpy as np

import nash_iv as V
from nash_iv import IV
import nash_core as C
import nash_core3 as T3

DLO = np.zeros(6)
DHI = V.up(np.array([math.pi / 2, math.pi / 2, math.pi / 2, math.pi, 2 * math.pi / 3, 2 * math.pi]))
H3_MAX = 0.04          # try the third-order bound on boxes with max half-width below this


# translates: Phi is invariant under the Z-shift (f1, f2) -> (f1 + 2pi/3, f2 + 4pi/3) and 2pi periods, and the copy
# (6, 8, 22) = Z-shift of (6, 0, 6), (6, 8, -2) = (6, 8, 22) - 2pi in f2 (bases equal up to Z and periodicity).
LOCAL_SOURCES = {(6, 4, 14): (6, 4, 14), (6, 0, 6): (6, 0, 6), (6, 8, 22): (6, 0, 6), (6, 8, -2): (6, 0, 6)}


def load_locals():
    """certified Gram-Schmidt cubes: list of (Btc (re IV, im IV), R) for every copy near D whose source certificate
    exists (nash_local_gs_<source>.json)."""
    import nash_copies as P
    import nash_local_gs as G
    out = []
    for key, src in LOCAL_SOURCES.items():
        tag = f"{src[0]}_{src[1]}_{src[2]}"
        try:
            with open(f"nash_local_gs_{tag}.json") as f:
                cert = json.load(f)
        except FileNotFoundError:
            continue
        cp = P.Copy(key)
        out.append((G.copy_basis(cp), float(cert["R"]), key))
    return out


def inside_locals(lo, hi, locs):
    """True where every point of the CKM box has Gram-Schmidt coordinates (w.r.t. some certified copy) inside its
    certified cube (rigorous enclosure of z(x) = L(Btc^H Bt(x)) - I, LU pivots bounded away from 0)."""
    N = lo.shape[0]
    res = np.zeros(N, dtype=bool)
    for Btc, R, key in locs:
        Z, ok = T3.z_of_box(lo, hi, Btc)
        res |= ok & np.all((Z.lo >= -R) & (Z.hi <= R), axis=1)
    return res


def kernel_models(lo, hi, iters=300):
    c, h = C.box_geometry(lo, hi)
    qc = C.q_float(C.ckm_float(c))
    K = C.clean_kernel(C.em_kernel(qc, iters=iters))
    cv, cg, _, _ = T3.q3(T3.bt3(c, c, point=True, order3=False))
    M = C.clean_slope(C.kernel_slope(cv.mid(), cg.mid(), K), K, h)
    return K, M


def split(lo, hi, info):
    """bisect each box along the coordinate with the largest estimated contribution h_i (|g_i| + sum_j |H_ij| h_j)."""
    n = lo.shape[0]
    h = 0.5 * (hi - lo)
    g = info["g"].mag() if info is not None else np.ones_like(h)
    if info is not None:
        Hf = np.zeros((n, 6, 6))
        Hm = info["H"].mag()
        Hf[:, C.TI, C.TJ] = Hm
        Hf[:, C.TJ, C.TI] = Hm
        score = h * (g + np.einsum("nij,nj->ni", Hf, h)) + 1e-12 * h
    else:
        score = h
    k = np.argmax(score, axis=1)
    r = np.arange(n)
    mid = 0.5 * (lo[r, k] + hi[r, k])
    a_hi = hi.copy()
    a_hi[r, k] = mid
    b_lo = lo.copy()
    b_lo[r, k] = mid
    return np.concatenate([lo, b_lo]), np.concatenate([a_hi, hi])


def initial_boxes(part, nparts, grid=(4, 4, 4, 6, 4, 12)):
    axes = [np.linspace(DLO[k], DHI[k], grid[k] + 1) for k in range(6)]
    axes = [np.concatenate([a[:-1], [DHI[k]]]) for k, a in enumerate(axes)]
    idx = np.stack(np.meshgrid(*[np.arange(g) for g in grid], indexing="ij"), -1).reshape(-1, 6)
    lo = np.array([[axes[k][i[k]] for k in range(6)] for i in idx])
    hi = np.array([[axes[k][i[k] + 1] for k in range(6)] for i in idx])
    sel = np.arange(lo.shape[0]) % nparts == part
    return lo[sel], hi[sel]


def run(part, nparts, max_boxes=50_000_000, batch=3000, log=print):
    locs = load_locals()
    log(f"part {part}/{nparts}: {len(locs)} local certificates loaded")
    lo_q, hi_q = initial_boxes(part, nparts)
    S0lo = C.S0.lo
    stats = dict(processed=0, outside=0, local=0, cert2=0, cert3=0, split=0)
    leaves = []
    worst = -np.inf
    t0 = time.time()
    tlast = t0
    min_w = np.inf
    while lo_q.shape[0]:
        lo, hi = lo_q[-batch:], hi_q[-batch:]
        lo_q, hi_q = lo_q[:-batch], hi_q[:-batch]
        n = lo.shape[0]
        stats["processed"] += n
        status = np.zeros(n, dtype=int)            # 0 open, 1 outside R, 2 local, 3 cert2, 4 cert3
        out = C.outside_R(lo, hi)
        status[out] = 1
        if locs:
            inl = inside_locals(lo, hi, locs) & (status == 0)
            status[inl] = 2
        todo = np.nonzero(status == 0)[0]
        info = None
        if len(todo):
            K, M = kernel_models(lo[todo], hi[todo])
            ub2, inf2 = C.box_bound(lo[todo], hi[todo], K, M)
            ok2 = ub2 < S0lo
            status[todo[ok2]] = 3
            if np.any(ok2):
                worst = max(worst, float(np.max(ub2[ok2] - S0lo)))
            hmax = np.max(inf2["h"], axis=1)
            try3 = (~ok2) & (hmax < H3_MAX)
            if np.any(try3):
                i3 = np.nonzero(try3)[0]
                ub3 = T3.box_bound3(lo[todo[i3]], hi[todo[i3]], K[i3], M[i3])
                ok3 = ub3 < S0lo
                status[todo[i3[ok3]]] = 4
                if np.any(ok3):
                    worst = max(worst, float(np.max(ub3[ok3] - S0lo)))
            info = dict(g=inf2["g"], H=inf2["H"])
        for s, key in ((1, "outside"), (2, "local"), (3, "cert2"), (4, "cert3")):
            stats[key] += int(np.sum(status == s))
        cert = status > 0
        leaves.append(np.concatenate([lo[cert], hi[cert], status[cert, None].astype(float)], axis=1))
        open_ = np.nonzero(status == 0)[0]
        if len(open_):
            # info rows correspond to todo; map open boxes to their rows in todo
            pos = {int(t): i for i, t in enumerate(todo)}
            rows = np.array([pos[int(o)] for o in open_])
            sub = dict(g=info["g"][rows], H=info["H"][rows])
            w = np.min(np.max(hi[open_] - lo[open_], axis=1))
            min_w = min(min_w, float(w))
            if w < 1e-9:
                log("FAIL: box too small", lo[open_][0].tolist(), hi[open_][0].tolist())
                return False, stats, leaves
            l2, h2 = split(lo[open_], hi[open_], sub)
            stats["split"] += len(open_)
            lo_q = np.concatenate([lo_q, l2])
            hi_q = np.concatenate([hi_q, h2])
        if stats["processed"] > max_boxes:
            log("stopping: max_boxes reached")
            return False, stats, leaves
        if time.time() - tlast > 60:
            tlast = time.time()
            log(f"  {stats}, queue {lo_q.shape[0]}, min width {min_w:.2e}, worst {worst:.2e}, "
                f"{time.time() - t0:.0f} s")
    log(f"DONE part {part}/{nparts}: {stats}, worst certified ub - S0 = {worst:.3e}, {time.time() - t0:.0f} s")
    return True, stats, leaves


if __name__ == "__main__":
    part = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    nparts = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    mb = int(sys.argv[3]) if len(sys.argv) > 3 else 50_000_000
    ok, stats, leaves = run(part, nparts, mb, log=lambda *a: print(*a, flush=True))
    arr = np.concatenate(leaves) if leaves else np.zeros((0, 13))
    np.save(f"nash_bb_leaves_part{part}of{nparts}.npy", arr)
    print("success:", ok, "leaves saved:", arr.shape[0], flush=True)
