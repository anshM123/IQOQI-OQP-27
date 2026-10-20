"""Global branch-and-bound for Theorem N with the numba tracking bound (nbjets + nbtrack; repo .venv python).

Domain, symmetries, local cubes and the certification rule are those of bb_track.py (see TRACK_METHOD.md):
D' = [0, pi/2]^3 x [0, pi] x [0, pi/3] x [0, 2 pi], region R, local Gram-Schmidt cubes, certify iff ub < S0.lo.
Evaluation policy: a box is evaluated when its largest half-width is <= HFINE, or once at the coarse level
(largest half-width <= HCOARSE) if no ancestor was evaluated; after a failed coarse evaluation the descendants
are split along their largest side until <= HFINE; after a failed fine evaluation the box is split along the
coordinate with the largest score h_i (|G_i| + sum_j |H_ij| h_j) from the bound.
usage: python bb_nb.py worker nworkers [outdir]"""
import os
os.environ.setdefault("NUMBA_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
import sys, json, time, math
import numpy as np
import warnings
warnings.filterwarnings("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import nbjets as NJ
import nbtrack as NT
sys.path.insert(0, NJ.ROOT)
import nash_core as C
import nash_bb as BB
import bb_track as BT

HFINE = 0.06
HCOARSE = 0.07
HMIN = 1e-3
BATCH = 512
CAP = 3_000_000
S0LO = C.S0.lo
ENGINE = "numba-track-v2.2 (audit 1+2 fixes: DHI up, safe_face, E rounding, sincos radius, NaN guards; freeze model)"


def evaluate(lo, hi):
    c, h, QCl, QCh, QBl, QBh = NJ.q_jets_batch(np.ascontiguousarray(lo), np.ascontiguousarray(hi))
    qcf = 0.5 * (QCl[:, :, 0] + QCh[:, :, 0])
    qcg = 0.5 * (QCl[:, :, 1:7] + QCh[:, :, 1:7])
    K0, face, R = NT.build_model(qcf, 1.0, qcg, h)
    # exactness of the model (insurance, audit 2): stochastic K0 with exact zeros on the face, R on the 2^-30 grid with
    # exact zero b-sums and zero face rows
    assert np.all(K0.reshape(-1, 9, 3).sum(axis=2) == 1.0) and np.all(K0 >= 0) and np.all(K0[face] == 0.0)
    assert np.all(np.round(R / 2.0 ** -30) * 2.0 ** -30 == R)
    assert np.all(R.reshape(-1, 9, 3, 18).sum(axis=2) == 0.0) and np.all(R[face] == 0.0)
    ub, valid, score = NT.track_bound_batch(h, QCl, QCh, QBl, QBh, np.ascontiguousarray(K0),
                                            np.ascontiguousarray(face), np.ascontiguousarray(R), 1e-3)
    return ub, score


def split_along(lo, hi, k):
    r = np.arange(len(lo))
    mid = 0.5 * (lo[r, k] + hi[r, k])
    a_hi = hi.copy()
    a_hi[r, k] = mid
    b_lo = lo.copy()
    b_lo[r, k] = mid
    return np.concatenate([lo, b_lo]), np.concatenate([a_hi, hi])


def run_initial(idx, locs):
    lo_q, hi_q = BT.initial(idx)
    fl_q = np.zeros(1, dtype=np.int8)        # 1: an ancestor was evaluated at the coarse level and failed
    st = dict(idx=int(idx), engine=ENGINE, evals=0, cert=0, outside=0, local=0, worst=-math.inf, unresolved=[],
              hist={}, vol0=float(np.prod(hi_q - lo_q)), vol_out=0.0, vol_local=0.0, vol_cert=0.0, vol_unres=0.0)
    vol = lambda a, b: float(np.sum(np.prod(b - a, axis=1)))
    t0 = time.time()
    while len(lo_q):
        lo, hi, fl = lo_q[-BATCH:], hi_q[-BATCH:], fl_q[-BATCH:]
        lo_q, hi_q, fl_q = lo_q[:-BATCH], hi_q[:-BATCH], fl_q[:-BATCH]
        n = len(lo)
        status = np.zeros(n, dtype=int)
        out = C.outside_R(lo, hi)
        status[out] = 1
        st["outside"] += int(out.sum())
        st["vol_out"] += vol(lo[out], hi[out])
        if locs:
            inl = BB.inside_locals(lo, hi, locs) & (status == 0)
            status[inl] = 2
            st["local"] += int(inl.sum())
            st["vol_local"] += vol(lo[inl], hi[inl])
        hmax = 0.5 * np.max(hi - lo, axis=1)
        do = (status == 0) & ((hmax <= HFINE) | ((hmax <= HCOARSE) & (fl == 0)))
        ev = np.nonzero(do)[0]
        kfine = np.argmax(hi - lo, axis=1)
        newfl = fl.copy()
        if len(ev) and st["evals"] < CAP:
            st["evals"] += len(ev)
            ub, score = evaluate(lo[ev], hi[ev])
            ok = ub < S0LO
            status[ev[ok]] = 3
            st["cert"] += int(ok.sum())
            st["vol_cert"] += vol(lo[ev[ok]], hi[ev[ok]])
            if np.any(ok):
                st["worst"] = max(st["worst"], float(np.max(ub[ok])))
            for hv in np.round(hmax[ev[ok]], 3):
                st["hist"][str(hv)] = st["hist"].get(str(hv), 0) + 1
            bad = ~ok
            coarse_fail = bad & (hmax[ev] > HFINE)
            newfl[ev[coarse_fail]] = 1
            fine_fail = bad & (hmax[ev] <= HFINE)
            sc = score[fine_fail].copy()
            hw = 0.5 * (hi[ev[fine_fail]] - lo[ev[fine_fail]])
            sc = np.where(hw >= 0.25 * np.max(hw, axis=1, keepdims=True), sc, -1.0)   # never split a side < hmax/4
            good_sc = np.all(np.isfinite(sc), axis=1)
            kk = np.where(good_sc, np.argmax(np.where(np.isfinite(sc), sc, -1.0), axis=1), kfine[ev[fine_fail]])
            kfine[ev[fine_fail]] = kk
        rest = np.nonzero(status == 0)[0]
        if len(rest):
            small = hmax[rest] < HMIN
            capped = st["evals"] >= CAP
            for j in rest[small | capped]:
                st["unresolved"].append([lo[j].tolist(), hi[j].tolist()])
                st["vol_unres"] += float(np.prod(hi[j] - lo[j]))
            go = rest[~(small | capped)]
            if len(go):
                a, b = split_along(lo[go], hi[go], kfine[go])
                f2 = np.concatenate([newfl[go], newfl[go]])
                lo_q = np.concatenate([lo_q, a]) if len(lo_q) else a
                hi_q = np.concatenate([hi_q, b]) if len(hi_q) else b
                fl_q = np.concatenate([fl_q, f2]) if len(fl_q) else f2
    st["time"] = time.time() - t0
    return st


if __name__ == "__main__":
    w, nw = int(sys.argv[1]), int(sys.argv[2])
    outdir = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, "bbnb")
    os.makedirs(outdir, exist_ok=True)
    here = os.getcwd()
    os.chdir(NJ.ROOT)
    locs = BB.load_locals()
    os.chdir(here)
    assert len(locs) == 4, f"expected 4 local certificates, got {len(locs)}"
    todo = BT.work_list()[w::nw]
    log = open(os.path.join(outdir, f"worker_{w}.log"), "a")
    log.write(f"worker {w}/{nw}: {len(todo)} initial boxes, {len(locs)} local certificates, engine {ENGINE}\n")
    log.flush()
    for idx in todo:
        fn = os.path.join(outdir, f"box_{idx}.json")
        if os.path.exists(fn):
            continue
        st = run_initial(idx, locs)
        json.dump(st, open(fn + ".tmp", "w"))
        os.replace(fn + ".tmp", fn)
        log.write(f"{time.strftime('%H:%M:%S')} box {idx}: evals {st['evals']} cert {st['cert']} local {st['local']} "
                  f"unresolved {len(st['unresolved'])} worst/S0 {st['worst'] / S0LO:.4f} time {st['time']:.0f}s\n")
        log.flush()
    log.write("done\n")
    log.close()
