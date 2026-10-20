"""Cross-check of the numba run: re-run a random sample of initial boxes with the independent numpy implementation
(track.box_bound_track, audited in audit_track/AUDIT_TRACK.md; now with the audit fixes and the freeze model).

The two engines share the mathematics, but not the code for jets, rounding or bound assembly. A region passes when
the numpy branch-and-bound certifies all of it (no unresolved boxes).
usage: python crosscheck_numpy.py worker nworkers nsample [seed]"""
import os, sys, json, time, math
import numpy as np
import warnings
warnings.filterwarnings("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".."))
import nash_core as C
import nash_bb as BB
import track as TR
import bb_track as BT

S0LO = C.S0.lo


def numpy_bound(lo, hi):
    """track bound with the freeze model, computed entirely in numpy."""
    c, h, qc, (qv, qg, qH) = TR.jets(lo, hi, order3=True)
    qcf = qc.v.mid()
    qcg = qc.g.mid()
    N = len(lo)
    K = TR.em_face(qcf, iters=400)
    face = TR.safe_face(K, K < 1e-3)
    K = TR.em_face(qcf, K=K, face=face, iters=400)
    K0, ref = TR.exact_kernel(K, face)
    freeze = qcf < 2.0 * np.einsum("nci,ni->nc", np.abs(qcg), h)
    R = TR.tracking_matrix(qcf, K0, face, ref, wK=1.0 / np.maximum(K0.reshape(N, 27), 1e-300), freeze=freeze)
    return TR.box_bound_track(lo, hi, model=(K0, face, ref, R))


def run(idx, locs, hfine=0.06, hcoarse=0.07, hmin=1e-3, cap=400_000):
    lo_q, hi_q = BT.initial(idx)
    fl_q = np.zeros(1, dtype=np.int8)
    st = dict(idx=int(idx), evals=0, cert=0, local=0, outside=0, unresolved=0)
    t0 = time.time()
    while len(lo_q):
        lo, hi, fl = lo_q[-400:], hi_q[-400:], fl_q[-400:]
        lo_q, hi_q, fl_q = lo_q[:-400], hi_q[:-400], fl_q[:-400]
        status = np.zeros(len(lo), dtype=int)
        out = C.outside_R(lo, hi)
        status[out] = 1
        st["outside"] += int(out.sum())
        inl = BB.inside_locals(lo, hi, locs) & (status == 0)
        status[inl] = 2
        st["local"] += int(inl.sum())
        hmax = 0.5 * np.max(hi - lo, axis=1)
        ev = np.nonzero((status == 0) & ((hmax <= hfine) | ((hmax <= hcoarse) & (fl == 0))))[0]
        newfl = fl.copy()
        if len(ev) and st["evals"] < cap:
            st["evals"] += len(ev)
            ub = numpy_bound(lo[ev], hi[ev])
            ok = ub < S0LO
            status[ev[ok]] = 3
            st["cert"] += int(ok.sum())
            newfl[ev[~ok & (hmax[ev] > hfine)]] = 1
        rest = np.nonzero(status == 0)[0]
        if len(rest):
            small = (hmax[rest] < hmin) | (st["evals"] >= cap)
            st["unresolved"] += int(small.sum())
            go = rest[~small]
            if len(go):
                a, b = BT.split(lo[go], hi[go])
                f2 = np.concatenate([newfl[go], newfl[go]])
                lo_q = np.concatenate([lo_q, a]) if len(lo_q) else a
                hi_q = np.concatenate([hi_q, b]) if len(hi_q) else b
                fl_q = np.concatenate([fl_q, f2]) if len(fl_q) else f2
    st["time"] = time.time() - t0
    return st


if __name__ == "__main__":
    w, nw, ns = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 2026
    rng = np.random.default_rng(seed)
    sample = sorted(rng.choice(BT.work_list(), ns, replace=False).tolist())
    here = os.getcwd()
    os.chdir(os.path.join(HERE, ".."))
    locs = BB.load_locals()
    os.chdir(here)
    os.makedirs(os.path.join(HERE, "xcheck"), exist_ok=True)
    for idx in sample[w::nw]:
        fn = os.path.join(HERE, "xcheck", f"x_{idx}.json")
        if os.path.exists(fn):
            continue
        st = run(idx, locs)
        json.dump(st, open(fn, "w"))
        print(json.dumps(st), flush=True)
