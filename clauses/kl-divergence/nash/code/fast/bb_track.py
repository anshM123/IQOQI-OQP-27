"""Global branch-and-bound for Theorem N (max_B Phi(A*, B; mu*) <= S0) with the tracking bound (track.py).

Domain D' = [0, pi/2]^3 x [0, pi] x [0, pi/3] x [0, 2 pi] in CKM coordinates (theta12, theta13, theta23, delta, f1, f2).
Coverage: every Bob basis is equivalent to one in D' under the symmetries of Phi(A*, .; mu*):
  complex conjugation (delta -> -delta; used for delta in [0, pi]) and left multiplication by D = diag(e^{i pi k/3})
  ((f1, f2) -> (f1 + pi/3, f2 + 2 pi/3); used for f1 in [0, pi/3]); column permutations (region R, outside_R).
A box is
  - discarded if it lies outside R (nash_core.outside_R),
  - certified if it lies inside a certified local Gram-Schmidt cube around a DKZ copy (nash_bb.inside_locals),
  - certified if track.box_bound_track < S0.lo (evaluated once the largest half-width is <= HEVAL),
  - otherwise bisected along its largest side; boxes below HMIN, or beyond the evaluation cap, are saved unresolved.
usage: python bb_track.py worker nworkers [outdir]"""
import sys, os, json, time, math
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import warnings
warnings.filterwarnings("ignore")
import nash_core as C
import nash_bb as BB
import track as TR

import nash_iv as _V
DHI = _V.up(np.array([math.pi / 2, math.pi / 2, math.pi / 2, math.pi, math.pi / 3, 2 * math.pi]))   # >= the true endpoints
GRID = (4, 4, 4, 6, 2, 12)
HEVAL = 0.06
HMIN = 1e-3
BATCH = 400
CAP = 2_000_000
S0LO = C.S0.lo


def initial(idx):
    axes = [np.linspace(0, DHI[k], GRID[k] + 1) for k in range(6)]
    for k in range(6):
        axes[k][-1] = DHI[k]
    ii = np.unravel_index(idx, GRID)
    lo = np.array([axes[k][ii[k]] for k in range(6)])
    hi = np.array([axes[k][ii[k] + 1] for k in range(6)])
    return lo[None], hi[None]


def split(lo, hi):
    k = np.argmax(hi - lo, axis=1)
    r = np.arange(len(lo))
    mid = 0.5 * (lo[r, k] + hi[r, k])
    a_hi = hi.copy()
    a_hi[r, k] = mid
    b_lo = lo.copy()
    b_lo[r, k] = mid
    return np.concatenate([lo, b_lo]), np.concatenate([a_hi, hi])


def run_initial(idx, locs):
    lo_q, hi_q = initial(idx)
    st = dict(idx=int(idx), evals=0, cert=0, outside=0, local=0, worst=-math.inf, unresolved=[], hist={})
    t0 = time.time()
    while len(lo_q):
        lo, hi = lo_q[-BATCH:], hi_q[-BATCH:]
        lo_q, hi_q = lo_q[:-BATCH], hi_q[:-BATCH]
        n = len(lo)
        status = np.zeros(n, dtype=int)
        out = C.outside_R(lo, hi)
        status[out] = 1
        st["outside"] += int(out.sum())
        if locs:
            inl = BB.inside_locals(lo, hi, locs) & (status == 0)
            status[inl] = 2
            st["local"] += int(inl.sum())
        hmax = 0.5 * np.max(hi - lo, axis=1)
        ev = np.nonzero((status == 0) & (hmax <= HEVAL))[0]
        if len(ev) and st["evals"] < CAP:
            st["evals"] += len(ev)
            ub = TR.box_bound_track(lo[ev], hi[ev], beta0=1.0, rounds=1)
            ok = ub < S0LO
            status[ev[ok]] = 3
            st["cert"] += int(ok.sum())
            if np.any(ok):
                st["worst"] = max(st["worst"], float(np.max(ub[ok])))
            for hv in np.round(hmax[ev[ok]], 3):
                st["hist"][str(hv)] = st["hist"].get(str(hv), 0) + 1
        rest = np.nonzero(status == 0)[0]
        if len(rest):
            small = hmax[rest] < HMIN
            capped = st["evals"] >= CAP
            for j in rest[small | capped]:
                st["unresolved"].append([lo[j].tolist(), hi[j].tolist()])
            go = rest[~(small | capped)]
            if len(go):
                a, b = split(lo[go], hi[go])
                lo_q = np.concatenate([lo_q, a]) if len(lo_q) else a
                hi_q = np.concatenate([hi_q, b]) if len(hi_q) else b
    st["time"] = time.time() - t0
    return st


def work_list():
    los, his = [], []
    for i in range(int(np.prod(GRID))):
        lo, hi = initial(i)
        los.append(lo[0])
        his.append(hi[0])
    out = C.outside_R(np.array(los), np.array(his))
    return [i for i in range(len(out)) if not out[i]]


if __name__ == "__main__":
    w, nw = int(sys.argv[1]), int(sys.argv[2])
    outdir = sys.argv[3] if len(sys.argv) > 3 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "bbrun")
    os.makedirs(outdir, exist_ok=True)
    here = os.getcwd()
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))   # local certificate files live in ROOT
    locs = BB.load_locals()
    os.chdir(here)
    assert len(locs) == 4, f"expected 4 local certificates, got {len(locs)}"
    todo = work_list()[w::nw]
    log = open(os.path.join(outdir, f"worker_{w}.log"), "a")
    log.write(f"worker {w}/{nw}: {len(todo)} initial boxes, {len(locs)} local certificates\n")
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
