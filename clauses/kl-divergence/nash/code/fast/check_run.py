"""Completeness check of a Theorem N run (bb_nb.py output directory).

Checks: every initial box of D' that is not rigorously outside R (bb_track.work_list, with DHI rounded up) has a
result file from the expected engine, with no unresolved boxes, and with certified + outside-R + local-cube volume
equal to the initial box volume (float bookkeeping, relative tolerance 1e-9).  Prints totals and the worst certified
upper bound relative to S0.
usage: python check_run.py [outdir]"""
import os, sys, json, glob
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".."))
import nash_core as C
import bb_track as BT

outdir = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "bbnb")
todo = BT.work_list()
missing, unresolved, badvol, badeng = [], [], [], []
REQUIRED_ENGINE = "numba-track-v2.2"
engines = {}
tot = dict(evals=0, cert=0, outside=0, local=0)
worst = -np.inf
for idx in todo:
    fn = os.path.join(outdir, f"box_{idx}.json")
    if not os.path.exists(fn):
        missing.append(idx)
        continue
    d = json.load(open(fn))
    if not d.get("engine", "").startswith(REQUIRED_ENGINE):
        badeng.append(idx)
    engines[d.get("engine", "?")] = engines.get(d.get("engine", "?"), 0) + 1
    if d["unresolved"]:
        unresolved.append((idx, len(d["unresolved"])))
    lo, hi = BT.initial(idx)
    v0 = float(np.prod(hi - lo))
    vs = d["vol_cert"] + d["vol_out"] + d["vol_local"]
    if abs(vs - v0) > 1e-9 * v0:
        badvol.append((idx, vs / v0))
    for k in tot:
        tot[k] += d[k]
    worst = max(worst, d["worst"])
print(f"initial boxes to cover: {len(todo)} (of {int(np.prod(BT.GRID))}; the rest are rigorously outside R)")
print(f"missing: {len(missing)}  unresolved: {len(unresolved)}  volume mismatch: {len(badvol)}  wrong engine: {len(badeng)}")
print(f"totals: {tot}; worst certified ub / S0.lo = {worst / C.S0.lo:.6f}; min margin S0.lo - ub = {C.S0.lo - worst:.3e}")
print("engines:", engines)
if missing[:10]:
    print("first missing:", missing[:10])
if unresolved[:10]:
    print("first unresolved:", unresolved[:10])
if badvol[:10]:
    print("first volume mismatches:", badvol[:10])
ok = not (missing or unresolved or badvol or badeng)
print("COMPLETE" if ok else "INCOMPLETE")
