"""
d4_ratios.py -- for every facet class of L(2,2,4) found by explore2.py: max-ent ratio
      R(beta) = (beta_ME - beta(u)) / (beta_L - beta(u)),   beta_ME = sup over max-ent behaviours with uniform
marginals (rank-one PVMs on Phi_4, or balanced PVMs on any Phi_D),
with a LOWER bound (Riemannian ascent over rank-one PVMs on Phi_4, several starts) and a certified UPPER bound
(tracial level-2 SDP, SCS, rigorous dual certificate: sdp_tracial.TracialSDP.certify).
The white-noise clause on this facet class holds iff R(beta) <= kappa_4 = I_ME(4)/2 = 1.4481216092...
usage: python d4_ratios.py classes_pickle [start_index] [eps] [max_iters] [out.pkl]
Output: one line per class + d4_ratios.pkl
"""
import sys
import time
import pickle
from fractions import Fraction
import numpy as np
from facet_lib import Scenario, Facet
from sdp_tracial import TracialSDP, objective_from_full
from maxent_opt import maximise
from core import i_me

if __name__ == "__main__":
    path = sys.argv[1]
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    eps = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-7
    maxit = int(sys.argv[4]) if len(sys.argv) > 4 else 60000
    outp = sys.argv[5] if len(sys.argv) > 5 else "d4_ratios.pkl"
    d = 4
    kappa = i_me(d) / 2
    sc = Scenario(d)
    classes = pickle.load(open(path, "rb"))
    if isinstance(classes, dict):
        classes = [dict(f=f, orbit=(classes.get("orbits") or [None] * len(classes["f"]))[k])
                   for k, f in enumerate(classes["f"])]
    S = TracialSDP(d, level=2)
    out = []
    try:
        out = pickle.load(open(outp, "rb")) if start > 0 else []
    except FileNotFoundError:
        out = []
    for ci, cl in enumerate(classes):
        if ci < start:
            continue
        F = Facet(sc, cl["f"])
        C, h0 = sc.full_coeffs(F.f)
        Cint = np.array(C, dtype=object)
        bu = Fraction(int(sum(Cint.reshape(-1))), d * d)
        gap = Fraction(h0) - bu
        if gap <= 0:
            print(f"class {ci}: degenerate (beta_L <= beta(u)) -- positivity-type, skipped", flush=True)
            out.append(dict(ci=ci, kind="trivial"))
            continue
        t0 = time.time()
        lb, U = maximise(np.array(C, dtype=float), d, nstart=16, seed=ci)
        r_lb = (lb - float(bu)) / float(gap)
        t1 = time.time()
        hd = objective_from_full(Cint, d)
        val, tt, Zr, st = S.solve(hd, eps=eps, max_iters=maxit)
        ok, ub, info = S.certify(hd, Zr, delta=1e-9)
        r_sdp = (val - float(bu)) / float(gap)
        r_ub = (ub - float(bu)) / float(gap) if ok else float('nan')
        verdict = "OK (< kappa_4)" if ok and r_ub < kappa else ("CGLMP-level" if abs(r_lb - kappa) < 1e-6 else "OPEN")
        print(f"class {ci:3d}: tight {len(F.tight):4d}, orbit {cl.get('orbit', '?')}, beta(u) = {bu}, beta_L = {h0}; "
              f"ratio LB {r_lb:.8f} | SDP {r_sdp:.8f} ({st}) | certified UB {r_ub:.8f}  [kappa_4 = {kappa:.8f}] "
              f"-> {verdict}  ({t1 - t0:.0f}s + {time.time() - t1:.0f}s)", flush=True)
        out.append(dict(ci=ci, f=F.f, tight=len(F.tight), orbit=cl.get('orbit'), bu=bu, bL=h0, r_lb=r_lb,
                        r_sdp=r_sdp, r_ub=r_ub, certified=ok, info=info, status=st, U=U))
        pickle.dump(out, open(outp, "wb"))
