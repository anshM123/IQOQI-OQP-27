"""certify the max-ent ratio of every non-CGLMP, non-positivity class of K_d (exact dual certificate, arb)."""
import sys, json, time
import numpy as np
import flint
from kd_sdp import certify_class, kappa_arb
d = int(sys.argv[1]); which = [int(a) for a in sys.argv[2].split(",")]
solver = sys.argv[3] if len(sys.argv) > 3 else "SCS"
eps = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-10
classes = json.load(open(f"kd_facets_d{d}.json"))
kap = kappa_arb(d)
print(f"d={d} kappa_d = {kap.str(15)}", flush=True)
for ci in which:
    cl = classes[ci]; c = np.array(cl["c"])
    t0 = time.time()
    sol, ub, rub = certify_class(d, c, eps=eps, solver=solver)
    verdict = "CERTIFIED < kappa_d" if (rub < kap) else ("NOT below kappa_d")
    print(f"  class {ci} c={cl['c']} size {cl['size']} tight {cl['tight']}: float SDP ratio {sol['val']/(-sol['Fu']):.9f};"
          f" certified UB on F-F(u) {ub.str(12)}, ratio UB {rub.str(12)}  -> {verdict}  ({time.time()-t0:.1f}s)", flush=True)
