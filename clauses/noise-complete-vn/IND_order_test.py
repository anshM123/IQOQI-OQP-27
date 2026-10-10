"""
IND_order_test.py -- insertion-order heuristics for the DD of a class representative (performance only; the
result of the DD does not depend on the order).  Runs each requested order until max_rays is exceeded or the DD
finishes, and prints the ray counts.
usage: python IND_order_test.py j max_rays order1[:seed] order2[:seed] ...
"""
import sys
import time
import numpy as np
from IND_core import Scen, functional_from_slack, affine_rank_exact
from IND_expand import load_reps
import IND_dd

if __name__ == "__main__":
    j = int(sys.argv[1])
    max_rays = int(sys.argv[2])
    sc = Scen(4)
    reps, S = load_reps(sc)
    sF = reps[j]
    T = np.nonzero(sF == 0)[0]
    den, w = functional_from_slack(sc, sF)
    jdrop = [i for i in range(sc.dim) if w[1 + i] != 0][0]
    keepc = [i for i in range(sc.dim) if i != jdrop]
    P = sc.X[:, keepc][T]
    for spec in sys.argv[3:]:
        order, _, sd = spec.partition(":")
        seed = int(sd) if sd else 0
        t0 = time.time()
        R, Z, info = IND_dd.facets_of_points(P, seed=seed, nthreads=4, verbose=True, label=spec, mode="nbhd",
                                             order=order, max_rays=max_rays)
        print(f"== {spec}: {'ABORTED' if R is None else 'DONE'} peak {info['peak']} steps {info['steps']} "
              f"{'' if R is None else len(R)} [{time.time() - t0:.0f}s]", flush=True)
