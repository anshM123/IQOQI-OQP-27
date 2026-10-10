"""
adjacency_big.py -- second stage of the exact adjacency decomposition: expand (all ridges, exact rotation, exact
orbit-membership certificates) the class representatives that adjacency_d4.py left unexpanded (too many tight
vertices for the pure-python DD), using the numba DD (dd_numba.py).  Any neighbour outside the listed classes is
reported (and appended, then expanded too).
usage: python adjacency_big.py d adj_in.pkl adj_out.pkl  [class indices to expand; default = all unexpanded]
"""
import sys
import time
import pickle
import numpy as np
from facet_lib import Scenario, Facet, Classifier
from dd_exact import affine_coords
import dd_numba
from closure_check import rotate
from explore_facets import medium_invariant
from adjacency_d4 import find_g

if __name__ == "__main__":
    d = int(sys.argv[1])
    data = pickle.load(open(sys.argv[2], "rb"))
    out_path = sys.argv[3]
    sc = Scenario(d)
    reps = [Facet(sc, f) for f in data["f"]]
    sigs = [medium_invariant(F) for F in reps]
    adjacency = dict(data["adjacency"])
    todo = [int(x) for x in sys.argv[4:]] if len(sys.argv) > 4 else [i for i in range(len(reps)) if i not in adjacency]
    print(f"d={d}: {len(reps)} classes, {len(adjacency)} expanded; to expand now: {todo}", flush=True)
    t0 = time.time()
    cache = {}
    while todo:
        i = todo.pop(0)
        F = reps[i]
        T = [tuple(int(x) for x in sc.V[k]) for k in F.tight]
        Tp, cols = affine_coords(T)
        ridges = dd_numba.facets_of_points(Tp, verbose=True)
        counts = {}
        for (r, tight) in ridges:
            ridge = [F.tight[k] for k in sorted(tight)]
            Fn = rotate(sc, F, ridge)
            # facet property: certified below either by an explicit relabelling onto an (exactly verified) listed
            # representative, or by the exact affine-rank test for a new class
            kb = Fn.slack.tobytes()
            j = cache.get(kb)
            if j is None:
                sg = medium_invariant(Fn)
                S2 = Fn.slack.reshape(d, d, d, d)
                for jj, sj in enumerate(sigs):
                    if sj == sg and find_g(reps[jj].slack.reshape(d, d, d, d), S2, sc) is not None:
                        j = jj
                        break
                if j is None:
                    if not Fn.is_facet():
                        raise RuntimeError("rotation gave a non-facet")
                    reps.append(Fn)
                    sigs.append(sg)
                    j = len(reps) - 1
                    todo.append(j)
                    print(f"  NEW class {j} (neighbour of {i}): tight {len(Fn.tight)}, f = {Fn.f}", flush=True)
                cache[kb] = j
            counts[j] = counts.get(j, 0) + 1
        adjacency[i] = counts
        print(f"class {i}: {len(F.tight)} vertices, {len(ridges)} ridges, neighbours {dict(sorted(counts.items()))}"
              f"  [{time.time() - t0:.0f}s]", flush=True)
        pickle.dump(dict(f=[R.f for R in reps], adjacency=adjacency), open(out_path, "wb"))
    unexp = [i for i in range(len(reps)) if i not in adjacency]
    print(("ADJACENCY-CLOSED" if not unexp else f"still unexpanded: {unexp}") + f": {len(reps)} classes", flush=True)
    cl = Classifier(sc)
    orbits = []
    for j, F in enumerate(reps):
        _, stab = cl.key_and_stab(F)
        orbits.append(sc.group_order() // stab)
    bad = 0
    for a_, cnt in adjacency.items():
        for b_, x in cnt.items():
            if b_ in adjacency and orbits[a_] * x != orbits[b_] * adjacency[b_].get(a_, 0):
                bad += 1
    print(f"orbits {orbits}\nTOTAL FACETS {sum(orbits)}; double-counting violations {bad}", flush=True)
    pickle.dump(dict(f=[R.f for R in reps], adjacency=adjacency, orbits=orbits, total=sum(orbits)),
                open(out_path, "wb"))
