"""
CLOSE_reexpand.py -- independent re-run of the exact expansion of non-positivity facet classes of L(2,2,4).

For each requested class j (representative from adj_d4_small_final.pkl):
  * all ridges of the representative by exact double description (CLOSE_dd_safe: dd_numba's compiled step with
    a certificate that no int64 overflow can occur), with the tight vertices put in a
    seeded RANDOM order (different initial simplex and tie-breaking than the original run, i.e. an independent
    computation path; the resulting ridge set must be the same);
  * exact rotation of every ridge to the neighbouring facet, identification of the neighbour with a listed class
    by an explicit relabelling (find_g; a neighbour matching no class is reported as NEW);
  * the neighbour counts are compared with the saved expansion (adj_d4_small_final.pkl + adj_d4_full.pkl);
  * DD-free cross-check of the positivity neighbours: the number of positivity inequalities p(ab|xy) >= 0 whose
    tight set meets the representative's tight set in affine rank dim-2 (= a ridge) is computed directly by
    exact rank computations and compared with the DD count for the positivity class.
usage: python CLOSE_reexpand.py seed j1 j2 ...
"""
import sys
import time
import pickle
import numpy as np
from facet_lib import Scenario, Facet, affine_rank
from dd_exact import affine_coords
import CLOSE_dd_safe
from closure_check import rotate
from explore_facets import medium_invariant
from adjacency_d4 import find_g


def log(*a):
    print(*a, flush=True)


if __name__ == "__main__":
    seed = int(sys.argv[1])
    todo = [int(x) for x in sys.argv[2:]]
    d = 4
    sc = Scenario(d)
    S = pickle.load(open("adj_d4_small_final.pkl", "rb"))
    Fb = pickle.load(open("adj_d4_full.pkl", "rb"))
    saved = dict(S["adjacency"])
    saved.update(Fb["adjacency"])
    reps = [Facet(sc, f) for f in S["f"]]
    sigs = [medium_invariant(F) for F in reps]
    JPOS = 25
    log(f"CLOSE_reexpand seed {seed}: classes {todo}")
    allok = True
    for j in todo:
        t0 = time.time()
        F = reps[j]
        rng = np.random.default_rng(seed * 1000 + j)
        order = rng.permutation(len(F.tight))
        tight_perm = [int(F.tight[k]) for k in order]
        T = [tuple(int(x) for x in sc.V[k]) for k in tight_perm]
        Tp, _ = affine_coords(T)
        ridges = CLOSE_dd_safe.facets_of_points_safe(Tp, verbose=False)
        maxent = CLOSE_dd_safe.LAST_MAX_ENTRY
        counts = {}
        cache = {}
        new = 0
        for (_, tight) in ridges:
            ridge = sorted(tight_perm[k] for k in tight)
            Fn = rotate(sc, F, ridge)
            kb = Fn.slack.tobytes()
            c = cache.get(kb)
            if c is None:
                sg = medium_invariant(Fn)
                S2 = Fn.slack.reshape(d, d, d, d)
                for jj, sj in enumerate(sigs):
                    if sj == sg and find_g(reps[jj].slack.reshape(d, d, d, d), S2, sc) is not None:
                        c = jj
                        break
                if c is None:
                    c = -1
                    new += 1
                    log(f"  class {j}: NEW neighbour (not in the list): tight {len(Fn.tight)}, f = {Fn.f}")
                cache[kb] = c
            counts[c] = counts.get(c, 0) + 1
        # DD-free count of positivity neighbours
        tset = set(int(i) for i in F.tight)
        npos = 0
        for x in range(2):
            for y in range(2):
                for a in range(d):
                    for b in range(d):
                        Ti = set(np.where(~((sc.lams[:, x] == a) & (sc.lams[:, 2 + y] == b)))[0].tolist())
                        common = sorted(tset & Ti)
                        if len(common) >= sc.dim - 1 and affine_rank(sc.V[common].tolist()) == sc.dim - 2:
                            npos += 1
        same = (counts == saved.get(j))
        posok = (npos == counts.get(JPOS, 0))
        allok &= same and posok and new == 0
        log(f"class {j}: tight {len(F.tight)}, {len(ridges)} ridges, neighbours {dict(sorted(counts.items()))}; "
            f"equal to saved expansion: {same}; positivity neighbours by direct rank test: {npos} "
            f"(DD: {counts.get(JPOS, 0)}, agree: {posok}); new: {new}; max |ray entry| in the DD {maxent} "
            f"(no-overflow bound certified)  [{time.time() - t0:.0f}s]")
    log("ALL REQUESTED CLASSES REPRODUCED" if allok else "MISMATCH")
