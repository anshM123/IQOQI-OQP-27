"""
closure_check.py -- exact completeness proof of a facet-class list of L(2,2,d) by adjacency closure.

For each class representative F: all ridges of F (exact DD in the affine hull of F, dd_exact.py), exact rotation of
each ridge to the neighbouring facet F', classification of F' by the G-invariant signature (verified with the
exhaustive G-hash for every NEW signature).  The list is complete iff every neighbour belongs to a listed class
(the dual graph of a polytope is connected).
usage: python closure_check.py d classes_pickle
"""
import sys
import time
import pickle
from fractions import Fraction
import math
import numpy as np
from facet_lib import Scenario, Facet, nullspace_1d
from dd_exact import facets_of_points, affine_coords
from explore_facets import medium_invariant


def rotate(sc, F, ridge):
    """exact neighbour of facet F through the ridge (indices into sc.V)."""
    rows = [list(map(int, sc.V[i])) + [-1] for i in ridge] + [list(map(int, F.f[1:])) + [0]]
    w = nullspace_1d(rows)
    gv, g0 = [int(x) for x in w[:-1]], int(w[-1])
    sF = [g0 - sum(a * int(b) for a, b in zip(gv, sc.V[i])) for i in F.tight]
    if min(sF) < 0:
        gv = [-x for x in gv]; g0 = -g0
    hv = np.array(F.f[1:], dtype=np.int64)
    sh = F.f[0] - sc.V @ hv
    num = sc.V @ np.array(gv, dtype=np.int64) - g0
    best = None
    for i in np.where(sh != 0)[0]:
        r = Fraction(int(num[i]), int(sh[i]))
        if best is None or r > best:
            best = r
    newh = [Fraction(a) + best * int(b) for a, b in zip(gv, F.f[1:])]
    newh0 = Fraction(g0) + best * F.f[0]
    den = 1
    for x in newh + [newh0]:
        den = den * x.denominator // math.gcd(den, x.denominator)
    vec = [int(x * den) for x in [newh0] + newh]
    g = 0
    for x in vec:
        g = math.gcd(g, x)
    return Facet(sc, [x // g for x in vec])


if __name__ == "__main__":
    d = int(sys.argv[1])
    sc = Scenario(d)
    classes = pickle.load(open(sys.argv[2], "rb"))
    reps = [Facet(sc, c["f"]) for c in classes]
    keys = {}
    for j, F in enumerate(reps):
        assert F.slack.min() >= 0 and F.is_facet()
        keys[medium_invariant(F)] = j
    print(f"d={d}: {len(reps)} classes; checking adjacency closure", flush=True)
    complete = True
    t0 = time.time()
    for j, F in enumerate(reps):
        T = [tuple(int(x) for x in sc.V[i]) for i in F.tight]
        Tp, cols = affine_coords(T)
        ridges = facets_of_points(Tp)
        counts = {}
        for (r, tight) in ridges:
            ridge = [F.tight[i] for i in sorted(tight)]
            Fn = rotate(sc, F, ridge)
            if not Fn.is_facet():
                print(f"  class {j}: rotation produced a non-facet (BUG)")
                complete = False
                continue
            k = keys.get(medium_invariant(Fn))
            if k is None:
                complete = False
                print(f"  class {j}: NEIGHBOUR NOT IN LIST: tight {len(Fn.tight)}, f = {Fn.f}")
                k = -1
            counts[k] = counts.get(k, 0) + 1
        print(f"class {j}: {len(F.tight)} vertices, {len(ridges)} ridges; neighbour classes {dict(sorted(counts.items()))}"
              f"  [{time.time() - t0:.0f}s]", flush=True)
    print("COMPLETE (adjacency-closed)" if complete else "NOT closed / errors", flush=True)
