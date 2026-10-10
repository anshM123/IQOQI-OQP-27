"""
kd_check6.py -- independent check of the K_d facet classification for d >= 6 (where the naive DD of kd_check.py is too
slow): (1) facets of K_d by a DIFFERENT exact DD implementation (P3_full_theory/dd_numba.py, written independently of
IND_dd.py) compared as SETS of primitive slack functions with the IND_dd facets saved by kd_facets.py; (2) the union of
the orbits of the listed class representatives under explicit physical relabellings (kd_check_orbits.py code) equals
that set; (3) the CGLMP-type class equals (d-1) - Pi_CGLMP on all deterministic points.
usage: python kd_check6.py d
"""
import os
import sys
import time
import json
import math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dd_numba import facets_of_points as dd_numba_facets
from kd_check import kd_points
from kd_check_orbits import lam_list, slack_of_ray, slack_of_table, generators, orbit

d = int(sys.argv[1])
lams = lam_list(d)
idx = {l: i for i, l in enumerate(lams)}
t0 = time.time()
P = kd_points(d)
out = dd_numba_facets(P, verbose=True)
A = {slack_of_ray(r, d, lams) for (r, tight) in out}
print(f"(1) dd_numba: {len(A)} facets [{time.time()-t0:.0f}s]", flush=True)
B = {slack_of_ray(tuple(int(v) for v in f), d, lams) for f in np.load(f"kd_facets_d{d}_raw.npy")}
print(f"    IND_dd (saved): {len(B)} facets; identical sets: {A == B}", flush=True)
classes = json.load(open(f"kd_facets_d{d}.json"))
gens = generators(d)
union = set()
for ci, cl in enumerate(classes):
    s = slack_of_table(cl["c"], cl["c0"], d, lams)
    O = orbit(s, d, lams, idx, gens)
    union |= O
    print(f"(2) class {ci}: orbit size {len(O)} (listed {cl['size']}), contained in the dd_numba set: {O <= A}", flush=True)
print(f"    union of orbits == dd_numba facet set: {union == A}  ({len(union)} / {len(A)})")
ok = True
cg = None
for ci, cl in enumerate(classes):
    c = cl["c"]
    good = True
    for (a0, a1, b0, b1) in lams:
        n = ((b0 - a0) % d, (a0 - b1) % d, (a1 - b0) % d, (b1 - a1) % d)
        F = sum(c[i][n[i]] for i in range(4))
        Pi = (a0 - b0) % d + (b1 - a0) % d + (b0 - a1) % d + (a1 - b1 - 1) % d
        if F != -(Pi - (d - 1)):
            good = False
            break
    if good:
        cg = ci
print(f"(3) class equal to (d-1) - Pi_CGLMP on all {d**4} deterministic points: {cg}")
