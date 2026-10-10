"""exact check: which listed class of K_d equals (d-1) - Pi_CGLMP on all d^4 deterministic points (up to a positive
factor and the orbit: the class representative itself is tested, and for adjacency-found representatives also every
orbit element under the physical group)."""
import sys, json, itertools
import numpy as np
from kd_check_orbits import lam_list, slack_of_table, generators, orbit
d = int(sys.argv[1]); fn = sys.argv[2]
classes = json.load(open(fn))
lams = lam_list(d); idx = {l: i for i, l in enumerate(lams)}
target = []
for (a0, a1, b0, b1) in lams:
    Pi = (a0 - b0) % d + (b1 - a0) % d + (b0 - a1) % d + (a1 - b1 - 1) % d
    target.append(Pi - (d - 1))          # slack of the CGLMP Pi-form facet: Pi - (d-1) >= 0
import math
g = 0
for v in target: g = math.gcd(g, abs(v))
target = tuple(v // g for v in target)
gens = generators(d)
for ci, cl in enumerate(classes):
    s = slack_of_table(cl["c"], cl["c0"], d, lams)
    O = orbit(s, d, lams, idx, gens)
    print(f"class {ci} (size {cl['size']}, tight {cl['tight']}): orbit size {len(O)}; contains the CGLMP Pi-form facet: {target in O}")
