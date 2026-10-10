"""exact set comparison: naive DD facets (kd_check.naive_facets) vs the IND_dd facets saved by kd_facets.py."""
import sys, time
import numpy as np
from kd_check import naive_facets, kd_points
d = int(sys.argv[1]); tag = sys.argv[2] if len(sys.argv) > 2 else ""
t0 = time.time()
A = set(tuple(int(v) for v in f) for f in naive_facets(kd_points(d)))
B = set(tuple(int(v) for v in f) for f in np.load(f"kd_facets_d{d}{tag}_raw.npy"))
print(f"d={d}: naive DD {len(A)} facets, IND_dd {len(B)} facets, identical sets: {A == B}  [{time.time()-t0:.0f}s]")
