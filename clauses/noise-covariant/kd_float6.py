import json, time, sys
import numpy as np
from kd_sdp import solve
d = int(sys.argv[1]); eps = float(sys.argv[2])
classes = json.load(open(f"kd_facets_d{d}.json"))
kap = (4.0 / (d * (d - 1)) * float(np.sum((d - np.arange(1, d)) / np.cos(np.pi * np.arange(1, d) / (2 * d))))) / 2
for ci, cl in enumerate(classes):
    if cl["tight"] == max(c["tight"] for c in classes) and cl["size"] == 4 * d:   # positivity
        continue
    t0 = time.time()
    sol = solve(d, np.array(cl["c"]), eps=eps)
    print(f"d={d} class {ci} size {cl['size']} tight {cl['tight']}: SDP ratio {sol['val']/(-sol['Fu']):.6f}  (kappa_d {kap:.6f})  "
          f"{sol['nv']} vars {time.time()-t0:.0f}s", flush=True)
