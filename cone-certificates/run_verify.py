"""driver: rigorous verification of CONE_d for a range of d (verify_cone.py), with retries; certificates -> certs/cert_d{d}.json."""
import sys, time, json
import numpy as np
from verify_cone import *
d0, d1 = int(sys.argv[1]), int(sys.argv[2])
q = int(sys.argv[3]) if len(sys.argv) > 3 else 16
for d in range(d0, d1 + 1):
    t0 = time.time(); done = False
    gg = ghat_float_grid(d, q)
    v = np.array([2 / np.sin(np.pi * m / (2 * d)) for m in range(1, d)])
    giv = None
    for attempt in range(4):
        rng = np.random.default_rng(7919 * d + attempt)
        ncols = (40 + 20 * attempt) * d + 50
        out = find_columns(d, q, ncols, rng, gg, v)
        if out is None:
            print(f"d={d}: attempt {attempt}: float LP infeasible with {ncols} columns", flush=True); continue
        nlist, lam_f, tmin = out
        if tmin <= 0:
            print(f"d={d}: attempt {attempt}: no strictly positive solution on the support", flush=True); continue
        if giv is None:
            giv = ghat_grid(d, q)
        ok, msg = verify(d, nlist, lam_f, giv)
        print(f"d={d}: attempt {attempt}: ncols {ncols} support {len(nlist)}  VERIFIED {ok}  {msg}  [{time.time()-t0:.0f}s]", flush=True)
        if ok:
            with open(f"certs/cert_d{d}.json", "w") as fh:
                json.dump(dict(d=d, q=q, cells=[[int(x) for x in n] for n in nlist], lam=[float(x) for x in lam_f], note=msg), fh)
            done = True; break
    if not done:
        print(f"d={d}: NOT VERIFIED", flush=True)
