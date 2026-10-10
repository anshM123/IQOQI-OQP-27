"""
IND_posridges.py -- DD-free cross-check of part of hypothesis (i): for every non-positivity class representative F,
the number of positivity facets P_i adjacent to F (F cap P_i a ridge: exact affine rank 46 of the common tight set,
python-flint) is compared with the number of positivity neighbours found by the independent DD (IND_expand.py,
logs/IND_expand_results.jsonl, class 25).  Own code only.
"""
import json
import numpy as np
from IND_core import Scen, affine_rank_exact
from IND_expand import load_reps

if __name__ == "__main__":
    sc = Scen(4)
    reps, S = load_reps(sc)
    runs = {}
    for line in open("logs/IND_expand_results.jsonl"):
        r = json.loads(line)
        runs[r["cls"]] = r
    ok = True
    for j, s in enumerate(reps):
        if j == 25:
            continue
        T = set(np.nonzero(s == 0)[0].tolist())
        cnt = 0
        for x in range(2):
            for y in range(2):
                for a in range(4):
                    for b in range(4):
                        Ti = [k for k in T if not (sc.lams[k][x] == a and sc.lams[k][2 + y] == b)]
                        if len(Ti) >= sc.dim - 1 and affine_rank_exact(sc.X[Ti].tolist()) == sc.dim - 2:
                            cnt += 1
        dd = runs[j]["counts"].get("25") if j in runs else None
        ok &= (dd is not None and dd == cnt)
        print(f"class {j:2d}: positivity facets adjacent (direct rank test) {cnt}; DD positivity neighbours {dd}; "
              f"agree {dd == cnt}", flush=True)
    print("ALL AGREE" if ok else "DISAGREEMENT OR MISSING DD RESULT")
