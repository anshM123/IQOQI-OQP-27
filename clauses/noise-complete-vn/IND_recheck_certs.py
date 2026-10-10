"""
IND_recheck_certs.py -- re-check of the stored expansion certificates logs/IND_cert_class<j>.npz (no double
description is run).  For every listed class j and every stored ridge R of the representative F:
  * R is a subset of the tight set T(F), and R has affine rank 46 (exact, python-flint)  -> R is a ridge of L in F;
  * the ridges are pairwise distinct and their number equals the DD count of logs/IND_expand_results.jsonl;
  * the stored neighbour slack s' equals g.s_rep for the stored explicit relabelling g (exact integer comparison of
    all 256 entries), s' != s_F and s' vanishes on R  -> s' is a facet of L through R other than F, i.e. THE
    neighbour of F across R (a ridge lies in exactly two facets);
  * the neighbour-class counts equal the stored counts.
(Completeness of each ridge list is what the DD provides; this script certifies soundness of what was recorded.)
usage: python IND_recheck_certs.py j1 j2 ...   (default: all classes with a certificate)
"""
import sys
import os
import json
import numpy as np
import flint
from IND_core import Scen
from IND_expand import load_reps


def main():
    sc = Scen(4)
    reps, S = load_reps(sc)
    runs = {}
    for line in open("logs/IND_expand_results.jsonl"):
        r = json.loads(line)
        runs[r["cls"]] = r
    todo = [int(a) for a in sys.argv[1:]] or [j for j in range(34) if os.path.exists(f"logs/IND_cert_class{j}.npz")]
    perms = sc.perms
    allok = True
    for j in todo:
        Dz = np.load(f"logs/IND_cert_class{j}.npz")
        bits, cls, gs, NS = Dz["ridge_bits"], Dz["neighbour_class"], Dz["relabelling"], Dz["neighbour_slack"].astype(np.int64)
        sF = reps[j]
        T = set(np.nonzero(sF == 0)[0].tolist())
        nr = len(bits)
        ok = (nr == runs[j]["ridges"])
        keys = set()
        counts = {}
        for r in range(nr):
            R = [t for t in range(256) if (int(bits[r, t // 64]) >> (t % 64)) & 1]
            keys.add(tuple(R))
            ok &= set(R) <= T
            P = sc.X[R]
            rk = flint.fmpz_mat([[int(x) - int(y) for x, y in zip(row, P[0])] for row in P[1:]]).rank()
            ok &= (rk == sc.dim - 2)
            k = int(cls[r])
            ok &= 0 <= k < 34
            si, i0, i1, i2, i3 = [int(x) for x in gs[r]]
            Tn = np.ascontiguousarray(np.transpose(NS[r].reshape(4, 4, 4, 4), tuple(int(x) for x in sc.sigmas[si])))
            ok &= np.array_equal(Tn[np.ix_(perms[i0], perms[i1], perms[i2], perms[i3])], reps[k].reshape(4, 4, 4, 4))
            ok &= not np.array_equal(NS[r], sF)
            ok &= all(NS[r][t] == 0 for t in R)
            counts[str(k)] = counts.get(str(k), 0) + 1
        ok &= len(keys) == nr
        ok &= {kk: v for kk, v in sorted(counts.items())} == runs[j]["counts"]
        allok &= ok
        print(f"class {j}: {nr} stored ridges re-checked (rank 46, distinct, neighbours = explicit relabellings of listed "
              f"representatives, counts equal): {ok}", flush=True)
    print("ALL STORED EXPANSION CERTIFICATES RE-CHECKED" if allok else "RE-CHECK FAILED")


if __name__ == "__main__":
    main()
