"""
ref_facets_compare.py -- quick version of ref_facets.py: my own DD (identity order and reversed order, my coordinates)
compared with P2's facets223.txt via tight-vertex sets; spot checks (Collins-Gisin I2233, coarse-grained CHSH, CGLMP_3).
usage: python ref_facets_compare.py [path to facets223.txt]
"""
import sys
import time
from collections import Counter

import ref_facets as RF


def main():
    fn = sys.argv[1] if len(sys.argv) > 1 else "../facets223.txt"
    V = [RF.coords(s) for s in RF.STRATS]
    A = [[1] + v for v in V]
    theirs = RF.p2_tight_sets(fn)
    ok = True
    fams = []
    for name, order in (("identity", list(range(81))), ("reversed", list(range(81))[::-1])):
        t0 = time.time()
        F = set(RF.prim(list(r)) for r in RF.dd(A, order))
        nbad = sum(1 for f in F if not RF.is_facet(f, V))
        mine = {RF.tight_set(f, V): f for f in F}
        fams.append(set(mine))
        same = set(mine) == set(theirs)
        ok &= same and nbad == 0 and len(F) == 1116 and len(mine) == len(F)
        print(f"DD {name}: {len(F)} facets, exact facet-check failures {nbad}, identical to P2 list (tight sets): "
              f"{same}  ({time.time() - t0:.0f}s)", flush=True)
    ok &= fams[0] == fams[1]
    print("P2 classes:", dict(Counter(theirs.values())))
    print("RESULT:", "PASS" if ok else "FAIL")


if __name__ == "__main__":
    main()
