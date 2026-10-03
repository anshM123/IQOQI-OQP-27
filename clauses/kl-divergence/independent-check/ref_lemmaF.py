"""
ref_lemmaF.py -- referee: direct instance check of Lemma F (flagged mixtures).
For d = 4..16 the block test factors of kl-divergence/blocks_testfactors.json are glued into ONE test factor r on the
(2,2,d) scenario (r = r_j on O_j x O_j for every setting pair, 0 on cross-block cells), and its feasibility
  max over all d^4 deterministic strategies of (1/4) sum_xy r(a_x, b_y | xy) <= 1
is checked EXACTLY (Fractions; for fixed (a0, a1) the maximum over b0 and over b1 separate).
This verifies the conclusion of Lemma F instance by instance, without using its proof.
usage: python ref_lemmaF.py [dmax]
"""
import sys
import json
from fractions import Fraction as Fr

TF = json.load(open(r"..\P4_kl\blocks_testfactors.json"))
R = {nm: {tuple(int(u) for u in k.split(",")): Fr(v) for k, v in dat["r"].items()} for nm, dat in TF.items()}
dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
for d in range(4, dmax + 1):
    k, rho = divmod(d, 4)
    names = ["CC4"] * k + ([{1: "T1", 2: "C2", 3: "K3"}[rho]] if rho else [])
    blk = []          # outcome -> (block index, local index, name)
    o = 0
    for j, nm in enumerate(names):
        m = TF[nm]["m"]
        for i in range(m):
            blk.append((j, i, nm))
        o += m
    assert o == d

    def r(x, y, a, b):
        ja, ia, nm = blk[a]
        jb, ib, _ = blk[b]
        return R[nm][(x, y, ia, ib)] if ja == jb else Fr(0)

    best = Fr(0)
    for a0 in range(d):
        for a1 in range(d):
            m0 = max(r(0, 0, a0, b) + r(1, 0, a1, b) for b in range(d))
            m1 = max(r(0, 1, a0, b) + r(1, 1, a1, b) for b in range(d))
            best = max(best, (m0 + m1) / 4)
    print(f"d={d:2d} blocks {names}: exact max over {d**4} strategies of the glued test factor = {float(best):.12f} "
          f"(<= 1: {best <= 1})", flush=True)
    assert best <= 1
