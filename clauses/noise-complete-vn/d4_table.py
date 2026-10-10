"""
d4_table.py -- assemble the d = 4 class table (type, tight vertices, orbit, beta(u), ratio bounds) from
adj_d4_*.pkl (classes, orbits) and d4_ratios.pkl (bounds) as markdown.
usage: python d4_table.py adj.pkl ratios.pkl
"""
import sys
import pickle
import itertools
import numpy as np
from facet_lib import Scenario, Facet
from core import i_me


def eff_outcomes(F, d):
    S = F.slack.reshape(d, d, d, d)
    eff = []
    for ax in range(4):
        reps = []
        for a in range(d):
            sl = np.take(S, a, axis=ax)
            if not any(np.array_equal(sl, r) for r in reps):
                reps.append(sl)
        eff.append(len(reps))
    return tuple(eff)


if __name__ == "__main__":
    d = 4
    sc = Scenario(d)
    A = pickle.load(open(sys.argv[1], "rb"))
    R = {e["ci"]: e for e in pickle.load(open(sys.argv[2], "rb"))}
    kappa = i_me(d) / 2
    names = {17: "CGLMP_4 (BGP S1)", 18: "BGP S2", 19: "BGP S3", 20: "BGP S4", 21: "BGP S5", 22: "BGP S6",
             23: "BGP S7", 24: "BGP S8", 25: "positivity"}
    print("| # | type | eff. outcomes | tight | orbit | ratio LB | certified ratio UB | margin to kappa_4 |")
    print("|---|---|---|---|---|---|---|---|")
    worst = None
    for j, f in enumerate(A["f"]):
        F = Facet(sc, f)
        eff = eff_outcomes(F, d)
        if j in names:
            typ = names[j]
        elif eff == (2, 2, 2, 2):
            typ = "lifted CHSH"
        elif eff == (3, 3, 3, 3):
            typ = "lifted CGLMP_3"
        elif eff == (4, 4, 4, 4):
            typ = "genuine (new vs BGP)"
        else:
            typ = "lifted from mixed (3/4) scenario"
        e = R.get(j)
        if e is None or e.get("kind") == "trivial":
            lb = ub = "--"
            mg = "trivial" if e is not None else "pending"
        else:
            lb = f"{e['r_lb']:.6f}"
            ub = f"{e['r_ub']:.6f}"
            mg = f"{kappa - e['r_ub']:+.4f}" if j != 17 else "= kappa_4 (theorem)"
            if j != 17 and (worst is None or e['r_ub'] > worst[1]):
                worst = (j, e['r_ub'])
        orb = A.get("orbits", [None] * 34)[j]
        print(f"| {j} | {typ} | {eff} | {len(F.tight)} | {orb} | {lb} | {ub} | {mg} |")
    print(f"\nlargest certified non-CGLMP ratio: class {worst[0]}: {worst[1]:.6f} < kappa_4 = {kappa:.10f}")
