"""
CLOSE_d4_extras.py -- exact side checks used by Theorems F4 / D4 and Corollary P4 (CLOSE_NOTES.md Sec. 4).

  (1) class 17 IS CGLMP_4: the CGLMP_4 inequality I_4 <= 2 (Collins-Gisin-Linden-Massar-Popescu 2002, weights
      1, 1/3) is built on the deterministic points, its slack tensor is shown to be an exact facet, and an explicit
      relabelling g with g.slack(rep 17) = slack(CGLMP_4) (both divided by the gcd of their entries) is found and
      checked in integers; I_4(u) = 0 and the local bound is 2, so the max-ent ratio of class 17 is I_ME(4)/2 = kappa_4.
  (2) the 34 representatives are pairwise G-inequivalent: distinct G-invariant signatures (medium_invariant), and an
      exhaustive find_g failure for any pair with equal signature.
  (3) the 63 other positivity facets all meet P = {p(00|00) = 0} in a ridge (exact affine rank 46).
  (4) orbit sizes by exhaustive stabiliser counts over G (optional, --orbits) and the counts of Corollary P4.
usage: python CLOSE_d4_extras.py [--orbits]
"""
import sys
import math
import time
import pickle
import itertools
from fractions import Fraction
import numpy as np
from facet_lib import Scenario, Facet, affine_rank, Classifier
from explore_facets import medium_invariant
from adjacency_d4 import find_g


def log(*a):
    print(*a, flush=True)


def cglmp_value(lam, d):
    """CGLMP I_d at a deterministic point (a0, a1, b0, b1) = (A1, A2, B1, B2) of CGLMP."""
    a0, a1, b0, b1 = lam
    I = Fraction(0)
    for k in range(d // 2):
        w = 1 - Fraction(2 * k, d - 1)
        pos = ((a0 - b0) % d == k) + ((b0 - a1) % d == (k + 1) % d) + ((a1 - b1) % d == k) + ((b1 - a0) % d == k)
        neg = ((a0 - b0) % d == (-k - 1) % d) + ((b0 - a1) % d == (-k) % d) + ((a1 - b1) % d == (-k - 1) % d) + \
              ((b1 - a0) % d == (-k - 1) % d)
        I += w * (int(pos) - int(neg))
    return I


def normalised(s):
    g = 0
    for x in s:
        g = math.gcd(g, int(x))
    return (np.array(s, dtype=np.int64) // g)


if __name__ == "__main__":
    t0 = time.time()
    d = 4
    sc = Scenario(d)
    D = pickle.load(open("adj_d4_small_final.pkl", "rb"))
    reps = [Facet(sc, f) for f in D["f"]]
    # (1) CGLMP_4
    vals = [cglmp_value(tuple(int(v) for v in lam), d) for lam in sc.lams]
    assert max(vals) == 2, "local bound of CGLMP_4 must be 2"
    slack = [2 - v for v in vals]
    den = 1
    for x in slack:
        den = den * x.denominator // math.gcd(den, x.denominator)
    s_cg = normalised([int(x * den) for x in slack])
    tight = np.where(s_cg == 0)[0]
    rk = affine_rank(sc.V[tight].tolist())
    s17 = normalised(reps[17].slack)
    g = find_g(s17.reshape(d, d, d, d), s_cg.reshape(d, d, d, d), sc)
    # I_4(u): every probability term equals 1/d, positive and negative terms cancel
    Iu = sum((1 - Fraction(2 * k, d - 1)) * (4 * Fraction(1, d) - 4 * Fraction(1, d)) for k in range(d // 2))
    log(f"(1) CGLMP_4: local bound 2, {len(tight)} tight deterministic points, exact affine rank {rk} "
        f"(facet: {rk == sc.dim - 1}); I_4(u) = {Iu}; explicit relabelling onto class 17: {g is not None}"
        + (f" (axis map {g[0]}, outcome permutations {g[1]}, {g[2]}, {g[3]}, {g[4]})" if g else ""))
    # (2) pairwise inequivalence
    sigs = [medium_invariant(F) for F in reps]
    groups = {}
    for j, sg in enumerate(sigs):
        groups.setdefault(sg, []).append(j)
    same = [v for v in groups.values() if len(v) > 1]
    extra_ok = True
    for grp in same:
        for i, j in itertools.combinations(grp, 2):
            if find_g(reps[i].slack.reshape(d, d, d, d), reps[j].slack.reshape(d, d, d, d), sc) is not None:
                extra_ok = False
                log(f"  classes {i} and {j} are EQUIVALENT")
    log(f"(2) 34 representatives: {len(groups)} distinct G-invariant signatures; groups with equal signature {same}; "
        f"pairwise inequivalent: {extra_ok}")
    # (3) positivity adjacency
    L = sc.lams
    P = set(np.where(~((L[:, 0] == 0) & (L[:, 2] == 0)))[0].tolist())
    nadj = 0
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    if (x, y, a, b) == (0, 0, 0, 0):
                        continue
                    T = sorted(P & set(np.where(~((L[:, x] == a) & (L[:, 2 + y] == b)))[0].tolist()))
                    nadj += int(affine_rank(sc.V[T].tolist()) == sc.dim - 2)
    log(f"(3) positivity facets meeting P = {{p(00|00) = 0}} in a ridge (exact affine rank 46): {nadj} of 63")
    # (4) orbits and Corollary P4
    if "--orbits" in sys.argv:
        cl = Classifier(sc)
        orbits = []
        for j, F in enumerate(reps):
            _, stab = cl.key_and_stab(F)
            orbits.append(sc.group_order() // stab)
        log(f"(4) orbit sizes recomputed (exhaustive stabilisers over |G| = {sc.group_order()}): {orbits}; "
            f"equal to saved: {orbits == D['orbits']}; total {sum(orbits)}")
    else:
        orbits = D["orbits"]
        log(f"(4) orbit sizes (saved, exhaustive stabilisers of the 2026-10-02 run): total {sum(orbits)}")
    adj = dict(D["adjacency"])
    adj.update(pickle.load(open("adj_d4_full.pkl", "rb"))["adjacency"])
    nP = Fraction(0)
    for j in range(34):
        if j == 25:
            continue
        nP += Fraction(orbits[j] * adj[j].get(25, 0), 64)
    log(f"    Corollary P4: facets of a positivity facet = sum_j orbit_j a_(j,25)/64 + {nadj} = {nP} + {nadj} = "
        f"{nP + nadj} (all terms integral: {all((orbits[j] * adj[j].get(25, 0)) % 64 == 0 for j in range(34) if j != 25)})")
    log(f"[{time.time() - t0:.0f}s]")
