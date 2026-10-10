"""
GLOBAL_fam3_exact.py -- exact data for the 3-parameter Fourier-shift family F3 on Phi_3 (Ansh Mishra, Aryan
Senthilkumar, 2026-10-09).  Own code; sympy exact arithmetic in Q(sqrt3).

Family F3.  Alice |a>_x = 3^{-1/2} sum_k w^{k(a + s_x)} |k>, Bob |b>_y = 3^{-1/2} sum_k w^{-k(b + t_y)} |k>
(w = e^{2 pi i/3}, real shifts s_x, t_y).  On Phi_3: q(a,b|x,y) = K(phi_xy + 2 pi (b - a)/3)/3 with
K(psi) = |1 + e^{i psi} + e^{2 i psi}|^2/9 = (3 + 4 cos psi + 2 cos 2 psi)/9 and link phases
phi_xy = -2 pi (s_x - t_y)/3... (sign conventions are irrelevant: the family is parametrised by
z = (phi_00, phi_01, phi_10) in R^3, phi_11 = phi_01 + phi_10 - phi_00, and checked against the state in
GLOBAL_fam3BB.py).  DKZ_3 is z* = (-pi/6, -pi/2, pi/6).
Translations z -> z + (2 pi/3) k (k in Z^3) are outcome relabellings, so [0, 2 pi/3]^3 is a fundamental domain.

This script: (E1) lists the lattice points z in (pi/6) Z^3 cap [0, 2 pi/3)^3 whose four link laws are permutations
of the DKZ level law Q = (2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9); (E2) for each, the level function g(l, m), the reduced
strategies lambda = (alpha, b0, b1) with sum_l g(l, hit_l(lambda)) minimal; a point is a DKZ COPY iff that minimum
is 2 (CGLMP Pi-form) and it is attained by exactly 10 strategies of the 4 + 4 + 2 type pattern; (E3) criticality:
for every level k and coordinate i, sum_{(l,m): g = k} dQ_l(m)/dz_i = 0 exactly; (E4) the KKT model: the type
weights reproduce P*_g = Q_g / r_g on every cell exactly.  Writes GLOBAL_fam3_copies.json.
"""
import json
import itertools
import sympy as sp

S3 = sp.sqrt(3)
QLEV = [2 * (2 + S3) / 9, 2 * (2 - S3) / 9, sp.Rational(1, 9)]
L = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 1, 1)]
TRIP = list(itertools.product(range(3), repeat=3))


def hit(lam):
    al, b0, b1 = lam
    return [b0 % 3, b1 % 3, (b0 - al) % 3, (b1 - al) % 3]


def K(psi):
    return sp.nsimplify(sp.simplify((3 + 4 * sp.cos(psi) + 2 * sp.cos(2 * psi)) / 9))


def dK(psi):
    return sp.simplify((-4 * sp.sin(psi) - 4 * sp.sin(2 * psi)) / 9)


def main():
    out = []
    pts = [p for p in itertools.product(range(4), repeat=3)]            # units pi/6, [0, 2pi/3) = {0,1,2,3} pi/6
    beta = ((16 + 24 * S3) - sp.sqrt(3280 - 960 * S3)) / 54
    r = [1 + beta * (sp.Rational(1, 2) - k) for k in range(3)]
    Pstar = [sp.simplify(QLEV[k] / r[k]) for k in range(3)]
    ncand = 0
    for p in pts:
        z = [sp.pi * c / 6 for c in p]
        phis = [sum(Li[i] * z[i] for i in range(3)) for Li in L]
        Q = [[K(ph + 2 * sp.pi * m / 3) for m in range(3)] for ph in phis]
        lev = []
        ok = True
        for l in range(4):
            row = []
            for m in range(3):
                found = [k for k in range(3) if sp.simplify(Q[l][m] - QLEV[k]) == 0]
                if len(found) != 1:
                    ok = False
                    break
                row.append(found[0])
            if not ok or sorted(row) != [0, 1, 2]:
                ok = False
                break
            lev.append(row)
        if not ok:
            continue
        ncand += 1
        sums = [sum(lev[l][hit(lam)[l]] for l in range(4)) for lam in TRIP]
        mn = min(sums)
        facet = [i for i, s in enumerate(sums) if s == mn]
        if mn != 2 or len(facet) != 10:
            out.append(dict(p=p, copy=False, min_level_sum=mn, n_min=len(facet)))
            continue
        # types
        types = {}
        adj = [{0, 2}, {2, 3}, {3, 1}, {1, 0}]
        for i in facet:
            lv = [lev[l][hit(TRIP[i])[l]] for l in range(4)]
            if 2 in lv:
                t = "A"
            else:
                ones = {l for l in range(4) if lv[l] == 1}
                t = "B" if ones in adj else "C"
            types[i] = t
        cnt = {t: list(types.values()).count(t) for t in "ABC"}
        # (E3) criticality
        crit = True
        for k in range(3):
            for i in range(3):
                s = 0
                for l in range(4):
                    for m in range(3):
                        if lev[l][m] == k:
                            s += L[l][i] * dK(phis[l] + 2 * sp.pi * m / 3)
                if sp.simplify(s) != 0:
                    crit = False
        # (E4) KKT model from the type weights: w_A = P*_2, w_B = P*_1 / 4, w_C = P*_1 / 2
        W = {"A": Pstar[2], "B": Pstar[1] / 4, "C": Pstar[1] / 2}
        kkt = True
        for l in range(4):
            for m in range(3):
                s = sum(W[types[i]] for i in facet if hit(TRIP[i])[l] == m)
                if sp.simplify(s - Pstar[lev[l][m]]) != 0:
                    kkt = False
        # S at the copy: (1/4) sum_l sum_m Q log(Q / P*) = sum_k Q_k log r_k  (exact identity, as every link has
        # each level once)
        out.append(dict(p=p, copy=True, levels=lev, facet=facet, types=[types[i] for i in facet], counts=cnt,
                        critical=crit, kkt=kkt))
    copies = [o for o in out if o["copy"]]
    print(f"lattice points of (pi/6)Z^3 in [0, 2pi/3)^3: {len(pts)}; with four DKZ-type link laws: {ncand}; "
          f"DKZ copies (CGLMP level sum 2 attained by exactly 10 strategies): {len(copies)}")
    for o in out:
        if o["copy"]:
            print(f"  copy at {o['p']} (units pi/6): types {o['counts']}, criticality exact: {o['critical']}, "
                  f"KKT model exact: {o['kkt']}")
        else:
            print(f"  non-copy DKZ-type point {o['p']}: min level sum {o['min_level_sum']} attained {o['n_min']} times")
    assert all(o["critical"] and o["kkt"] and o["counts"] == {"A": 4, "B": 4, "C": 2} for o in copies)
    json.dump(dict(copies=[dict(p=o["p"], levels=o["levels"], facet=o["facet"], types=o["types"]) for o in copies],
                   others=[o for o in out if not o["copy"]]), open("GLOBAL_fam3_copies.json", "w"), default=str)


if __name__ == "__main__":
    main()
