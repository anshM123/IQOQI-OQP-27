"""
check_d4_summary.py -- re-derive the d = 4 conclusions from the saved data (no SDP solving):
  * every class representative is an exact facet (integer slacks >= 0, exact affine rank 47 of the tight set),
    its local bound is attained, beta(u) and beta_L are recomputed exactly;
  * orbit sizes sum to 11 665 992; class-pair double counting over expanded classes;
  * every non-CGLMP class has a certified ratio bound (from d4_ratios.pkl, produced by sdp_tracial.certify)
    strictly below a rigorous rational lower bound of kappa_4;
  * which classes are expanded (adjacency closure) and which are not.
usage: python check_d4_summary.py
"""
import pickle
from fractions import Fraction
import numpy as np
from facet_lib import Scenario, Facet

KAPPA4_LO = Fraction(1448121609, 10 ** 9)      # kappa_4 = I_ME(4)/2 = 1.448121609229354...

if __name__ == "__main__":
    sc = Scenario(4)
    S = pickle.load(open("adj_d4_small_final.pkl", "rb"))
    try:
        Fb = pickle.load(open("adj_d4_full.pkl", "rb"))
        adj = dict(S["adjacency"]); adj.update(Fb["adjacency"])
    except FileNotFoundError:
        adj = dict(S["adjacency"])
    orbits = S["orbits"]
    R = {e["ci"]: e for e in pickle.load(open("d4_ratios.pkl", "rb"))}
    ok = True
    for j, f in enumerate(S["f"]):
        F = Facet(sc, f)
        isf = F.is_facet()
        C, h0 = sc.full_coeffs(F.f)
        bu = Fraction(int(sum(np.array(C, dtype=object).reshape(-1))), 16)
        e = R[j]
        cert = bool(e.get("certified")) and Fraction(e["r_ub"]).limit_denominator(10 ** 12) < KAPPA4_LO
        is_cglmp = (j == 17)
        line_ok = isf and (cert or is_cglmp)
        ok &= line_ok
        print(f"class {j:2d}: facet {isf}, tight {len(F.tight):3d}, orbit {orbits[j]:8d}, beta_L {h0}, beta(u) {str(bu):>7s}, "
              f"ratio UB {e['r_ub']:.7f} {'< kappa_4 (certified)' if cert else ('= kappa_4 (CGLMP theorem)' if is_cglmp else 'NOT certified')}"
              f", expanded {j in adj}")
    print(f"total facets {sum(orbits)} (JZC: 11665992); classes {len(orbits)}")
    bad = sum(1 for i, c in adj.items() for k, a in c.items() if k in adj and orbits[i] * a != orbits[k] * adj[k].get(i, 0))
    print(f"double counting violations among expanded classes: {bad}")
    print(f"unexpanded classes: {[j for j in range(len(orbits)) if j not in adj]}")
    print("ALL PER-CLASS CERTIFICATES OK" if ok else "SOME CLASS NOT CERTIFIED")
