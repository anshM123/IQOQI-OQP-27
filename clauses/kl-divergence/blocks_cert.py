"""
blocks_cert.py -- RIGOROUS lower bounds for the block (direct-sum) competitors on Phi_d (Lemma B, Lemma F of
THEOREM.md), uniform setting distribution sigma = 1/4.

Blocks (each realised by rank-one PVMs on a maximally entangled block Phi_m, m outcomes):
   T1   (m=1): trivial, q = delta_(0,0) for every setting pair;
   C2   (m=2): CHSH, c(a,b|x,y) = (1 + (-1)^(a+b+xy)/sqrt2)/4;
   K3   (m=3): DKZ_3, q(a,b|x,y) = 1/(54 sin^2(pi (b-a-delta_xy)/3));
   CC4  (m=4): CHSH (x) CHSH with shared settings, q((a1,a2),(b1,b2)|xy) = c(a1,b1|xy) c(a2,b2|xy).
For each block: an exact rational test factor r_j (from the numerical optimum, rationalised), scaled by the EXACT
maximum over all m^4 deterministic strategies so that (1/4) sum_xy r_j(a_x, b_y|xy) <= 1 (shrunk by 1e-9);
certified L_j = (1/4) sum q_j log r_j by 50-digit interval arithmetic; R_j^xy = max_ab r_j(a,b|xy) (exact).
Cross conditions (Lemma F): R_j^00 + R_k^11 <= 4 and R_j^01 + R_k^10 <= 4 for all block types j, k (exact).
Competitor for d = 4k + rho (k >= 1, rho in {0,1,2,3}): k blocks CC4 + one block of size rho:
   S^UNI(competitor_d) >= C(d) = (4k L_CC4 + rho L_rho)/d.
usage: python blocks_cert.py [T_bound_bits]
"""
import sys
import itertools
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf

sys.path.insert(0, ".")
from bell22d import kl_strength

iv.dps = 50
LN2 = iv.log(iv.mpf(2))
S2 = iv.sqrt(iv.mpf(2))
DL = {(0, 0): Fr(1, 4), (0, 1): Fr(3, 4), (1, 0): Fr(-1, 4), (1, 1): Fr(1, 4)}


def chsh_iv(a, b, x, y):
    return (1 + (-1) ** ((a + b + x * y) % 2) / S2) / 4


def block(name):
    """returns (m, dict (x,y,a,b) -> iv value)"""
    Q = {}
    if name == "T1":
        for x, y in itertools.product(range(2), repeat=2):
            Q[(x, y, 0, 0)] = iv.mpf(1)
        return 1, Q
    if name == "C2":
        for x, y, a, b in itertools.product(range(2), repeat=4):
            Q[(x, y, a, b)] = chsh_iv(a, b, x, y)
        return 2, Q
    if name == "K3":
        for x, y, a, b in itertools.product(range(2), range(2), range(3), range(3)):
            dl = DL[(x, y)]
            s = iv.sin(iv.pi * ((b - a) - iv.mpf(dl.numerator) / dl.denominator) / 3)
            Q[(x, y, a, b)] = 1 / (54 * s * s)
        return 3, Q
    if name == "CC4":
        for x, y, A, B in itertools.product(range(2), range(2), range(4), range(4)):
            a1, a2, b1, b2 = A >> 1, A & 1, B >> 1, B & 1
            Q[(x, y, A, B)] = chsh_iv(a1, b1, x, y) * chsh_iv(a2, b2, x, y)
        return 4, Q
    raise ValueError(name)


def certify_block(name):
    m, Q = block(name)
    if m == 1:
        R = {k: Fr(1) for k in Q}
    else:
        q = np.zeros((2, 2, m, m))
        for (x, y, a, b), v in Q.items():
            q[x, y, a, b] = float(mpf(v.mid))
        res = kl_strength(q)
        R = {k: Fr(float(q[k] / res["p"][k])).limit_denominator(10 ** 12) for k in Q}
    # exact maximum over all deterministic strategies (a0, a1, b0, b1)
    Mx = max(sum(R[(x, y, lam[x], lam[2 + y])] for x in range(2) for y in range(2)) / 4
             for lam in itertools.product(range(m), repeat=4))
    scale = (1 - Fr(1, 10 ** 9)) / Mx if m > 1 else Fr(1)
    R = {k: v * scale for k, v in R.items()}
    assert all(v > 0 for v in R.values())
    # feasibility re-check (exact)
    Mx2 = max(sum(R[(x, y, lam[x], lam[2 + y])] for x in range(2) for y in range(2)) / 4
              for lam in itertools.product(range(m), repeat=4))
    assert Mx2 <= 1
    L = iv.mpf(0)
    for k, v in Q.items():
        L += v * iv.log(iv.mpf(R[k].numerator) / R[k].denominator) / 4
    Rmax = {(x, y): max(R[(x, y, a, b)] for a in range(m) for b in range(m)) for x in range(2) for y in range(2)}
    return dict(m=m, L=L / LN2, R=R, Rmax=Rmax, Mx2=Mx2)


if __name__ == "__main__":
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 0.068784872742
    B = {}
    for name in ("T1", "C2", "K3", "CC4"):
        B[name] = certify_block(name)
        b = B[name]
        print(f"{name}: certified L >= {float(mpf(b['L'].a)):.12f} bits; exact max test-factor value over strategies "
              f"{float(b['Mx2']):.12f}; R^xy max = " +
              ", ".join(f"{xy}:{float(v):.6f}" for xy, v in b["Rmax"].items()), flush=True)
    # cross conditions (exact)
    ok = True
    for j, k in itertools.product(B, repeat=2):
        Rj, Rk = B[j]["Rmax"], B[k]["Rmax"]
        c1 = Rj[(0, 0)] + Rk[(1, 1)] <= 4
        c2 = Rj[(0, 1)] + Rk[(1, 0)] <= 4
        ok = ok and c1 and c2
    print("cross conditions R_j^00 + R_k^11 <= 4 and R_j^01 + R_k^10 <= 4 for all block pairs:", ok)
    Lr = {0: None, 1: B["T1"]["L"], 2: B["C2"]["L"], 3: B["K3"]["L"]}
    L4 = B["CC4"]["L"]
    worst = None
    for d in range(4, 2001):
        k, rho = divmod(d, 4)
        C = (4 * k * L4 + (rho * Lr[rho] if rho else 0)) / d
        lo = float(mpf(C.a))
        if worst is None or lo < worst[1]:
            worst = (d, lo)
        if d <= 12:
            print(f"  d={d:2d} = 4*{k}+{rho}: competitor >= {lo:.12f} bits  vs DKZ_d <= T = {T:.12f}: "
                  f"margin {lo - T:.6f}", flush=True)
    print(f"min over 4 <= d <= 2000: d={worst[0]}, {worst[1]:.12f} bits (> T: {worst[1] > T})")
    # analytic: for fixed rho, C(4k+rho) = L4 - rho (L4 - L_rho)/(4k+rho) increases with k (L_rho < L4), so
    # min over k >= 1 is at k = 1; check the four residues at k = 1 rigorously:
    for rho in range(4):
        C = (4 * L4 + (rho * Lr[rho] if rho else 0)) / (4 + rho)
        print(f"  residue {rho}: C(4+{rho}) >= {float(mpf(C.a)):.12f} > T: {C.a > T}")
    print("monotonicity premise L_rho < L4:", all(Lr[r].b < L4.a for r in (1, 2, 3)))
    import json
    out = {name: {"m": b["m"], "r": {",".join(map(str, k)): str(v) for k, v in b["R"].items()}} for name, b in B.items()}
    with open("blocks_testfactors.json", "w") as f:
        json.dump(out, f)
    print("exact test factors written to blocks_testfactors.json")
