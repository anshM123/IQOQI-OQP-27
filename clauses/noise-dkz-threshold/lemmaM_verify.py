"""
lemmaM_verify.py -- RIGOROUS (python-flint arb) verification of the explicit Lemma M construction for 3 <= d <= dmax.

Construction (NOTES.md Sec. 5): S = d-1, L = floor((S-1)/2), Q(n) = G(n)/kappa + (1-1/kappa)/d,
D(z) = Q(z) - Q(S-z).  Regulariser: weight eta' on every interior cell (x1,x2 >= 1) with x1 + x2 <= S-L-1, so that
F_eta(z) = eta' [max(0, S-L-1-z) - (z-1)/2 * 1{2 <= z <= S-L-1}]  (z <= L),  m_eta(x) = eta' max(0, S-L-1-x).
Families y = 1..L: weight w_y on every cell (t, S-y-t), t = 1..S-y-1, with
      w_z = 2 (Dt(z) - T(z)) / (S - z + 1),  T(z) = sum_{y>z} w_y,  Dt = D - F_eta,  z = L, ..., 1.
Core marginal m_I(x) = sum_{y <= min(L, S-1-x)} w_y + m_eta(x).
Positivity conditions checked here (all other properties are algebraic identities):
  (P1) Dt(z) - T(z) > 0 for z = 1..L;  (P2) Q(x) - m_I(x) > 0 for x = 1..S-1;  (P3) 2 Q(0) - 1 > 0.
Also checked: the mean identity sum_n n Q(n) = S/4 (ball contains S/4).  eta' = D(L)/(100 S) (any eta' > 0 for which
the checks pass is admissible).
"""
import sys
import time
import flint
from flint import arb

flint.ctx.prec = 120


def verify(d):
    S = d - 1
    L = (S - 1) // 2
    pi = arb.pi()
    # kappa = I_ME(d)/2
    # kappa_d := I(DKZ_d)/2 = 2 - 4 E_G[n]/(d-1)  (definition; makes the mean identity E_Q[n] = S/4 exact)
    G = []
    for n in range(d):
        sn = (pi * (4 * n + 1) / (4 * d)).sin()
        G.append(1 / (2 * d * d * sn * sn))
    EG = sum((G[n] * n for n in range(d)), arb(0))
    kap = 2 - 4 * EG / (d - 1)
    # consistency with the closed form of I_ME(d)/2 (not used in the proof)
    s = arb(0)
    for j in range(1, d):
        s += arb(d - j) / (pi * j / (2 * d)).cos()
    kap_closed = s * 2 / (d * (d - 1))
    assert (kap - kap_closed).contains(0) or abs((kap - kap_closed).mid()) < 1e-25
    c = (1 - 1 / kap) / d
    Q = [G[n] / kap + c for n in range(d)]
    mean = sum((Q[n] * n for n in range(d)), arb(0))
    mean_ok = (mean - arb(S) / 4).contains(0)
    p3 = (2 * Q[0] - 1) > 0
    if L == 0:
        # no interior: only the completion; (P2) with m_I = 0
        p2 = all(Q[x] > 0 for x in range(1, S))
        return dict(d=d, mean_ok=mean_ok, p1=True, p2=p2, p3=p3, min_p1=None, min_p2=None)
    D = [None] + [Q[z] - Q[S - z] for z in range(1, L + 1)]
    etap = D[L] / (100 * S)
    etap = arb(etap.mid()) if etap.mid() > 0 else None
    if etap is None or not (etap > 0):
        return dict(d=d, mean_ok=mean_ok, p1=False, p2=False, p3=p3, min_p1=None, min_p2=None)
    M = S - L - 1

    def F_eta(z):
        v = max(0, M - z)
        if 2 <= z <= M:
            return etap * (arb(v) - arb(z - 1) / 2)
        return etap * v

    w = [arb(0)] * (L + 2)
    T = arb(0)
    p1 = True
    min_p1 = None
    for z in range(L, 0, -1):
        Dt = D[z] - F_eta(z)
        g = Dt - T
        if not (g > 0):
            p1 = False
        r = (g / Dt)
        min_p1 = r if min_p1 is None else (r if r.mid() < min_p1.mid() else min_p1)
        w[z] = 2 * g / (S - z + 1)
        T = T + w[z]
    # prefix sums W(k) = sum_{y=1}^k w_y
    W = [arb(0)] * (L + 1)
    for k in range(1, L + 1):
        W[k] = W[k - 1] + w[k]
    p2 = True
    min_p2 = None
    for x in range(1, S):
        k = min(L, S - 1 - x)
        mI = (W[k] if k >= 1 else arb(0)) + etap * max(0, M - x)
        rho = Q[x] - mI
        if not (rho > 0):
            p2 = False
        r = rho / Q[x]
        min_p2 = r if min_p2 is None else (r if r.mid() < min_p2.mid() else min_p2)
    return dict(d=d, mean_ok=mean_ok, p1=p1, p2=p2, p3=p3, min_p1=min_p1, min_p2=min_p2)


if __name__ == "__main__":
    d0, d1 = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    bad = []
    worst1 = worst2 = None
    for d in range(d0, d1 + 1):
        r = verify(d)
        ok = r["mean_ok"] and r["p1"] and r["p2"] and r["p3"]
        if not ok:
            bad.append(d)
            print("FAIL", r, flush=True)
        if r["min_p1"] is not None and (worst1 is None or r["min_p1"].mid() < worst1[1].mid()):
            worst1 = (d, r["min_p1"])
        if r["min_p2"] is not None and (worst2 is None or r["min_p2"].mid() < worst2[1].mid()):
            worst2 = (d, r["min_p2"])
        if d % 100 == 0 or d == d1:
            print(f"  ... d <= {d}: failures so far {bad}; worst (Dt-T)/Dt = {worst1[1].str(6) if worst1 else '-'} "
                  f"(d={worst1[0] if worst1 else '-'}), worst rho/Q = {worst2[1].str(6) if worst2 else '-'} "
                  f"(d={worst2[0] if worst2 else '-'})  [{time.time()-t0:.0f}s]", flush=True)
    print(f"RESULT d = {d0}..{d1}: {'ALL VERIFIED' if not bad else 'FAILURES ' + str(bad)}")
