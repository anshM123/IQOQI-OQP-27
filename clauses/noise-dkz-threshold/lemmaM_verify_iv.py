"""
lemmaM_verify_iv.py -- INDEPENDENT re-check (mpmath interval arithmetic; separate code, imports nothing from
lemmaM_verify.py / lemmaM_anti.py / lemmaM_pairing.py) of the explicit Lemma M construction.

Part A (small d): builds the FULL pairing matrix pi on {0..S}^2 in interval arithmetic and checks directly, with no
use of the core lemma: pi = 0 off T = {x1 + x2 <= S}; pi symmetric; every cell of T strictly positive; every row sum
encloses Q(x); every difference R(y) - R(S-y) of anti-diagonal sums encloses 0.  (With the pairing lemma this proves
CLAIM_d, strictly, for these d.)
Part B (range of d): the three positivity conditions (P1)-(P3) of the construction plus the mean identity.
usage: python lemmaM_verify_iv.py A dmin dmax | B dmin dmax
"""
import sys
import time
import mpmath
from mpmath import iv

iv.prec = 113


def data(d):
    S = d - 1
    L = (S - 1) // 2
    pi = iv.pi
    G = [1 / (2 * d * d * iv.sin(pi * (4 * n + 1) / (4 * d)) ** 2) for n in range(d)]
    EG = sum((G[n] * n for n in range(d)), iv.mpf(0))
    kap = 2 - 4 * EG / (d - 1)                    # kappa_d := I(DKZ_d)/2 (definition)
    cc = (1 - 1 / kap) / d
    Q = [G[n] / kap + cc for n in range(d)]
    return S, L, Q


def construction(d):
    S, L, Q = data(d)
    if L == 0:
        return S, L, Q, None, [], None
    D = {z: Q[z] - Q[S - z] for z in range(1, L + 1)}
    eta = mpmath.mpf(D[L].a) / (200 * S)          # a positive real number below D(L)/(100 S)
    eta = iv.mpf(eta)
    M = S - L - 1
    w = {}
    T = iv.mpf(0)
    gaps = []
    for z in range(L, 0, -1):
        Feta = eta * (max(0, M - z) - (iv.mpf(z - 1) / 2 if 2 <= z <= M else 0))
        g = D[z] - Feta - T
        gaps.append(g)
        w[z] = 2 * g / (S - z + 1)
        T += w[z]
    return S, L, Q, eta, gaps, w


def partA(d):
    S, L, Q, eta, gaps, w = construction(d)
    n = d
    P = [[iv.mpf(0) for _ in range(n)] for _ in range(n)]
    if L >= 1:
        M = S - L - 1
        for x1 in range(1, n):
            for x2 in range(1, n):
                if x1 + x2 <= M:
                    P[x1][x2] += eta
        for y in range(1, L + 1):
            for t in range(1, S - y):
                P[t][S - y - t] += w[y]
    mI = [sum(P[x], iv.mpf(0)) for x in range(n)]
    rho = [Q[x] - mI[x] for x in range(n)]
    for x in range(1, S):
        A = min(rho[x].a, rho[S - x].a) / 2                   # any 0 < A <= min(rho) / 2 works; use a real number
        A = iv.mpf(A) if A > 0 else iv.mpf(0)
        P[x][S - x] += A
    # edges: E(x) = rho(x) - A(x), recomputed from the current antithetic weights
    for x in range(1, n):
        Ex = Q[x] - sum(P[x], iv.mpf(0))
        P[x][0] += Ex
        P[0][x] += Ex
    P[0][0] += Q[0] - sum(P[0], iv.mpf(0))
    ok = True
    msgs = []
    for x1 in range(n):
        for x2 in range(n):
            if x1 + x2 > S:
                if not (P[x1][x2].a == 0 and P[x1][x2].b == 0):
                    ok = False; msgs.append(("off-T", x1, x2))
            elif not (P[x1][x2].a > 0):
                ok = False; msgs.append(("nonpositive", x1, x2, P[x1][x2]))
            if not (P[x1][x2] - P[x2][x1]).a <= 0 <= (P[x1][x2] - P[x2][x1]).b:
                ok = False; msgs.append(("asym", x1, x2))
    for x in range(n):
        r = sum(P[x], iv.mpf(0)) - Q[x]
        if not (r.a <= 0 <= r.b):
            ok = False; msgs.append(("marginal", x, r))
    R = [sum((P[a][y - a] for a in range(0, y + 1)), iv.mpf(0)) for y in range(n)]
    for y in range(n):
        r = R[y] - R[S - y]
        if not (r.a <= 0 <= r.b):
            ok = False; msgs.append(("sum-law", y, r))
    return ok, msgs[:5]


def partB(d):
    S, L, Q, eta, gaps, w = construction(d)
    mean = sum((Q[k] * k for k in range(d)), iv.mpf(0)) - iv.mpf(S) / 4
    ok = (mean.a <= 0 <= mean.b) and ((2 * Q[0] - 1).a > 0)
    if L >= 1:
        ok = ok and (eta.a > 0) and all(g.a > 0 for g in gaps)
        M = S - L - 1
        Wp = [iv.mpf(0)] * (L + 1)
        for k in range(1, L + 1):
            Wp[k] = Wp[k - 1] + w[k]
        for x in range(1, S):
            k = min(L, S - 1 - x)
            mI = (Wp[k] if k >= 1 else iv.mpf(0)) + eta * max(0, M - x)
            if not (Q[x] - mI).a > 0:
                ok = False
    return ok


if __name__ == "__main__":
    part, d0, d1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    t0 = time.time()
    bad = []
    for d in range(d0, d1 + 1):
        if part == "A":
            ok, msgs = partA(d)
            if not ok:
                bad.append(d); print("FAIL", d, msgs, flush=True)
        else:
            if not partB(d):
                bad.append(d); print("FAIL", d, flush=True)
        if d % 250 == 0:
            print(f"  ... d <= {d}, failures {bad} [{time.time()-t0:.0f}s]", flush=True)
    print(f"RESULT part {part}, d = {d0}..{d1}: {'ALL VERIFIED' if not bad else 'FAILURES ' + str(bad)} "
          f"[{time.time()-t0:.0f}s]")
