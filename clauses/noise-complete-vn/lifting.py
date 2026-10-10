"""
lifting.py -- outcome liftings (coarse-grainings) of lower-outcome Bell inequalities into the (2,2,d) scenario.

A lower inequality is given on full probabilities: beta'[x][y] = k_x x l_y integer matrix (Alice x has k_x
outcomes, Bob y has l_y outcomes) with local bound L'.  A lifting is a family of surjections
c_Ax : [d] -> [k_x], c_By : [d] -> [l_y]; beta(a,b|x,y) = beta'_xy(c_Ax(a), c_By(b)), same local bound.
The lifted inequality is converted to an exact CG facet via its tight set (facet_lib.facet_from_tight).
"""
import itertools
import numpy as np
from facet_lib import Scenario, facet_from_tight


def chsh_full():
    """CHSH as P(a=b|00)+P(a=b|01)+P(a=b|10)+P(a!=b|11) <= 3 on full probabilities (2 outcomes)."""
    eq = np.eye(2, dtype=int)
    ne = 1 - eq
    return [[eq, eq], [eq, ne]], 3


def cglmp3_full():
    """CGLMP_3 in the probability (chain) form: P(X1<Y1)+P(Y1<X2)+P(X2<Y2)+P(Y2<=X1) >= 1 for local,
    i.e. as an upper bound: -(...) <= -1.  Here written with the standard coefficients I_3 <= 2."""
    d = 3
    B = np.zeros((2, 2, d, d), dtype=int)
    # I_d = sum_k (1-2k/(d-1)) [P(A1=B1+k)+P(B1=A2+k+1)+P(A2=B2+k)+P(B2=A1+k) - P(A1=B1-k-1)
    #       - P(B1=A2-k) - P(A2=B2-k-1) - P(B2=A1-k-1)], k = 0 only for d = 3 (weight 1); local bound 2.
    for a in range(d):
        for b in range(d):
            # (x,y) = (0,0): A1,B1 ; (1,0): A2,B1 ; (1,1): A2,B2 ; (0,1): A1,B2
            B[0, 0, a, b] += (1 if a == b else 0) - (1 if a == (b - 1) % d else 0)
            B[1, 0, a, b] += (1 if b == (a + 1) % d else 0) - (1 if b == a else 0)
            B[1, 1, a, b] += (1 if a == b else 0) - (1 if a == (b - 1) % d else 0)
            B[0, 1, a, b] += (1 if b == a else 0) - (1 if b == (a - 1) % d else 0)
    return [[B[0, 0], B[0, 1]], [B[1, 0], B[1, 1]]], 2


def local_bound(beta):
    kA = [len(beta[0][0]), len(beta[1][0])]
    kB = [len(beta[0][0][0]), len(beta[0][1][0])]
    best = None
    for a0 in range(kA[0]):
        for a1 in range(kA[1]):
            for b0 in range(kB[0]):
                for b1 in range(kB[1]):
                    a = (a0, a1); b = (b0, b1)
                    v = sum(int(beta[x][y][a[x]][b[y]]) for x in range(2) for y in range(2))
                    best = v if best is None else max(best, v)
    return best


def lift(beta, L, maps, d):
    """maps = (cA0, cA1, cB0, cB1), each a length-d tuple of lower outcomes. Returns full coefficient tensor."""
    C = np.zeros((2, 2, d, d), dtype=np.int64)
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    C[x, y, a, b] = beta[x][y][maps[x][a]][maps[2 + y][b]]
    return C, L


def full_to_facet(sc, C, L):
    """full coefficient tensor C with local bound L -> exact CG Facet (raises if not a facet)."""
    d = sc.d
    vals = np.array([sum(int(C[x, y, lam[x], lam[2 + y]]) for x in range(2) for y in range(2))
                     for lam in sc.lams])
    assert vals.max() == L, (vals.max(), L)
    tight = np.where(vals == L)[0]
    F = facet_from_tight(sc, tight)
    return F


def surjections(d, k):
    out = []
    for m in itertools.product(range(k), repeat=d):
        if len(set(m)) == k:
            out.append(m)
    return out
