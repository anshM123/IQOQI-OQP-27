"""
competitor_model.py -- independent cross-check of Proposition 5 that does NOT use the facet list of L(2,2,3):
for each d, an explicit local model of the reduced competitor behaviour q_{v*} = v* q + (1 - v*) n_{1/d} at the exact
critical visibility v* = v_even(d) / v_odd(d), with weights in Q(sqrt2), verified exactly.

Method: a floating-point LP (HiGHS) over the 81 deterministic strategies of the (2,2,3) scenario finds a vertex
solution; its support S is then used to solve A_S w = q_{v*} EXACTLY in Q(sqrt2) (Gaussian elimination with the Q2 class
of exact.py); the solution is accepted only if it satisfies all 36 equations exactly and w >= 0 exactly.  Together with
Lemma 3 this shows v_c(C_d) >= v*, and Lemma 2 gives v_c(C_d) <= v*.

usage: python competitor_model.py [dmin dmax]
"""
import itertools
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

from exact import Q2

SQ2 = Q2(0, 1)
S = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}


def target(d):
    """exact q_{v*} on {0,1,R}^2 (dict (x,y,a,b) -> Q2) and v*."""
    t = Fr(1, d)
    if d % 2 == 0:
        vstar = Q2(4 * (d - 1)) / ((SQ2 - 1) * (d * d) + 4 * (d - 1))
    else:
        vstar = Q2(4) / ((SQ2 - 1) * d + 4)
    m = [t, t, 1 - 2 * t]
    q = {}
    for x in range(2):
        for y in range(2):
            for a in range(3):
                for b in range(3):
                    ch = Q2(0)
                    if a < 2 and b < 2:
                        ch = (Q2(1) + (1 if a == b else -1) * S[(x, y)] * Q2(0, Fr(1, 2))) * Fr(1, 4)
                    if d % 2 == 1:
                        ch = ch * (1 - t) + (t if (a == 0 and b == 0) else 0)
                    q[(x, y, a, b)] = vstar * ch + (1 - vstar) * (m[a] * m[b])
    return q, vstar


def solve_exact(A, rhs, cols):
    """exact solution of A[:, cols] w = rhs in Q(sqrt2) (A integer 0/1, rhs Q2); None if inconsistent."""
    rows = len(A)
    M = [[Q2(A[r][c]) for c in cols] + [rhs[r]] for r in range(rows)]
    n = len(cols)
    piv_cols = []
    r0 = 0
    for c in range(n):
        piv = next((r for r in range(r0, rows) if not M[r][c] == Q2(0)), None)
        if piv is None:
            continue
        M[r0], M[piv] = M[piv], M[r0]
        pv = M[r0][c]
        M[r0] = [x / pv for x in M[r0]]
        for r in range(rows):
            if r != r0 and not M[r][c] == Q2(0):
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[r0])]
        piv_cols.append(c)
        r0 += 1
    # consistency
    for r in range(r0, rows):
        if not M[r][n] == Q2(0):
            return None
    w = [Q2(0)] * n
    for i, c in enumerate(piv_cols):
        w[c] = M[i][n]
    return w


def run(d, verbose=True):
    q, vstar = target(d)
    strat = list(itertools.product(range(3), repeat=4))
    keys = sorted(q)
    A = [[int(s[k[0]] == k[2] and s[2 + k[1]] == k[3]) for s in strat] for k in keys]
    rhs = [q[k] for k in keys]
    Af = np.array(A, float)
    bf = np.array([float(x) for x in rhs])
    rng = np.random.default_rng(d)
    for attempt in range(20):
        c = rng.random(len(strat))
        res = linprog(c, A_eq=Af, b_eq=bf, bounds=(0, None), method="highs")
        if res.status != 0:
            continue
        sup = [i for i in range(len(strat)) if res.x[i] > 1e-11]
        w = solve_exact(A, rhs, sup)
        if w is None or any(x.sign() < 0 for x in w):
            continue
        # exact verification of all 36 equations
        ok = all(sum((w[j] * A[r][i] for j, i in enumerate(sup)), Q2(0)) == rhs[r] for r in range(len(keys)))
        if ok:
            if verbose:
                print(f"  d={d:2d}: exact local model of q_v* at v* = {float(vstar):.12f} with {len(sup)} "
                      f"deterministic strategies, weights in Q(sqrt2), all >= 0, all 36 equations exact: OK")
            return True
    if verbose:
        print(f"  d={d:2d}: FAILED to find an exact model")
    return False


if __name__ == "__main__":
    lo, hi = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (3, 12)
    ok = all(run(d) for d in range(lo, hi + 1))
    print("RESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


def flag_model(s_param, exact=True):
    """explicit facet-free local model of R_v = v CH + (1-v) nu (x) nu, nu = (s, s, 1-2s), at v = T(s) =
    4s(1-s)/(sqrt2 - (1-2s)^2) (independent-check-B/REPORT.md sec. 2.4).  Outcome 2 plays the role of '*' (= R).
    Returns (weights dict strategy -> weight, v)."""
    s = Fr(s_param)
    v = Q2(4 * s * (1 - s)) / (SQ2 - (1 - 2 * s) ** 2)
    rho = (1 - v) * (1 - 2 * s)
    sig = (1 - v) * (1 - 2 * s) ** 2
    pi0 = 1 - 4 * rho + 3 * sig
    W = {}

    def add(st, w):
        W[st] = W.get(st, Q2(0)) + w
    add((2, 2, 2, 2), sig)
    for r in (0, 1):
        h = (rho - sig) * Fr(1, 2)
        add((2, r, r, 1 - r), h)          # A0 = *: (A1, B0, B1) = (r, r, 1-r)
        add((r, 2, r, r), h)              # A1 = *: (A0, B0, B1) = (r, r, r)
        add((r, 1 - r, 2, r), h)          # B0 = *: (A0, A1, B1) = (r, 1-r, r)
        add((r, r, r, 2), h)              # B1 = *: (A0, A1, B0) = (r, r, r)
    for st in itertools.product((0, 1), repeat=4):
        val = sum(S[(x, y)] * (1 if (st[x] + st[2 + y]) % 2 == 0 else -1) for x in range(2) for y in range(2))
        if val == 2:
            add(st, pi0 * Fr(1, 8))
    return W, v


def check_flag_model(dmax=40):
    """exact check, s = 1/d for d = 2..dmax: weights >= 0, sum 1, link marginals = v CH + (1-v) nu (x) nu."""
    ok = True
    for d in range(2, dmax + 1):
        s = Fr(1, d)
        W, v = flag_model(s)
        ok &= all(w.sign() >= 0 for w in W.values()) and sum(W.values(), Q2(0)) == Q2(1)
        m = [s, s, 1 - 2 * s]
        for x in range(2):
            for y in range(2):
                for a in range(3):
                    for b in range(3):
                        lhs = sum((w for st, w in W.items() if st[x] == a and st[2 + y] == b), Q2(0))
                        ch = (Q2(1) + (1 if a == b else -1) * S[(x, y)] * Q2(0, Fr(1, 2))) * Fr(1, 4) if a < 2 and b < 2 else Q2(0)
                        ok &= lhs == v * ch + (1 - v) * (m[a] * m[b])
        # v = T(1/d) equals v_even(d)
        ok &= v == Q2(4 * (d - 1)) / ((SQ2 - 1) * (d * d) + 4 * (d - 1))
    return ok
