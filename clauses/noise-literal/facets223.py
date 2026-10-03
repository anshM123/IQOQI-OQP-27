"""
facets223.py -- complete facet list of the local polytope L(2,2,3) by an exact double-description computation,
and its classification into the three classes positivity / lifted CHSH / CGLMP_3 (orbits under relabellings).

Coordinates (Collins-Gisin, 24 of them): pA(a|x), pB(b|y) for a, b in {0,1}; p(a,b|x,y) for a, b in {0,1}.
These determine a no-signalling behaviour on {0,1,2}^2 uniquely, and L(2,2,3) is full-dimensional in them.
Vertices: the 81 deterministic strategies (a0, a1, b0, b1).

Double description (Motzkin-Raiffa-Thompson-Thrall; Fukuda-Prodon 1996): the facets of P = conv(V) are the extreme
rays of the pointed cone C = { h in Z^25 : h0 + h'.v >= 0 for all v in V }.  Exact integer arithmetic, combinatorial
adjacency test (r+, r- adjacent iff no third current ray vanishes on all rows where both vanish).  Every output ray
is then re-checked exactly (validity on all 81 vertices, facet: tight vertices have affine rank 24).

The output is compared (as sets of normalised integer inequalities) with the explicitly generated classes:
  positivity p(a,b|x,y) >= 0 (36), lifted CHSH (coarse-grain every measurement by a 1|2 partition, 3^4 * 8 = 648),
  CGLMP_3 orbit under the symmetry group (outcome permutations per measurement, setting swaps, party swap).

usage: python facets223.py            (writes facets223.txt; ~1 min)
"""
import itertools
import sys
import time
from fractions import Fraction
from math import gcd

import numpy as np

D = 3


# ------------------------------------------------------------------------------------------------------------------
# coordinates
# ------------------------------------------------------------------------------------------------------------------
def cg_index():
    """index map of the 24 CG coordinates."""
    idx = {}
    k = 0
    for x in range(2):
        for a in range(2):
            idx[("A", x, a)] = k
            k += 1
    for y in range(2):
        for b in range(2):
            idx[("B", y, b)] = k
            k += 1
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    idx[("AB", x, y, a, b)] = k
                    k += 1
    return idx


IDX = cg_index()
NCG = len(IDX)          # 24


def strategies():
    return list(itertools.product(range(D), repeat=4))       # (a0, a1, b0, b1)


def cg_vertex(s):
    a = (s[0], s[1])
    b = (s[2], s[3])
    v = [0] * NCG
    for x in range(2):
        for k in range(2):
            v[IDX[("A", x, k)]] = int(a[x] == k)
    for y in range(2):
        for k in range(2):
            v[IDX[("B", y, k)]] = int(b[y] == k)
    for x in range(2):
        for y in range(2):
            for i in range(2):
                for j in range(2):
                    v[IDX[("AB", x, y, i, j)]] = int(a[x] == i and b[y] == j)
    return v


def full_to_cg(beta):
    """beta[x][y][a][b] (rational) acting on full behaviours p(a,b|x,y): returns (c0, c) with
    sum beta p = c0 + c . (CG coordinates of p) for every no-signalling p (exact)."""
    c0 = Fraction(0)
    c = [Fraction(0)] * NCG
    for x in range(2):
        for y in range(2):
            for a in range(D):
                for b in range(D):
                    w = Fraction(beta[x][y][a][b])
                    if w == 0:
                        continue
                    # express p(a,b|x,y) in CG coordinates
                    terms = []          # list of (coef, key or None for constant)
                    if a < 2 and b < 2:
                        terms = [(1, ("AB", x, y, a, b))]
                    elif a < 2 and b == 2:
                        # p(a,2) = pA(a|x) - p(a,0) - p(a,1)
                        terms = [(1, ("A", x, a)), (-1, ("AB", x, y, a, 0)), (-1, ("AB", x, y, a, 1))]
                    elif a == 2 and b < 2:
                        terms = [(1, ("B", y, b)), (-1, ("AB", x, y, 0, b)), (-1, ("AB", x, y, 1, b))]
                    else:
                        # p(2,2) = 1 - pA(0) - pA(1) - pB(0) - pB(1) + sum_{i,j<2} p(i,j)
                        terms = [(1, None), (-1, ("A", x, 0)), (-1, ("A", x, 1)), (-1, ("B", y, 0)),
                                 (-1, ("B", y, 1))] + [(1, ("AB", x, y, i, j)) for i in range(2) for j in range(2)]
                    for co, key in terms:
                        if key is None:
                            c0 += w * co
                        else:
                            c[IDX[key]] += w * co
    return c0, c


def normalise(h):
    """integer vector h (h0, h') of the inequality h0 + h'.x >= 0 -> primitive integer tuple."""
    den = 1
    for t in h:
        if isinstance(t, Fraction):
            den = den * t.denominator // gcd(den, t.denominator)
    hi = [int(t * den) for t in h]
    g = 0
    for t in hi:
        g = gcd(g, abs(t))
    return tuple(t // g for t in hi)


def ineq_from_full(beta, bound):
    """Bell inequality sum beta p <= bound  ->  normalised (h0, h') with h0 + h'.x >= 0."""
    c0, c = full_to_cg(beta)
    h = [Fraction(bound) - c0] + [-t for t in c]
    return normalise(h)


# ------------------------------------------------------------------------------------------------------------------
# exact double description
# ------------------------------------------------------------------------------------------------------------------
def int_rank(M):
    """exact rank of an integer matrix (fraction-free Gaussian elimination)."""
    M = [list(map(int, row)) for row in M]
    if not M:
        return 0
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(r + 1, rows):
            if M[i][c] != 0:
                f, g = M[i][c], M[r][c]
                M[i] = [g * M[i][j] - f * M[r][j] for j in range(cols)]
                gg = 0
                for t in M[i]:
                    gg = gcd(gg, abs(t))
                if gg > 1:
                    M[i] = [t // gg for t in M[i]]
        r += 1
        if r == rows:
            break
    return r


def solve_int_inverse_columns(B):
    """B: n x n nonsingular integer matrix.  returns integer vectors r_j (primitive, positive multiples of the
    columns of B^{-1}) so that B r_j = lambda_j e_j with lambda_j > 0."""
    n = len(B)
    M = [[Fraction(B[i][j]) for j in range(n)] + [Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [t / pv for t in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][j] - f * M[c][j] for j in range(2 * n)]
    inv = [[M[i][n + j] for j in range(n)] for i in range(n)]
    rays = []
    for j in range(n):
        col = [inv[i][j] for i in range(n)]
        rays.append(list(normalise(col)))
    return rays


def popcount2(z):
    return np.bitwise_count(z).sum(axis=-1)


def double_description(A, order=None, verbose=True):
    """extreme rays of {h : A h >= 0} (A integer m x n of rank n).  Returns list of primitive integer rays."""
    A = np.asarray(A, dtype=object)
    m, n = A.shape
    order = list(range(m)) if order is None else list(order)
    # greedy choice of n independent rows
    K = []
    for i in order:
        if int_rank([list(A[j]) for j in K + [i]]) == len(K) + 1:
            K.append(i)
        if len(K) == n:
            break
    assert len(K) == n, "A does not have full column rank"
    rays = solve_int_inverse_columns([list(A[i]) for i in K])
    Ai = np.array(A, dtype=np.int64)
    R = np.array(rays, dtype=object)
    words = (m + 63) // 64

    def zero_mask(Rm, rows):
        Z = np.zeros((len(Rm), words), dtype=np.uint64)
        if len(Rm) == 0:
            return Z
        vals = np.array([[int(np.dot(Ai[i].astype(object), r)) for i in rows] for r in Rm], dtype=object)
        for k, i in enumerate(rows):
            hit = np.array([v == 0 for v in vals[:, k]])
            Z[hit, i // 64] |= np.uint64(1) << np.uint64(i % 64)
        return Z

    processed = list(K)
    Z = zero_mask(R, processed)
    rest = [i for i in order if i not in K]
    t0 = time.time()
    for step, i in enumerate(rest):
        ai = Ai[i].astype(object)
        s = np.array([int(np.dot(ai, r)) for r in R], dtype=object)
        pos = [k for k in range(len(R)) if s[k] > 0]
        neg = [k for k in range(len(R)) if s[k] < 0]
        zer = [k for k in range(len(R)) if s[k] == 0]
        new_rays = []
        new_Z = []
        if neg:
            Zneg = Z[neg]
            for kp in pos:
                inter = Z[kp][None, :] & Zneg
                cnt = popcount2(inter)
                cand = np.nonzero(cnt >= n - 2)[0]
                for c in cand:
                    kn = neg[c]
                    zz = inter[c]
                    # combinatorial adjacency test: rays containing zz must be exactly kp and kn
                    cont = np.all((Z & zz[None, :]) == zz[None, :], axis=1)
                    if int(cont.sum()) != 2:
                        continue
                    r = s[kp] * R[kn] - s[kn] * R[kp]
                    g = 0
                    for t in r:
                        g = gcd(g, abs(int(t)))
                    r = np.array([int(t) // g for t in r], dtype=object)
                    znew = zz.copy()
                    znew[i // 64] |= np.uint64(1) << np.uint64(i % 64)
                    new_rays.append(r)
                    new_Z.append(znew)
        keep = pos + zer
        Zk = Z[keep].copy()
        for k_, k in enumerate(keep):
            if s[k] == 0:
                Zk[k_, i // 64] |= np.uint64(1) << np.uint64(i % 64)
        R = np.array([R[k] for k in keep] + new_rays, dtype=object)
        Z = np.vstack([Zk] + ([np.array(new_Z, dtype=np.uint64)] if new_Z else []))
        processed.append(i)
        if verbose:
            print(f"  DD step {step + 1}/{len(rest)}: |R+|={len(pos)} |R0|={len(zer)} |R-|={len(neg)} "
                  f"-> {len(R)} rays  ({time.time() - t0:.1f}s)", flush=True)
    return [tuple(int(t) for t in r) for r in R]


# ------------------------------------------------------------------------------------------------------------------
# candidate classes
# ------------------------------------------------------------------------------------------------------------------
def zero_beta():
    return [[[[Fraction(0)] * D for _ in range(D)] for _ in range(2)] for _ in range(2)]


def positivity_ineqs():
    out = set()
    for x, y, a, b in itertools.product(range(2), range(2), range(D), range(D)):
        beta = zero_beta()
        beta[x][y][a][b] = Fraction(-1)          # -p(a,b|x,y) <= 0
        out.add(ineq_from_full(beta, 0))
    return out


def chsh_lifted_ineqs():
    """sum_xy s_xy E_xy <= 2 with E_xy the correlator of the coarse-grained observables
    A_x = +1 on outcome group S_x (a singleton) and -1 otherwise; prod s = -1."""
    out = set()
    for Sa0, Sa1, Sb0, Sb1 in itertools.product(range(D), repeat=4):
        for s in itertools.product((1, -1), repeat=4):
            if s[0] * s[1] * s[2] * s[3] != -1:
                continue
            Sa, Sb = (Sa0, Sa1), (Sb0, Sb1)
            beta = zero_beta()
            for x in range(2):
                for y in range(2):
                    for a in range(D):
                        for b in range(D):
                            ea = 1 if a == Sa[x] else -1
                            eb = 1 if b == Sb[y] else -1
                            beta[x][y][a][b] += s[2 * x + y] * ea * eb
            out.add(ineq_from_full(beta, 2))
    return out


def cglmp_beta(d=D):
    """CGLMP I_d coefficients in the reading of the mathematical paper (A1 = x0, A2 = x1, B1 = y0, B2 = y1)."""
    beta = zero_beta() if d == D else [[[[Fraction(0)] * d for _ in range(d)] for _ in range(2)] for _ in range(2)]
    for k in range(d // 2):
        w = Fraction(1) - Fraction(2 * k, d - 1)
        for a in range(d):
            for b in range(d):
                # +P(A1 = B1 + k) : x0,y0, a = b + k
                if (a - b - k) % d == 0:
                    beta[0][0][a][b] += w
                # +P(B1 = A2 + k + 1) : x1,y0, b = a + k + 1
                if (b - a - k - 1) % d == 0:
                    beta[1][0][a][b] += w
                # +P(A2 = B2 + k) : x1,y1
                if (a - b - k) % d == 0:
                    beta[1][1][a][b] += w
                # +P(B2 = A1 + k) : x0,y1, b = a + k
                if (b - a - k) % d == 0:
                    beta[0][1][a][b] += w
                # -P(A1 = B1 - k - 1)
                if (a - b + k + 1) % d == 0:
                    beta[0][0][a][b] -= w
                # -P(B1 = A2 - k)
                if (b - a + k) % d == 0:
                    beta[1][0][a][b] -= w
                # -P(A2 = B2 - k - 1)
                if (a - b + k + 1) % d == 0:
                    beta[1][1][a][b] -= w
                # -P(B2 = A1 - k - 1)
                if (b - a + k + 1) % d == 0:
                    beta[0][1][a][b] -= w
    return beta


def apply_symmetry(beta, perms, swapx, swapy, swapparty):
    """relabelled functional: (g beta)(p) = beta(g^{-1} p); we simply relabel indices of beta, which runs over the
    whole group when the group element runs over the group."""
    nb = zero_beta()
    for x in range(2):
        for y in range(2):
            for a in range(D):
                for b in range(D):
                    X = 1 - x if swapx else x
                    Y = 1 - y if swapy else y
                    A = perms[X][a]
                    B = perms[2 + Y][b]
                    if swapparty:
                        nb[y][x][b][a] += beta[X][Y][A][B]
                    else:
                        nb[x][y][a][b] += beta[X][Y][A][B]
    return nb


def cglmp_orbit():
    beta0 = cglmp_beta()
    out = set()
    perms_all = list(itertools.permutations(range(D)))
    for P in itertools.product(perms_all, repeat=4):
        for sx, sy, sp in itertools.product((0, 1), repeat=3):
            out.add(ineq_from_full(apply_symmetry(beta0, P, sx, sy, sp), 2))
    return out


# ------------------------------------------------------------------------------------------------------------------
def check_facet(h, V):
    """exact: valid on all vertices; tight vertices have affine rank NCG (i.e. span a hyperplane)."""
    vals = [h[0] + sum(hi * vi for hi, vi in zip(h[1:], v)) for v in V]
    if min(vals) < 0:
        return False, "invalid"
    tight = [[1] + list(v) for v, t in zip(V, vals) if t == 0]
    rk = int_rank(tight)
    return rk == NCG, f"rank {rk}"


def main():
    V = [cg_vertex(s) for s in strategies()]
    A = [[1] + v for v in V]
    assert int_rank(A) == NCG + 1
    print(f"L(2,2,3): {len(V)} vertices in R^{NCG} (full-dimensional)", flush=True)
    t0 = time.time()
    rays = double_description(A, verbose=False)
    print(f"double description: {len(rays)} extreme rays ({time.time() - t0:.1f}s)", flush=True)
    F = set(normalise(list(r)) for r in rays)
    assert len(F) == len(rays)
    bad = [h for h in F if not check_facet(h, V)[0]]
    print(f"exact facet check: {len(F) - len(bad)} facets verified, {len(bad)} failures", flush=True)
    pos = positivity_ineqs()
    chsh = chsh_lifted_ineqs()
    cgl = cglmp_orbit()
    print(f"classes: positivity {len(pos)}, lifted CHSH {len(chsh)}, CGLMP_3 orbit {len(cgl)}", flush=True)
    for name, S in (("positivity", pos), ("lifted CHSH", chsh), ("CGLMP", cgl)):
        nf = sum(1 for h in S if check_facet(h, V)[0])
        print(f"  {name}: {nf}/{len(S)} are facets", flush=True)
    U = pos | chsh | cgl
    print(f"union of classes: {len(U)};  DD facets == union: {F == U}", flush=True)
    with open("facets223.txt", "w") as f:
        f.write("# facets of L(2,2,3) in CG coordinates: h0 + h.x >= 0 ; class\n")
        for h in sorted(F):
            cls = "positivity" if h in pos else "CHSH" if h in chsh else "CGLMP" if h in cgl else "OTHER"
            f.write(" ".join(map(str, h)) + " ; " + cls + "\n")
    return F == U and not bad


if __name__ == "__main__":
    ok = main()
    print("RESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
