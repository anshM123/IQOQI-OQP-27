"""
dd_exact.py -- exact double description (Motzkin) for the facets of a full-dimensional integer point
configuration, and an exact ADJACENCY-CLOSURE completeness check for facet lists of Bell polytopes.

facets_of_points(P): P = list of integer points spanning R^k affinely.  Returns the facets of conv(P) as primitive
integer vectors (y0, y) with y0 + y.p >= 0 for all p in P, each tight on an affinely spanning subset.
Method: extreme rays of the pointed cone {(y0,y) : y0 + y.p >= 0 for all p} by incremental DD with the
combinatorial adjacency test; the ray (1,0,...,0) (no tight point) is discarded.  All arithmetic: python ints.

closure_check(sc, reps, classify): for every representative facet F, enumerate ALL ridges (facets of F, via DD in
the affine hull of F), rotate each ridge to the neighbouring facet F' exactly, and classify F'.  If every
neighbour lies in a listed class, the union of the listed orbits is closed under ridge adjacency; since the facet
graph (dual graph) of a polytope is connected, the list is then COMPLETE.
"""
import math
from fractions import Fraction
import numpy as np


def primitive(v):
    g = 0
    for x in v:
        g = math.gcd(g, int(x))
    if g == 0:
        return tuple(int(x) for x in v)
    return tuple(int(x) // g for x in v)


def solve_simplicial_rays(A):
    """A: n x n integer matrix (rows = constraints a_i), nonsingular.  Rays of {y : A y >= 0}: columns of
    adj(A) up to sign, i.e. r_j with a_i . r_j = 0 (i != j), a_j . r_j > 0."""
    n = len(A)
    M = [[Fraction(x) for x in row] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    inv = [row[n:] for row in M]           # A^{-1}; columns are the rays (A inv = I)
    rays = []
    for j in range(n):
        col = [inv[i][j] for i in range(n)]
        den = 1
        for x in col:
            den = den * x.denominator // math.gcd(den, x.denominator)
        rays.append(primitive([int(x * den) for x in col]))
    return rays


def dd_cone(constraints):
    """extreme rays of {y : a.y >= 0 for a in constraints} (pointed, full-dimensional assumed).
    constraints: list of integer tuples (length n).  Returns list of (ray, frozenset of tight constraint indices)."""
    n = len(constraints[0])
    # choose n linearly independent constraints greedily
    basis = []
    Mrows = []
    for i, a in enumerate(constraints):
        trial = Mrows + [list(a)]
        if np.linalg.matrix_rank(np.array(trial, dtype=float)) > len(Mrows):
            # exact confirmation via Fractions rank is implicit in the later inversion (raises if singular)
            Mrows = trial
            basis.append(i)
            if len(basis) == n:
                break
    assert len(basis) == n, "constraints do not have full rank"
    rays = solve_simplicial_rays([constraints[i] for i in basis])
    C = constraints
    data = []
    for r in rays:
        tight = frozenset(i for i in basis if sum(a * b for a, b in zip(C[i], r)) == 0)
        data.append((r, tight))
    done = list(basis)
    for i in range(len(C)):
        if i in basis:
            continue
        a = C[i]
        vals = [sum(x * y for x, y in zip(a, r)) for (r, _) in data]
        plus = [k for k, v in enumerate(vals) if v > 0]
        minus = [k for k, v in enumerate(vals) if v < 0]
        zero = [k for k, v in enumerate(vals) if v == 0]
        new = []
        for k in plus:
            new.append(data[k])
        for k in zero:
            new.append((data[k][0], data[k][1] | {i}))
        # adjacency test (combinatorial): r+, r- adjacent iff no third ray's tight set contains Z+ & Z-,
        # and |Z+ & Z-| >= n - 2
        tsets = [t for (_, t) in data]
        for kp in plus:
            for km in minus:
                common = tsets[kp] & tsets[km]
                if len(common) < n - 2:
                    continue
                ok = True
                for k3 in range(len(data)):
                    if k3 != kp and k3 != km and common <= tsets[k3]:
                        ok = False
                        break
                if not ok:
                    continue
                rp, rm = data[kp][0], data[km][0]
                vp, vm = vals[kp], vals[km]
                nr = primitive([vp * y - vm * x for x, y in zip(rp, rm)])   # vp*rm - vm*rp, a.nr = 0
                new.append((nr, common | {i}))
        data = new
        done.append(i)
    return data


def facets_of_points(P):
    """P: list of integer points (tuples) spanning R^k affinely.  Facets as (y0, y), y0 + y.p >= 0."""
    cons = [tuple([1] + list(p)) for p in P]
    rays = dd_cone(cons)
    out = []
    for r, tight in rays:
        if all(x == 0 for x in r[1:]):
            continue          # the trivial ray y0 > 0
        out.append((r, tight))
    return out


def affine_coords(points):
    """integer points on a (k-1)-dim affine subspace of Z^m -> integer coordinates in Z^(k-1)... uses a set of
    pivot coordinates: choose coordinates that are affinely independent (projection is injective on the
    affine hull)."""
    P = np.array(points, dtype=float)
    X = P[1:] - P[0]
    k = np.linalg.matrix_rank(X)
    # greedy choice of k coordinates with rank k
    cols = []
    for j in range(P.shape[1]):
        if np.linalg.matrix_rank(X[:, cols + [j]]) > len(cols):
            cols.append(j)
            if len(cols) == k:
                break
    return [tuple(int(points[i][j]) for j in cols) for i in range(len(points))], cols
