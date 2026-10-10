"""
CLOSE_lib.py -- routines for the completeness proof of facet lists of the (2,2,d) local polytope L via the
no-signalling polytope NS (the "visibility argument", see CLOSE_NOTES.md).  Every decision is exact
(python integers / Fractions); floating point is only used to propose candidates (LP), which are then
re-derived and verified exactly.

Contents
  positivity_forms(sc)      the 4 d^2 affine forms p(ab|xy) = c0 + A.cg on the CG coordinates (verified exactly
                            on all deterministic points)
  ns_vertices_polar(...)    all vertices of NS = {cg : p(ab|xy) >= 0}: facets of the polar conv{q_i} by exact
                            double description (CLOSE_dd_safe: no-overflow certificate), each vertex verified exactly
  cone_rays(C)              extreme rays of a pointed cone {r : C r >= 0} (exact integer DD, numba)
  ns_neighbours(...)        all NS-edges at a vertex (tangent cone rays) and their other endpoints (exact)
  full_tensor / pr_tensor   behaviours as exact tensors W[x][y][a][b]
  pr_structure(W, d)        recognises a generalised PR box: returns (k, relabelling) with W = g.PR_k exactly
  violated_known_facet(...) LP proposal of a facet of L violated by a behaviour, exact re-derivation, exact
                            classification into a listed class by an explicit relabelling, exact violation
"""
import itertools
import math
from fractions import Fraction
import numpy as np
from facet_lib import Facet, facet_from_tight
import CLOSE_dd_safe


# ----------------------------------------------------------------------------- positivity forms
def positivity_forms(sc):
    """keys[i] = (x, y, a, b); f_i(cg) = c0[i] + A[i] . cg equals p(ab|xy) on every no-signalling behaviour."""
    d, n = sc.d, sc.dim
    idx = sc.cg_index()
    keys, c0, A = [], [], []
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    vec = [0] * n
                    c = 0
                    if a < d - 1 and b < d - 1:
                        vec[idx[('AB', x, y, a, b)]] += 1
                    elif a < d - 1:
                        vec[idx[('A', x, a)]] += 1
                        for bb in range(d - 1):
                            vec[idx[('AB', x, y, a, bb)]] -= 1
                    elif b < d - 1:
                        vec[idx[('B', y, b)]] += 1
                        for aa in range(d - 1):
                            vec[idx[('AB', x, y, aa, b)]] -= 1
                    else:
                        c = 1
                        for aa in range(d - 1):
                            vec[idx[('A', x, aa)]] -= 1
                        for bb in range(d - 1):
                            vec[idx[('B', y, bb)]] -= 1
                        for aa in range(d - 1):
                            for bb in range(d - 1):
                                vec[idx[('AB', x, y, aa, bb)]] += 1
                    keys.append((x, y, a, b))
                    c0.append(c)
                    A.append(vec)
    c0 = np.array(c0, dtype=np.int64)
    A = np.array(A, dtype=np.int64)
    # exact check on all deterministic points: f_{xyab}(lam) = [a_x = a][b_y = b]
    vals = c0[None, :] + sc.V @ A.T
    for r, lam in enumerate(sc.lams):
        for i, (x, y, a, b) in enumerate(keys):
            assert int(vals[r, i]) == int(lam[x] == a and lam[2 + y] == b)
    return keys, c0, A


def u_exact(sc):
    d = sc.d
    out = [Fraction(1, d)] * (2 * (d - 1)) + [Fraction(1, d)] * (2 * (d - 1)) + [Fraction(1, d * d)] * (4 * (d - 1) ** 2)
    return out


def form_values(c0, A, x):
    """exact values of all positivity forms at the (Fraction) CG point x."""
    out = []
    for i in range(len(c0)):
        s = Fraction(int(c0[i]))
        row = A[i]
        for j in np.nonzero(row)[0]:
            s += int(row[j]) * x[j]
        out.append(s)
    return out


def exact_rank_rows(rows):
    """rank of a list of integer rows (fraction-free elimination)."""
    M = [list(map(int, r)) for r in rows]
    if not M:
        return 0
    n, m = len(M), len(M[0])
    rank = 0
    for col in range(m):
        piv = None
        for i in range(rank, n):
            if M[i][col] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        for i in range(rank + 1, n):
            if M[i][col] != 0:
                a, b = M[rank][col], M[i][col]
                M[i] = [a * M[i][j] - b * M[rank][j] for j in range(m)]
                g = 0
                for t in M[i]:
                    g = math.gcd(g, t)
                if g > 1:
                    M[i] = [t // g for t in M[i]]
        rank += 1
        if rank == n:
            break
    return rank


# ----------------------------------------------------------------------------- NS vertices
def ns_vertices_polar(sc, c0, A, verbose=False):
    """All vertices of NS.  NS - u = {y : q_i . y <= 1}, q_i = -d^2 A_i (integers); its vertices are the facets of
    the polar conv{q_i}, computed by exact DD with a no-overflow certificate (CLOSE_dd_safe).  For the facet
    (r0, r') (r0 + r'.q >= 0, tight on T) the vertex is x = u - r'/r0 and, since f_i(u) = 1/d^2 for every form,
        f_i(x) = (r0 - d^2 A_i.r') / (d^2 r0)          (exact integers; |entries| tiny, bound certified by the DD).
    Every vertex is verified exactly: all numerators >= 0 and zero exactly on the DD tight set.
    Returns (num, den): num[v, i] = numerator of f_i at vertex v (int64), den[v] = d^2 r0 (int64)."""
    d, n = sc.d, sc.dim
    Q = [tuple(int(v) for v in (-d * d) * A[i]) for i in range(len(A))]
    u = u_exact(sc)
    assert all(v == Fraction(1, d * d) for v in form_values(c0, A, u))
    R, Z, m = CLOSE_dd_safe.facets_of_points_safe_arrays(Q, verbose=verbose)
    assert m == len(A)
    r0 = R[:, 0].astype(np.int64)
    assert (r0 > 0).all(), "origin must be interior to the polar"
    M = int(np.abs(R).max())
    assert 2 * (d * d) * n * M < 2 ** 62          # the products below are exact in int64
    num = r0[:, None] - (d * d) * (R[:, 1:] @ A.T)
    assert (num >= 0).all(), "vertex outside NS"
    bits = np.zeros((len(R), Z.shape[1]), np.uint64)
    zr, zc = np.nonzero(num == 0)
    np.bitwise_or.at(bits, (zr, zc // 64), np.left_shift(np.uint64(1), (zc % 64).astype(np.uint64)))
    assert np.array_equal(bits, Z), "tight set mismatch"
    return num, (d * d) * r0


def values_to_tensor(keys, d, num, den):
    """W[x][y][a][b] = num_i / den for the positivity form i = (x, y, a, b)."""
    W = [[[[None] * d for _ in range(d)] for _ in range(2)] for _ in range(2)]
    for (x, y, a, b), v in zip(keys, num):
        W[x][y][a][b] = Fraction(int(v), int(den))
    return W


def cone_rays(C, verbose=False):
    """extreme rays of the pointed cone {r : C r >= 0} (C integer m x n of rank n) by exact incremental DD with a
    certificate that no int64 overflow can occur (CLOSE_dd_safe.cone_rays_safe).  Returns list of (ray, tight)."""
    return CLOSE_dd_safe.cone_rays_safe(C, verbose=verbose, label="cone dd")


def ns_neighbours(c0, A, x0, verbose=False):
    """all NS-edges at the vertex x0 (exact Fractions): extreme rays r of the tangent cone {r : A_T r >= 0}
    (T = forms vanishing at x0) and the other endpoint x0 + t* r, t* = min_{A_i r < 0} f_i(x0)/(-A_i r)."""
    vals = form_values(c0, A, x0)
    T = [i for i, v in enumerate(vals) if v == 0]
    assert exact_rank_rows([A[i] for i in T]) == A.shape[1], "not a vertex"
    rays = cone_rays([A[i] for i in T], verbose=verbose)
    out = []
    for r, _ in rays:
        Ar = A.astype(object) @ np.array(r, dtype=object)
        best = None
        for i in range(len(c0)):
            if int(Ar[i]) < 0:
                t = vals[i] / Fraction(-int(Ar[i]))
                if best is None or t < best:
                    best = t
        assert best is not None and best > 0
        x1 = tuple(x0[j] + best * int(r[j]) for j in range(len(x0)))
        out.append((r, x1))
    return out


# ----------------------------------------------------------------------------- behaviours
def full_tensor(sc, keys, c0, A, x):
    d = sc.d
    W = [[[[None] * d for _ in range(d)] for _ in range(2)] for _ in range(2)]
    for (xx, yy, a, b), v in zip(keys, form_values(c0, A, x)):
        W[xx][yy][a][b] = v
    return W


def pr_tensor(d, k):
    """canonical generalised PR box with k outcomes embedded in d: 1/k if a, b < k and b - a = xy mod k."""
    W = [[[[Fraction(0)] * d for _ in range(d)] for _ in range(2)] for _ in range(2)]
    for x in range(2):
        for y in range(2):
            for a in range(k):
                b = (a + x * y) % k
                W[x][y][a][b] = Fraction(1, k)
    return W


def cg_of_tensor(sc, W):
    """exact CG coordinates of a no-signalling tensor."""
    d = sc.d
    v = []
    for x in range(2):
        for a in range(d - 1):
            v.append(sum(W[x][0][a][b] for b in range(d)))
    for y in range(2):
        for b in range(d - 1):
            v.append(sum(W[0][y][a][b] for a in range(d)))
    for x in range(2):
        for y in range(2):
            for a in range(d - 1):
                for b in range(d - 1):
                    v.append(W[x][y][a][b])
    return v


def is_deterministic(W, d):
    return all(W[x][y][a][b] in (0, 1) for x in range(2) for y in range(2) for a in range(d) for b in range(d))


def pr_structure(W, d):
    """If W = g.PR_k for an outcome relabelling g (k >= 2), return (k, (al0, al1, be0, be1)) where al_x / be_y are
    permutations of range(d) (actual outcome -> canonical label) and W[x][y][a][b] == PR_k[x][y][al_x[a]][be_y[b]]
    has been verified exactly.  Otherwise return None."""
    SA = [[a for a in range(d) if sum(W[x][0][a][b] for b in range(d)) > 0] for x in range(2)]
    SB = [[b for b in range(d) if sum(W[0][y][a][b] for a in range(d)) > 0] for y in range(2)]
    k = len(SA[0])
    if k < 2 or any(len(s) != k for s in SA + SB):
        return None
    M = {}
    for x in range(2):
        for y in range(2):
            m = {}
            for a in SA[x]:
                nz = [b for b in range(d) if W[x][y][a][b] != 0]
                if len(nz) != 1 or W[x][y][a][nz[0]] != Fraction(1, k):
                    return None
                m[a] = nz[0]
            if sorted(m.values()) != SB[y]:
                return None
            M[(x, y)] = m
    inv10 = {b: a for a, b in M[(1, 0)].items()}
    inv01 = {b: a for a, b in M[(0, 1)].items()}
    h = {a: inv01[M[(1, 1)][inv10[M[(0, 0)][a]]]] for a in SA[0]}
    a0 = SA[0][0]
    orbit = [a0]
    while True:
        nxt = h[orbit[-1]]
        if nxt == a0:
            break
        orbit.append(nxt)
    if len(orbit) != k:
        return None                      # holonomy not a single k-cycle
    al0 = {a: i for i, a in enumerate(orbit)}
    be0 = {M[(0, 0)][a]: al0[a] for a in SA[0]}
    al1 = {a1: be0[M[(1, 0)][a1]] for a1 in SA[1]}
    be1 = {M[(0, 1)][a]: al0[a] for a in SA[0]}
    maps = []
    for lab, used in ((al0, SA[0]), (al1, SA[1]), (be0, SB[0]), (be1, SB[1])):
        full = dict(lab)
        free = [o for o in range(d) if o not in full]
        for j, o in enumerate(free):
            full[o] = k + j
        maps.append([full[o] for o in range(d)])
    al = (maps[0], maps[1])
    be = (maps[2], maps[3])
    P = pr_tensor(d, k)
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    if W[x][y][a][b] != P[x][y][al[x][a]][be[y][b]]:
                        return None
    return k, (maps[0], maps[1], maps[2], maps[3])


def pr_count(d, k):
    """number of generalised PR boxes with k outcomes in the (2,2,d) scenario: C(d,k)^4 (k!)^3 (k-1)!."""
    return math.comb(d, k) ** 4 * math.factorial(k) ** 3 * math.factorial(k - 1)


# ----------------------------------------------------------------------------- facets and violation
def facet_value_exact(F, cgx):
    """h . cg(x) for the facet F = (h0, h) at an exact (Fraction) CG point."""
    h = F.f[1:]
    s = Fraction(0)
    for j, c in enumerate(h):
        if c:
            s += int(c) * cgx[j]
    return s


def violated_known_facet(sc, cgx, reps, sigs, find_g, medium_invariant, tries=20, seed=1):
    """propose (LP ray shooting from u towards the point) a facet of L violated by the exact CG point cgx,
    re-derive it exactly, verify the violation exactly, and identify it with a listed class by an explicit
    relabelling.  Returns (class index, facet, violation h.x - h0 > 0, relabelling) or None."""
    from facet_lib import facet_in_direction
    d = sc.d
    rng = np.random.default_rng(seed)
    base = np.array([float(v) for v in cgx]) - sc.u
    for t in range(tries):
        c = base if t == 0 else base + 1e-3 * rng.normal(size=sc.dim)
        F = facet_in_direction(sc, c)
        if F is None or not F.is_facet():
            continue
        val = facet_value_exact(F, cgx)
        if val <= F.f[0]:
            continue
        sg = medium_invariant(F)
        S2 = F.slack.reshape(d, d, d, d)
        for j, sj in enumerate(sigs):
            if sj == sg:
                g = find_g(reps[j].slack.reshape(d, d, d, d), S2, sc)
                if g is not None:
                    return j, F, val - F.f[0], g
        return -1, F, val - F.f[0], None           # violated facet NOT in the list
    return None
