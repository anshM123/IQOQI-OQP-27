"""
kd_adjacency.py -- exact symmetric adjacency decomposition of the cyclic local polytope K_d (for d where plain double
description is too slow), with the completeness criterion of Theorem V (P3_full_theory/CLOSE_NOTES.md Sec. 2,
Remark (e)): here the role of NS is played by the product of simplices Delta = {Q_i(n) >= 0, sum_n Q_i(n) = 1}, whose
inequalities Q_i(n) >= 0 are the positivity facets of K_d, and whose vertices outside K_d are the points
(e_{n1},...,e_{n4}) with n1+n2+n3+n4 != 0 mod d.

A facet is stored as its primitive integer slack vector on the d^3 vertices of K_d (vertex (n1,n2,n3), n4 = -n1-n2-n3).
Ridges of a facet F: facets of conv(tight(F)) inside aff(F), computed by exact DD (P3_full_theory/IND_dd.py) after an
injective coordinate projection; each ridge functional g is rotated exactly to the unique other facet g + theta*s_F.
Classes: the physical group (zero-sum translations x units x D_4 on the cycle order) acts by vertex permutations
(precomputed); two slack vectors are equivalent iff some permutation maps one onto the other (checked exactly).
(ii) of Theorem V: every vertex of Delta outside K_d strictly violates some listed facet (checked exactly).
usage: python kd_adjacency.py d
"""
import os
import sys
import time
import json
import math
import itertools
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from IND_dd import facets_of_points
from dd_numba import facets_of_points as numba_facets
DDMODE = 'ind'


def vertices(d):
    V = []
    for n1, n2, n3 in itertools.product(range(d), repeat=3):
        V.append((n1, n2, n3, (-n1 - n2 - n3) % d))
    return V


def coords(V, d):
    X = np.zeros((len(V), 4 * (d - 1)), np.int64)
    for k, n in enumerate(V):
        for i in range(4):
            if n[i]:
                X[k, i * (d - 1) + n[i] - 1] = 1
    return X


def group_perms(V, d):
    idx = {v: k for k, v in enumerate(V)}
    units = [u for u in range(1, d) if math.gcd(u, d) == 1]
    cyc = [0, 2, 3, 1]
    perms = set()
    for r in range(4):
        for refl in (False, True):
            order = [cyc[(r + k) % 4] for k in range(4)]
            if refl:
                order = order[::-1]
            p = [None] * 4
            for j in range(4):
                p[cyc[j]] = order[j]
            perms.add(tuple(p))
    out = []
    for p in sorted(perms):
        for u in units:
            for t in itertools.product(range(d), repeat=3):
                tt = t + ((-sum(t)) % d,)
                # facet transform c'_j(n) = c_{p[j]}(u n + t_j); on vertices: s'(n) = s(m) with m_{p[j]} = u n_j + t_j
                perm = np.empty(len(V), np.int64)
                for k, n in enumerate(V):
                    m = [0] * 4
                    for j in range(4):
                        m[p[j]] = (u * n[j] + tt[j]) % d
                    perm[k] = idx[tuple(m)]
                out.append(perm)
    return np.array(out)


def primitive(s):
    g = 0
    for v in s:
        g = math.gcd(g, int(abs(v)))
    return np.array([int(v) // g for v in s], dtype=np.int64)


def facet_from_table(c, c0, V):
    return primitive([c0 - sum(c[i][n[i]] for i in range(4)) for n in V])


def table_from_slack(s, X, V, d):
    """recover (c, c0) with c_i(0) = 0 from a slack vector: s = h0 + h.X  (exact least-squares-free solve)."""
    A = np.hstack([np.ones((len(V), 1), np.int64), X]).astype(float)
    sol, *_ = np.linalg.lstsq(A, s.astype(float), rcond=None)
    h0 = sol[0]; h = sol[1:]
    c = np.zeros((4, d))
    for i in range(4):
        c[i, 1:] = -h[i * (d - 1):(i + 1) * (d - 1)]
    return c, h0


class Classifier:
    def __init__(self, perms):
        self.perms = perms
        self.reps = []            # list of slack vectors
        self.keys = []            # invariant keys

    @staticmethod
    def key(s):
        vals, cnt = np.unique(s, return_counts=True)
        return tuple(zip(vals.tolist(), cnt.tolist()))

    def find(self, s):
        k = self.key(s)
        for j, (r, kr) in enumerate(zip(self.reps, self.keys)):
            if kr != k:
                continue
            imgs = s[self.perms]                  # all images s o perm
            if np.any(np.all(imgs == r[None, :], axis=1)):
                return j
        return None

    def add(self, s):
        self.reps.append(s)
        self.keys.append(self.key(s))
        return len(self.reps) - 1

    def orbit(self, s):
        imgs = s[self.perms]
        return np.unique(imgs, axis=0)


def ridges_and_neighbours(s, X, d):
    T = np.where(s == 0)[0]
    n = X.shape[1]
    # hyperplane: s = h0 + h.X ; find coordinate j with h_j != 0 to drop
    A = np.hstack([np.ones((len(s), 1)), X.astype(float)])
    sol, *_ = np.linalg.lstsq(A, s.astype(float), rcond=None)
    j = int(np.argmax(np.abs(sol[1:])))
    keep = [c for c in range(n) if c != j]
    PT = X[T][:, keep]
    if DDMODE == 'numba':
        outn = numba_facets([list(map(int, p)) for p in PT])
        R = np.array([r for (r, tight) in outn], dtype=np.int64)
        info = {}
    else:
        R, Z, info = facets_of_points(PT, nthreads=2, verbose=False)
    neigh = []
    off = np.where(s > 0)[0]
    Xk = X[:, keep]
    for r in R:
        g = r[0] + Xk @ r[1:]                        # ridge functional extended to all vertices (integer)
        assert (g[T] >= 0).all()
        # rotate: g + theta s >= 0 on all vertices with equality on a new vertex
        ratios = [(-int(g[v]), int(s[v])) for v in off]        # theta = max over ALL off-facet vertices (may be <= 0)
        from fractions import Fraction
        best = max(ratios, key=lambda t: Fraction(t[0], t[1]))
        num, den = best
        nb = den * g.astype(object) + num * s.astype(object)
        nb = primitive(nb)
        assert (nb >= 0).all()
        neigh.append(nb)
    return neigh, len(R), info


if __name__ == "__main__":
    d = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == 'numba':
        DDMODE = 'numba'
    t0 = time.time()
    V = vertices(d)
    X = coords(V, d)
    perms = group_perms(V, d)
    print(f"d={d}: {len(V)} vertices, group {len(perms)} [{time.time()-t0:.0f}s]", flush=True)
    clf = Classifier(perms)
    # seeds: positivity (Q_1(1) >= 0) and CGLMP_d
    pos = primitive([1 if n[0] == 1 else 0 for n in V])
    # CGLMP_d in cycle coordinates: f(n) = (-n) mod d, c_1 = c_2 = c_3 = -f, c_4(m) = f(-m)
    f = [(-n) % d for n in range(d)]
    c_cg = [[-f[n] for n in range(d)]] * 3 + [[f[(-m) % d] for m in range(d)]]
    cg = facet_from_table(c_cg, 0, V)
    assert (cg >= 0).all() and (pos >= 0).all()
    ipos = clf.add(pos)
    queue = [clf.add(cg)]
    expanded = set()
    adj = {}
    while queue:
        j = queue.pop(0)
        if j == ipos or j in expanded:
            continue
        s = clf.reps[j]
        tt = time.time()
        neigh, nr, info = ridges_and_neighbours(s, X, d)
        counts = {}
        for nb in neigh:
            k = clf.find(nb)
            if k is None:
                k = clf.add(nb)
                queue.append(k)
                print(f"   new class {k}: tight {int((nb == 0).sum())}", flush=True)
            counts[k] = counts.get(k, 0) + 1
        expanded.add(j)
        adj[j] = counts
        print(f"class {j}: tight {int((s == 0).sum())}, {nr} ridges, neighbour classes {counts} "
              f"[{time.time()-tt:.0f}s, total {time.time()-t0:.0f}s]", flush=True)
    # (ii) every vertex of Delta outside K_d violates a listed facet
    allf = np.vstack([clf.orbit(r) for r in clf.reps])
    # exact affine coefficients: choose an affinely independent vertex subset B (square), coeffs*det(B) = adj(B) s[rows]
    import flint
    A_int = np.hstack([np.ones((len(V), 1), np.int64), X])
    rows = []
    for k in range(len(V)):
        if np.linalg.matrix_rank(A_int[rows + [k]].astype(float)) > len(rows):
            rows.append(k)
        if len(rows) == A_int.shape[1]:
            break
    Bm = flint.fmpz_mat([[int(v) for v in A_int[k]] for k in rows])
    detB = int(Bm.det())
    assert detB != 0
    Binv = Bm.inv()
    nB = len(rows)
    adjB_int = np.array([[int((Binv[i, j] * detB).p) for j in range(nB)] for i in range(nB)], dtype=np.int64)
    assert all((Binv[i, j] * detB).q == 1 for i in range(nB) for j in range(nB))
    coeffs = (adjB_int @ allf[:, rows].T).T                     # = detB * (h0, h)
    assert np.abs(coeffs).max() < 2 ** 40
    assert np.array_equal(A_int @ coeffs.T, detB * allf.T), "slack reconstruction failed"
    tables = coeffs * (1 if detB > 0 else -1)              # positive multiple of (h0, h)
    bad = 0
    for n in itertools.product(range(d), repeat=4):
        if sum(n) % d == 0:
            continue
        x = np.zeros(4 * (d - 1), np.int64)
        for i in range(4):
            if n[i]:
                x[i * (d - 1) + n[i] - 1] = 1
        vals = tables[:, 0] + tables[:, 1:] @ x
        if not (vals < 0).any():
            bad += 1
    sizes = [len(clf.orbit(r)) for r in clf.reps]
    print(f"classes {len(clf.reps)} (sizes {sizes}, total {sum(sizes)}); positivity class {ipos} not expanded; "
          f"Delta-vertices outside K_d violating no listed facet: {bad}")
    print("COMPLETE (Theorem V)" if bad == 0 else "NOT COMPLETE")
    out = []
    for j, r in enumerate(clf.reps):
        c, c0 = table_from_slack(r, X, V, d)
        out.append({"size": sizes[j], "tight": int((r == 0).sum()), "slack": r.tolist(),
                    "c_float": np.round(c, 6).tolist(), "c0_float": float(c0), "adj": {str(k): v for k, v in adj.get(j, {}).items()}})
    json.dump(out, open(f"kd_adj_d{d}{'_numba' if DDMODE == 'numba' else ''}.json", "w"))
