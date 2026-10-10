"""
facet_lib.py -- exact facet machinery for the (2,2,d) local polytope L in Collins-Gisin (CG) coordinates.

CG coordinates (dimension 4 d (d-1)):  pA(a|x), a < d-1 (x = 0,1);  pB(b|y), b < d-1;  p(ab|xy), a, b < d-1.
Deterministic points lam = (a0, a1, b0, b1) in the order of itertools.product(range(d), repeat=4).
A facet is stored as a primitive integer vector f = (h0, h) with  h . v <= h0  on L, tight on an affinely
independent set of dim(L) = 4d(d-1) vertices.  All facet data are recomputed EXACTLY (python integers /
Fractions) from the combinatorial tight set; floating point is used only to find candidates.

Symmetry group G of L (order 8 (d!)^4): outcome relabellings of each of the 4 measurements, swaps of the two
settings of a party, and the party swap.  Facets are classified by a G-invariant hash of the slack tensor
s[a0,a1,b0,b1] = h0 - h . v(lam) (exact integers), and the orbit size is |G| / |Stab|.
"""
import itertools
import math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog


# ----------------------------------------------------------------------------- coordinates
class Scenario:
    def __init__(self, d):
        self.d = d
        self.lams = np.array(list(itertools.product(range(d), repeat=4)))      # a0 a1 b0 b1
        self.dim = 4 * d * (d - 1)
        self.V = np.array([self.cg_point(l) for l in self.lams], dtype=np.int64)   # (d^4, dim)
        self.u = self.cg_of_full(np.full((2, 2, d, d), 1.0 / d ** 2))
        self._axis_perms = None

    def cg_index(self):
        d = self.d
        idx = {}
        k = 0
        for x in range(2):
            for a in range(d - 1):
                idx[('A', x, a)] = k; k += 1
        for y in range(2):
            for b in range(d - 1):
                idx[('B', y, b)] = k; k += 1
        for x in range(2):
            for y in range(2):
                for a in range(d - 1):
                    for b in range(d - 1):
                        idx[('AB', x, y, a, b)] = k; k += 1
        return idx

    def cg_point(self, lam):
        d = self.d
        a = (lam[0], lam[1]); b = (lam[2], lam[3])
        v = []
        for x in range(2):
            for aa in range(d - 1):
                v.append(1 if a[x] == aa else 0)
        for y in range(2):
            for bb in range(d - 1):
                v.append(1 if b[y] == bb else 0)
        for x in range(2):
            for y in range(2):
                for aa in range(d - 1):
                    for bb in range(d - 1):
                        v.append(1 if (a[x] == aa and b[y] == bb) else 0)
        return v

    def cg_of_full(self, p):
        """full behaviour p[x,y,a,b] (no-signalling) -> CG coordinates (float)."""
        d = self.d
        v = []
        for x in range(2):
            for aa in range(d - 1):
                v.append(p[x, 0, aa, :].sum())
        for y in range(2):
            for bb in range(d - 1):
                v.append(p[0, y, :, bb].sum())
        for x in range(2):
            for y in range(2):
                for aa in range(d - 1):
                    for bb in range(d - 1):
                        v.append(p[x, y, aa, bb])
        return np.array(v, dtype=float)

    def full_coeffs(self, f):
        """facet f = (h0, h) in CG coords -> coefficient tensor C[x,y,a,b] on full probabilities (NS points)
        with  h . cg(p) = sum C p  (using pA(a|x) = sum_b p(ab|x,0), pB(b|y) = sum_a p(ab|0,y))."""
        d = self.d
        h0, h = f[0], f[1:]
        idx = self.cg_index()
        C = np.zeros((2, 2, d, d), dtype=object)
        C[:] = 0
        for x in range(2):
            for aa in range(d - 1):
                C[x, 0, aa, :] += h[idx[('A', x, aa)]]
        for y in range(2):
            for bb in range(d - 1):
                C[0, y, :, bb] += h[idx[('B', y, bb)]]
        for x in range(2):
            for y in range(2):
                for aa in range(d - 1):
                    for bb in range(d - 1):
                        C[x, y, aa, bb] += h[idx[('AB', x, y, aa, bb)]]
        return C, h0

    # ------------------------------------------------------------------ symmetry
    def axis_perms(self):
        """the 8 setting/party symmetries as permutations of the 4 axes (a0,a1,b0,b1)."""
        out = []
        for party in (False, True):
            for sa in (False, True):
                for sb in (False, True):
                    ax = [0, 1, 2, 3]
                    if sa:
                        ax[0], ax[1] = ax[1], ax[0]
                    if sb:
                        ax[2], ax[3] = ax[3], ax[2]
                    if party:
                        ax = [ax[2], ax[3], ax[0], ax[1]]
                    out.append(tuple(ax))
        return out

    def group_order(self):
        return 8 * math.factorial(self.d) ** 4


# ----------------------------------------------------------------------------- exact linear algebra
def exact_rank(rows):
    """rank of an integer matrix (list of lists) by fraction-free Gaussian elimination."""
    M = [list(map(int, r)) for r in rows]
    if not M:
        return 0
    n, m = len(M), len(M[0])
    rank = 0
    col = 0
    prev = 1
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
                M[i] = [(a * M[i][j] - b * M[rank][j]) // prev if False else (a * M[i][j] - b * M[rank][j])
                        for j in range(m)]
                g = 0
                for t in M[i]:
                    g = math.gcd(g, t)
                if g > 1:
                    M[i] = [t // g for t in M[i]]
        rank += 1
        if rank == n:
            break
    return rank


def affine_rank(P):
    P = [list(map(int, r)) for r in P]
    if len(P) <= 1:
        return 0
    base = P[0]
    return exact_rank([[a - b for a, b in zip(r, base)] for r in P[1:]])


def nullspace_1d(rows):
    """fast path: float SVD + integer reconstruction, verified exactly; falls back to exact elimination."""
    A = np.array(rows, dtype=float)
    try:
        _, sv, Vt = np.linalg.svd(A)
        n = A.shape[1]
        rank = int(np.sum(sv > 1e-8 * max(1.0, sv[0])))
        if rank == n - 1:
            v = Vt[-1]
            nz = np.abs(v[np.abs(v) > 1e-9])
            v = v / nz.min()
            for mult in range(1, 121):
                w = v * mult
                wi = np.round(w)
                if np.max(np.abs(w - wi)) < 1e-6:
                    wi = wi.astype(np.int64)
                    Ai = np.array(rows, dtype=np.int64)
                    if not np.any(Ai @ wi):
                        g = int(np.gcd.reduce(np.abs(wi[wi != 0])))
                        return [int(x) // g for x in wi]
                    break
    except np.linalg.LinAlgError:
        pass
    return nullspace_1d_exact(rows)


def nullspace_1d_exact(rows):
    """integer matrix with a 1-dimensional rational nullspace -> primitive integer nullspace vector
    (raises if the nullspace dimension is not 1)."""
    M = [[Fraction(int(x)) for x in r] for r in rows]
    n, m = len(M), len(M[0])
    piv_cols = []
    r = 0
    for c in range(m):
        piv = None
        for i in range(r, n):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(n):
            if i != r and M[i][c] != 0:
                fac = M[i][c]
                M[i] = [a - fac * b for a, b in zip(M[i], M[r])]
        piv_cols.append(c)
        r += 1
        if r == n:
            break
    free = [c for c in range(m) if c not in piv_cols]
    if len(free) != 1:
        raise ValueError(f"nullspace dimension {len(free)} != 1")
    fc = free[0]
    v = [Fraction(0)] * m
    v[fc] = Fraction(1)
    for i, c in enumerate(piv_cols):
        v[c] = -M[i][fc]
    den = 1
    for x in v:
        den = den * x.denominator // math.gcd(den, x.denominator)
    w = [int(x * den) for x in v]
    g = 0
    for x in w:
        g = math.gcd(g, x)
    return [x // g for x in w]


# ----------------------------------------------------------------------------- facets
class Facet:
    """primitive integer facet (h0, h): h . v <= h0 on all deterministic points."""

    def __init__(self, sc, f):
        self.sc = sc
        self.f = tuple(int(x) for x in f)
        h0 = self.f[0]
        if max(abs(x) for x in self.f) < 2 ** 40:
            self.slack = h0 - sc.V @ np.array(self.f[1:], dtype=np.int64)
        else:
            h = np.array(self.f[1:], dtype=object)
            self.slack = np.array([h0 - int(np.dot(h, v)) for v in sc.V.tolist()], dtype=np.int64)
        if self.slack.min() < 0:
            raise ValueError("not valid")
        self.tight = np.where(self.slack == 0)[0]

    def is_facet(self, exact=True):
        if not exact:
            P = self.sc.V[self.tight].astype(float)
            return np.linalg.matrix_rank(P[1:] - P[0], tol=1e-8) == self.sc.dim - 1
        return affine_rank(self.sc.V[self.tight].tolist()) == self.sc.dim - 1

    def value(self, cgp):
        return float(np.dot(np.array(self.f[1:], float), cgp)), self.f[0]


def facet_from_tight(sc, tight):
    """exact hyperplane through the CG points V[tight] (must have affine rank dim-1); oriented so that all
    deterministic points satisfy h . v <= h0.  Returns Facet."""
    rows = [list(sc.V[i]) + [-1] for i in tight]
    w = nullspace_1d(rows)          # h . v - h0 = 0  ->  w = (h, h0)
    h, h0 = w[:-1], w[-1]
    vals = sc.V @ np.array(h, dtype=np.int64)
    s = h0 - vals
    if s.min() < 0 and s.max() > 0:
        raise ValueError("hyperplane through tight set is not valid (not a face)")
    if s.max() <= 0:
        h = [-x for x in h]
        h0 = -h0
    return Facet(sc, [h0] + list(h))


def facet_in_direction(sc, c, rng=None):
    """ray shooting from u: maximise c . g over the polar {g : g . (v - u) <= 1} -> vertex = facet."""
    V = sc.V.astype(float) - sc.u[None, :]
    m = V.shape[0]
    res = linprog(-c, A_ub=V, b_ub=np.ones(m), bounds=[(None, None)] * sc.dim, method="highs-ds",
                  options=dict(time_limit=2.0))
    if res.status != 0:
        return None
    g = res.x
    vals = V @ g
    tight = np.where(vals > 1 - 1e-7)[0]
    try:
        F = facet_from_tight(sc, tight)
    except ValueError:
        return None
    if not F.is_facet(exact=False):
        return None
    return F


def random_ridge_neighbour(F, rng):
    """random ridge of F (ray shooting inside aff F from the barycentre of its vertices) and the facet F'
    adjacent to F through that ridge (exact rotation).  Returns (F', ridge_tight) or None."""
    sc = F.sc
    h = np.array(F.f[1:], float)
    W = sc.V[F.tight].astype(float)
    mode = rng.integers(3)
    if mode == 0:
        cF = W.mean(axis=0)
    else:
        wts = rng.exponential(size=len(W)) ** 3
        cF = (wts / wts.sum()) @ W
    Wc = W - cF[None, :]
    if mode == 2:
        k = int(rng.integers(1, min(12, len(W))))
        S = rng.choice(len(W), size=k, replace=False)
        delta = Wc[S].sum(axis=0) + 1e-3 * rng.normal(size=sc.dim)
    else:
        delta = rng.normal(size=sc.dim)
    delta -= h * (delta @ h) / (h @ h)
    # polar of F inside aff F: g . (w - cF) <= 1, g orthogonal to h; solved in a basis of h^perp
    # (the equality-constrained form makes the dual simplex stall on degenerate facets)
    _, _, Vt = np.linalg.svd(h[None, :])
    Bp = Vt[1:].T
    res = linprog(-(Bp.T @ delta), A_ub=Wc @ Bp, b_ub=np.ones(len(W)),
                  bounds=[(None, None)] * Bp.shape[1], method="highs-ds", options=dict(time_limit=0.5))
    if res.status != 0:
        return None
    g = Bp @ res.x
    vals = Wc @ g
    rloc = np.where(vals > 1 - 1e-7)[0]
    ridge = F.tight[rloc]
    Pr = sc.V[ridge].astype(float)
    if np.linalg.matrix_rank(Pr[1:] - Pr[0], tol=1e-8) != sc.dim - 2:
        return None
    # exact ridge inequality within aff F: find integer (g0, g) through the ridge points and one extra tight
    # direction -- equivalently rotate: candidates F' = hyperplane through ridge + one outside vertex.
    # exact rotation: theta* = max over v not in F of (gv - g0)/(h0 - hv), using an exact g through the ridge.
    rows = [list(sc.V[i]) + [-1] for i in ridge] + [list(map(int, F.f[1:])) + [0]]   # g orthogonal-ish fix
    try:
        w = nullspace_1d(rows)
    except ValueError:
        return None
    gv, g0 = np.array(w[:-1], dtype=object), w[-1]
    # orient g so that g . w <= g0 on F's vertices
    sF = [g0 - int(np.dot(gv, sc.V[i])) for i in F.tight]
    if min(sF) < 0:
        gv = -gv; g0 = -g0
        sF = [-x for x in sF]
    if min(sF) < 0:
        return None
    h0 = F.f[0]
    hv = np.array(F.f[1:], dtype=np.int64)
    gvi = np.array([int(x) for x in gv], dtype=np.int64)
    sh = h0 - sc.V @ hv
    num = sc.V @ gvi - int(g0)
    best = None
    for i in np.where(sh != 0)[0]:
        r = Fraction(int(num[i]), int(sh[i]))
        if best is None or r > best:
            best = r
    # F' : (g + theta h) . v <= g0 + theta h0
    th = best
    newh = [Fraction(int(a)) + th * int(b) for a, b in zip(gv, hv)]
    newh0 = Fraction(int(g0)) + th * h0
    den = 1
    for x in newh + [newh0]:
        den = den * x.denominator // math.gcd(den, x.denominator)
    vec = [int(x * den) for x in [newh0] + newh]
    gg = 0
    for x in vec:
        gg = math.gcd(gg, x)
    vec = [x // gg for x in vec]
    try:
        Fp = Facet(sc, vec)
    except ValueError:
        return None
    if not Fp.is_facet(exact=False):
        return None
    return Fp, ridge


# ----------------------------------------------------------------------------- classification
class Classifier:
    """G-invariant hash of slack tensors + stabiliser sizes (exhaustive over G, vectorised)."""

    def __init__(self, sc, seed=12345):
        self.sc = sc
        d = sc.d
        rng = np.random.default_rng(seed)
        self.w = rng.random(d ** 4)
        self.perms = np.array(list(itertools.permutations(range(d))))
        # index arrays for permuting axes 2,3 jointly: for each (p2,p3) the flattened index map on (b0,b1)
        P = len(self.perms)
        self.idx23 = np.zeros((P * P, d * d), dtype=np.int64)
        k = 0
        for p2 in self.perms:
            for p3 in self.perms:
                self.idx23[k] = (p2[:, None] * d + p3[None, :]).reshape(-1)
                k += 1

    def _orbit_values(self, s, want_stab=False, target=None):
        """iterate over the group: yields hash values (and stabiliser count if want_stab)."""
        d = self.sc.d
        S = s.reshape(d, d, d, d)
        best = np.inf
        stab = 0
        for ax in self.sc.axis_perms():
            T = np.transpose(S, ax)
            for p0 in self.perms:
                for p1 in self.perms:
                    U = T[p0][:, p1].reshape(d * d, d * d)        # rows (a0,a1), cols (b0,b1)
                    # apply all (p2,p3) column permutations: V[k, r, c] = U[r, idx23[k, c]]
                    Vk = U[:, self.idx23]                            # (d*d, P*P, d*d)
                    Vk = np.transpose(Vk, (1, 0, 2)).reshape(len(self.idx23), -1)
                    vals = Vk @ self.w
                    m = vals.min()
                    if m < best:
                        best = m
                    if want_stab:
                        stab += int(np.sum(np.all(Vk == s[None, :], axis=1)))
        return best, stab

    def key(self, F):
        best, _ = self._orbit_values(F.slack.astype(float))
        return round(float(best), 9)

    def key_and_stab(self, F):
        best, stab = self._orbit_values(F.slack.astype(float), want_stab=True)
        return round(float(best), 9), stab
