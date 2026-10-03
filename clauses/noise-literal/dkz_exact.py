"""
dkz_exact.py -- EXACT critical visibility of DKZ_d under Gill noise for small d:  v_c(DKZ_d) = 2/I_ME(d).

(1) Covariant polytope K_d = conv{ (e_{m00}, e_{m01}, e_{m10}, e_{m11}) : m00 - m01 - m10 + m11 = 0 mod d } (link
    difference laws of deterministic strategies), coordinates mu_xy(m), m = 1..d-1 (mu_xy(0) = 1 - sum).  Its complete
    facet list is computed by the exact double description of facets223.py and re-verified (valid + facet-defining).
(2) A Z_d-covariant behaviour P_xy(b-a)/d is local iff (P_xy) in K_d (Lemma 8 for "if"; "only if": twirl a local model).
(3) T^{v*}_xy(m) = v* h_xy(m) + (1 - v*)/d with v* = 2/I_ME(d), h_xy from Lemma 7.  All numbers lie in the field
    Q(c), c = cos(theta), theta = pi/(4d): sin^2(k theta) = (1 - T_{2k}(c))/2, sec(pi j/(2d)) = 1/T_{2j}(c) (Chebyshev).
    Field elements are polynomials in c reduced modulo the minimal polynomial of c; a nonzero element's sign is decided
    by rational interval evaluation at a rigorous enclosure of c (width < 1e-45); zero is decided exactly.
    If every facet is >= 0 at T^{v*}, then T^{v*} is local, so v_c(DKZ_d) >= 2/I_ME(d); with the CGLMP upper bound,
    v_c(DKZ_d) = 2/I_ME(d) exactly.

usage: python dkz_exact.py d [d ...]
"""
import sys
import time
from fractions import Fraction as Fr

import sympy as sp  # only for the minimal polynomial of cos(pi/(4d))

from exact import cos_pi_frac_bounds
from facets223 import double_description, int_rank, normalise

LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
DELTA4 = {(0, 0): 1, (0, 1): -1, (1, 0): 3, (1, 1): 1}        # 4 * delta_xy


# ------------------------------------------------------------------------------------------------------------------
# number field Q(c), c = cos(pi/(4d))
# ------------------------------------------------------------------------------------------------------------------
class Field:
    """Q(c), c = cos(pi/(4d)); elements = coefficient lists [a_0, ..., a_{n-1}] (Fractions) of a_0 + a_1 c + ..."""

    def __init__(self, d):
        self.d = d
        X = sp.symbols("X")
        mp = sp.Poly(sp.minimal_polynomial(sp.cos(sp.pi / (4 * d)), X), X, domain="QQ")
        cf = [Fr(int(t.p), int(t.q)) for t in reversed(mp.all_coeffs())]      # low -> high
        lead = cf[-1]
        self.m = [t / lead for t in cf]                                        # monic
        self.n = len(self.m) - 1
        lo, hi = cos_pi_frac_bounds(Fr(1, 4 * d))
        # round outward to 60 decimals (keeps the enclosure rigorous, makes interval arithmetic fast)
        S = 10 ** 60
        lo = Fr((lo.numerator * S) // lo.denominator, S)
        hi = Fr(-((-hi.numerator * S) // hi.denominator), S)
        self.c_lo, self.c_hi = lo, hi
        assert hi - lo < Fr(1, 10 ** 45)
        f = lambda t: sum(q * t ** k for k, q in enumerate(self.m))
        assert f(lo) * f(hi) < 0, "enclosure must contain a root of m"
        # m(c) = 0 independently of sympy: m divides T_{2d} (exact division), whose roots cos((2k+1) pi/(4d)) are
        # pairwise more than 1e-45 apart, and m changes sign on the enclosure [lo, hi] of c = cos(pi/(4d)) of width
        # < 1e-45; hence the root of m in [lo, hi] is c.  (All later steps only use m(c) = 0: reduction mod m is then
        # evaluation-compatible, inverses are verified by a * z = 1 mod m, signs by interval evaluation.)
        Tq = [Fr(1)], [Fr(0), Fr(1)]
        Tm2, Tm1 = Tq
        for _ in range(2 * d - 1):
            nxt = [Fr(0)] + [2 * x for x in Tm1]
            for i, x in enumerate(Tm2):
                nxt[i] -= x
            Tm2, Tm1 = Tm1, nxt
        rem = list(Tm1)                                   # T_{2d}, low -> high
        for k in range(len(rem) - 1, self.n - 1, -1):     # divide by monic m
            t = rem[k]
            if t:
                for j in range(self.n + 1):
                    rem[k - self.n + j] -= t * self.m[j]
        assert all(x == 0 for x in rem[: self.n]), "m must divide T_{2d}"
        self._cheb = {0: self.const(1), 1: self.reduce([Fr(0), Fr(1)])}

    def const(self, q):
        return [Fr(q)] + [Fr(0)] * (self.n - 1)

    def reduce(self, p):
        p = list(p) + [Fr(0)] * max(0, self.n - len(p))
        for k in range(len(p) - 1, self.n - 1, -1):
            t = p[k]
            if t:
                for j in range(self.n + 1):
                    p[k - self.n + j] -= t * self.m[j]
        return p[: self.n]

    def add(self, a, b):
        return [x + y for x, y in zip(a, b)]

    def scale(self, a, q):
        return [x * q for x in a]

    def mul(self, a, b):
        r = [Fr(0)] * (2 * self.n - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        r[i + j] += x * y
        return self.reduce(r)

    def inv(self, a):
        """solve a * z = 1 (multiplication matrix, exact Gaussian elimination)."""
        n = self.n
        cols = []
        e = self.const(1)
        basis = [[Fr(int(i == j)) for i in range(n)] for j in range(n)]
        M = [self.mul(a, bj) for bj in basis]               # column j = a * c^j
        A = [[M[j][i] for j in range(n)] + [e[i]] for i in range(n)]
        for col in range(n):
            piv = next(r for r in range(col, n) if A[r][col] != 0)
            A[col], A[piv] = A[piv], A[col]
            pv = A[col][col]
            A[col] = [x / pv for x in A[col]]
            for r in range(n):
                if r != col and A[r][col] != 0:
                    f = A[r][col]
                    A[r] = [x - f * y for x, y in zip(A[r], A[col])]
        z = [A[i][n] for i in range(n)]
        assert self.mul(a, z) == self.const(1)
        return z

    def cheb(self, k):
        """T_k(c) = cos(k theta), via T_{k+1} = 2 c T_k - T_{k-1}."""
        k = abs(k)
        c = self._cheb[1]
        while max(self._cheb) < k:
            j = max(self._cheb)
            self._cheb[j + 1] = self.add(self.scale(self.mul(c, self._cheb[j]), 2), self.scale(self._cheb[j - 1], -1))
        return self._cheb[k]

    def interval(self, a):
        lo, hi = Fr(0), Fr(0)
        for q in reversed(a):
            cands = [lo * self.c_lo, lo * self.c_hi, hi * self.c_lo, hi * self.c_hi]
            lo, hi = min(cands) + q, max(cands) + q
        return lo, hi


# ------------------------------------------------------------------------------------------------------------------
def covariant_vertices(d):
    V = []
    for m00 in range(d):
        for m01 in range(d):
            for m10 in range(d):
                ms = (m00, m01, m10, (m01 + m10 - m00) % d)
                v = []
                for i in range(4):
                    v += [int(ms[i] == m) for m in range(1, d)]
                V.append(v)
    return V


def run(d, verbose=True):
    t0 = time.time()
    V = covariant_vertices(d)
    A = [[1] + v for v in V]
    dim = 4 * (d - 1)
    assert int_rank(A) == dim + 1, "K_d full-dimensional"
    rays = double_description(A, verbose=False)
    F = sorted(set(normalise(list(r)) for r in rays))
    # exact re-verification: valid and facet-defining
    for h in F:
        vals = [h[0] + sum(a * b for a, b in zip(h[1:], v)) for v in V]
        assert min(vals) >= 0
        tight = [[1] + v for v, t in zip(V, vals) if t == 0]
        assert int_rank(tight) == dim
    # second DD run with reversed order
    rays2 = double_description(A, order=list(range(len(A)))[::-1], verbose=False)
    assert sorted(set(normalise(list(r)) for r in rays2)) == F
    if verbose:
        print(f"d={d}: K_d has {len(F)} facets (exact DD, two orders, all re-verified) [{time.time() - t0:.1f}s]",
              flush=True)
    K = Field(d)
    one = K.const(1)
    S = K.const(0)
    for j in range(1, d):
        S = K.add(S, K.scale(K.inv(K.cheb(2 * j)), d - j))
    ime = K.scale(S, Fr(4, d * (d - 1)))
    vstar = K.scale(K.inv(ime), 2)
    T = {}
    for xy in LINKS:
        for m in range(d):
            k = 4 * m - DELTA4[xy]
            s2 = K.scale(K.add(one, K.scale(K.cheb(2 * k), -1)), Fr(1, 2))
            h = K.scale(K.inv(s2), Fr(1, 2 * d * d))
            T[(xy, m)] = K.add(K.mul(vstar, h), K.scale(K.add(one, K.scale(vstar, -1)), Fr(1, d)))
    for xy in LINKS:
        tot = K.const(0)
        for m in range(d):
            tot = K.add(tot, T[(xy, m)])
        assert tot == one, "each link distribution sums to 1"
    n = K.n
    Tv = T

    def interval_vec(cs):
        return K.interval(cs)
    nzero, minval = 0, None
    for h in F:
        val = [Fr(h[0])] + [Fr(0)] * (n - 1)
        k = 1
        for i, xy in enumerate(LINKS):
            for m in range(1, d):
                if h[k]:
                    tv = Tv[(xy, m)]
                    val = [a + h[k] * b for a, b in zip(val, tv)]
                k += 1
        if all(x == 0 for x in val):
            nzero += 1
            continue
        lo, hi = interval_vec(val)
        if hi < 0:
            print(f"   facet {h} NEGATIVE at T^v*: {float(lo)}")
            return False
        if lo <= 0:
            raise ValueError("sign undecided")
        minval = lo if minval is None else min(minval, lo)
    if verbose:
        print(f"   field Q(cos(pi/{4 * d})) of degree {K.n}; v* = 2/I_ME({d}) in [{float(K.interval(vstar)[0]):.15f}, "
              f"{float(K.interval(vstar)[1]):.15f}]; all {len(F)} facets >= 0 at T^v* ({nzero} exactly tight, "
              f"smallest positive value >= {float(minval):.3e})  =>  v_c(DKZ_{d}) = 2/I_ME({d}) EXACTLY "
              f"[{time.time() - t0:.1f}s]", flush=True)
    return True


if __name__ == "__main__":
    ok = all(run(int(a)) for a in sys.argv[1:])
    print("RESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
