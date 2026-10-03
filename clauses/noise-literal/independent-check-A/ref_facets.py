"""
ref_facets.py -- independent re-computation of the facets of L(2,2,3) (referee check of Lemma 4 / item C1).

Independent of P2's facets223.py:
  * different coordinates: Collins-Gisin coordinates that DROP OUTCOME 0 (keep outcomes 1, 2), different ordering;
  * own double-description code, ALGEBRAIC adjacency test (rank of the common active rows = n - 2, computed mod a
    61-bit prime and confirmed exactly over Q when the modular rank is deficient), random insertion orders;
  * comparison with P2's facets223.txt through the coordinate-free invariant "set of tight deterministic strategies"
    (a facet of a full-dimensional polytope is determined by its vertex set);
  * spot checks: the Collins-Gisin matrix I2233 (J. Phys. A 37, 1775 (2004), eq. (39)) and the coarse-grained CHSH.
usage: python ref_facets.py
"""
import itertools
import random
import sys
import time
from fractions import Fraction
from math import gcd

OUT = (0, 1, 2)
STRATS = list(itertools.product(OUT, repeat=4))            # (a0, a1, b0, b1)
KEEP = (1, 2)                                              # CG outcomes kept (outcome 0 dropped)
PRIME = (1 << 61) - 1


def coords(s):
    """my CG coordinates: [pAB(a,b|x,y) for x,y,a,b] + [pA(a|x)] + [pB(b|y)], a, b in KEEP."""
    a, b = (s[0], s[1]), (s[2], s[3])
    v = []
    for x in range(2):
        for y in range(2):
            for i in KEEP:
                for j in KEEP:
                    v.append(int(a[x] == i and b[y] == j))
    for x in range(2):
        for i in KEEP:
            v.append(int(a[x] == i))
    for y in range(2):
        for j in KEEP:
            v.append(int(b[y] == j))
    return v


def rank_mod(rows, p=PRIME):
    M = [[x % p for x in r] for r in rows]
    rk, ncol = 0, len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [x * inv % p for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]
                M[i] = [(x - f * y) % p for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk


def rank_exact(rows):
    M = [[Fraction(x) for x in r] for r in rows]
    rk, ncol = 0, len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(rk + 1, len(M)):
            if M[i][c] != 0:
                f = M[i][c] / M[rk][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk


def prim(v):
    g = 0
    for t in v:
        g = gcd(g, abs(t))
    return tuple(t // g for t in v) if g else tuple(v)


def initial_cone(A, order):
    n = len(A[0])
    K = []
    for i in order:
        if rank_exact([A[j] for j in K + [i]]) == len(K) + 1:
            K.append(i)
        if len(K) == n:
            break
    B = [[Fraction(x) for x in A[i]] for i in K]
    # invert B (Gauss-Jordan)
    M = [row + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(B)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    rays = []
    for j in range(n):
        col = [M[i][n + j] for i in range(n)]
        den = 1
        for t in col:
            den = den * t.denominator // gcd(den, t.denominator)
        rays.append(prim([int(t * den) for t in col]))
    # sanity: B r_j = positive multiple of e_j
    for j, r in enumerate(rays):
        vals = [sum(a * b for a, b in zip(A[i], r)) for i in K]
        assert all(v == 0 for k, v in enumerate(vals) if k != j) and vals[j] > 0
    return K, rays


def dd(A, order):
    n = len(A[0])
    K, rays = initial_cone(A, order)
    processed = list(K)
    dot = lambda i, r: sum(a * b for a, b in zip(A[i], r))
    zmask = lambda r: sum(1 << i for i in processed if dot(i, r) == 0)
    R = [(r, zmask(r)) for r in rays]
    for i in order:
        if i in K:
            continue
        s = [dot(i, r) for r, _ in R]
        pos = [k for k in range(len(R)) if s[k] > 0]
        neg = [k for k in range(len(R)) if s[k] < 0]
        zer = [k for k in range(len(R)) if s[k] == 0]
        new = []
        for kp in pos:
            zp = R[kp][1]
            for kn in neg:
                S = zp & R[kn][1]
                if bin(S).count("1") < n - 2:
                    continue
                rows = [A[j] for j in processed if (S >> j) & 1]
                rk = rank_mod(rows)
                if rk < n - 2:
                    rk = rank_exact(rows)          # modular rank can only under-estimate
                if rk != n - 2:
                    continue
                r = prim([s[kp] * a - s[kn] * b for a, b in zip(R[kn][0], R[kp][0])])
                new.append((r, S | (1 << i)))
        R = [R[k] for k in pos] + [(R[k][0], R[k][1] | (1 << i)) for k in zer] + new
        processed.append(i)
    return [r for r, _ in R]


def tight_set(f, V):
    return frozenset(k for k, v in enumerate(V) if f[0] + sum(a * b for a, b in zip(f[1:], v)) == 0)


def is_facet(f, V):
    vals = [f[0] + sum(a * b for a, b in zip(f[1:], v)) for v in V]
    if min(vals) < 0:
        return False
    tight = [[1] + list(v) for v, t in zip(V, vals) if t == 0]
    return rank_exact(tight) == len(V[0])


def p2_tight_sets(fn):
    """P2 file: h0 + h.x >= 0 with x = [pA(a|x) (x,a), pB(b|y) (y,b), pAB(a,b|x,y) (x,y,a,b)], a, b in {0,1}.
    Evaluated directly on deterministic strategies (my own reading of the documented layout)."""
    out = {}
    for line in open(fn):
        if line.startswith("#"):
            continue
        h, cls = line.split(";")
        h = [int(t) for t in h.split()]
        cls = cls.strip()
        assert len(h) == 25
        tight = []
        mn = None
        for k, s in enumerate(STRATS):
            a, b = (s[0], s[1]), (s[2], s[3])
            val = h[0]
            idx = 1
            for x in range(2):
                for i in range(2):
                    val += h[idx] * (a[x] == i)
                    idx += 1
            for y in range(2):
                for j in range(2):
                    val += h[idx] * (b[y] == j)
                    idx += 1
            for x in range(2):
                for y in range(2):
                    for i in range(2):
                        for j in range(2):
                            val += h[idx] * (a[x] == i and b[y] == j)
                            idx += 1
            mn = val if mn is None else min(mn, val)
            if val == 0:
                tight.append(k)
        assert mn >= 0, "P2 inequality invalid on a deterministic point"
        out[frozenset(tight)] = cls
    return out


def full_functional_tight(beta, bound):
    """tight set and validity of sum beta(x,y,a,b) p(a,b|x,y) <= bound on deterministic strategies."""
    vals = []
    for s in STRATS:
        a, b = (s[0], s[1]), (s[2], s[3])
        vals.append(bound - sum(beta.get((x, y, a[x], b[y]), 0) for x in range(2) for y in range(2)))
    return min(vals) >= 0, frozenset(k for k, v in enumerate(vals) if v == 0)


def main():
    t0 = time.time()
    V = [coords(s) for s in STRATS]
    A = [[1] + v for v in V]
    assert rank_exact(A) == 25
    results = []
    orders = [list(range(81))]
    rng = random.Random(2026)
    for _ in range(2):
        o = list(range(81))
        rng.shuffle(o)
        orders.append(o)
    for o in orders:
        t1 = time.time()
        rays = dd(A, o)
        F = set(prim(list(r)) for r in rays)
        results.append(F)
        print(f"DD order {o[:6]}...: {len(rays)} rays, {len(F)} distinct, {time.time() - t1:.1f}s", flush=True)
    same = all(F == results[0] for F in results)
    F = results[0]
    nbad = sum(1 for f in F if not is_facet(f, V))
    print(f"all orders agree: {same}; exact facet check failures: {nbad}")
    mine = {tight_set(f, V): f for f in F}
    assert len(mine) == len(F)
    theirs = p2_tight_sets(sys.argv[1] if len(sys.argv) > 1 else "../facets223.txt")
    print(f"P2 list: {len(theirs)} facets; mine: {len(mine)}; identical tight-set families: {set(mine) == set(theirs)}")
    from collections import Counter
    print("P2 classes:", Counter(theirs.values()))
    # tight-set sizes per class
    sizes = Counter((theirs[T], len(T)) for T in theirs)
    print("tight-set sizes by class:", dict(sizes))
    # spot check 1: Collins-Gisin I2233 (eq. 39), CG form with outcomes {0,1} kept; I2233 <= 0 for LHV.
    # first row: Alice marginals A1=0, A1=1, A2=0, A2=1; first column: Bob marginals B1=0, B1=1, B2=0, B2=1.
    alice = [-1, -1, 0, 0]
    bob = [-1, -1, 0, 0]
    corr = [[1, 1, 0, 1],
            [1, 0, 1, 1],
            [0, 1, 0, -1],
            [1, 1, -1, -1]]
    vals = []
    for s in STRATS:
        a, b = (s[0], s[1]), (s[2], s[3])
        pa = [int(a[0] == 0), int(a[0] == 1), int(a[1] == 0), int(a[1] == 1)]
        pb = [int(b[0] == 0), int(b[0] == 1), int(b[1] == 0), int(b[1] == 1)]
        val = sum(alice[i] * pa[i] for i in range(4)) + sum(bob[j] * pb[j] for j in range(4)) + \
            sum(corr[j][i] * pa[i] * pb[j] for i in range(4) for j in range(4))
        vals.append(val)
    T = frozenset(k for k, v in enumerate(vals) if v == 0)
    print(f"Collins-Gisin I2233: max over LHV = {max(vals)} (should be 0); tight set is a facet in P2 list: "
          f"{T in theirs} ({theirs.get(T)}); |tight| = {len(T)}")
    # spot check 2: coarse-grained CHSH ({0} vs {1,2}, signs (+,+,+,-))
    sgn = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    beta = {}
    for x, y in sgn:
        for a in OUT:
            for b in OUT:
                beta[(x, y, a, b)] = sgn[(x, y)] * (1 if a == 0 else -1) * (1 if b == 0 else -1)
    ok, T = full_functional_tight(beta, 2)
    print(f"coarse-grained CHSH valid: {ok}; in P2 list: {T in theirs} ({theirs.get(T)}); |tight| = {len(T)}")
    # spot check 3: CGLMP_3 in the BRIEF form (I_3 <= 2)
    beta = {}
    d = 3
    for a in OUT:
        for b in OUT:
            def add(x, y, w):
                beta[(x, y, a, b)] = beta.get((x, y, a, b), 0) + w
            k = 0
            if (a - b - k) % d == 0: add(0, 0, 1)
            if (b - a - k - 1) % d == 0: add(1, 0, 1)
            if (a - b - k) % d == 0: add(1, 1, 1)
            if (b - a - k) % d == 0: add(0, 1, 1)
            if (a - b + k + 1) % d == 0: add(0, 0, -1)
            if (b - a + k) % d == 0: add(1, 0, -1)
            if (a - b + k + 1) % d == 0: add(1, 1, -1)
            if (b - a + k + 1) % d == 0: add(0, 1, -1)
    ok, T = full_functional_tight(beta, 2)
    print(f"CGLMP_3 (BRIEF form) valid: {ok}; in P2 list: {T in theirs} ({theirs.get(T)}); |tight| = {len(T)}")
    good = same and nbad == 0 and set(mine) == set(theirs) and len(mine) == 1116
    print(f"RESULT: {'PASS' if good else 'FAIL'}  ({time.time() - t0:.0f}s)")


if __name__ == "__main__":
    main()
