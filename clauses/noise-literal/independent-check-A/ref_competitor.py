"""
ref_competitor.py -- referee re-derivation of Theorem 1(a) (competitor C_d), independent of P2's code.

 A. competitor behaviour from the explicit projectors (own exact Q(sqrt2) matrices), d = 3..12, compared with Lemma 1.
 B. Proposition 5 for ALL d >= 3 with a different certificate: for every facet F (my own facet list from
    ref_facets.dd, my coordinates), G_F(t) = f_c(n_t) f(q_t) - f(n_t) f_c(q_t) is shown >= 0 on [0, 1/3] by exact real
    root isolation of the norm polynomial N = G * conj(G) in Q[t] (sympy) + exact sign tests of G between roots.
 C. explicit EXACT local models at v* for d = 3..24 (both constructions): decomposition of the coarse-grained point
    q_{v*} into deterministic strategies of L(2,2,3) with weights in Q(sqrt2), checked exactly (no facet list used),
    lifted to a local model of the full d-outcome behaviour (Lemma 3 post-processing) and checked exactly for d = 4, 5.
usage: python ref_competitor.py
"""
import itertools
import sys
import time
from fractions import Fraction as Fr

import numpy as np
import sympy as sp
from scipy.optimize import linprog

import ref_facets as RF


# ------------------------------------------------------------------------------------------------------------------
class K:
    """a + b sqrt2, a, b rational (own minimal implementation)."""
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a, self.b = Fr(a), Fr(b)

    @staticmethod
    def of(x):
        return x if isinstance(x, K) else K(x)

    def __add__(s, o):
        o = K.of(o)
        return K(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __sub__(s, o):
        o = K.of(o)
        return K(s.a - o.a, s.b - o.b)

    def __rsub__(s, o):
        return K.of(o) - s

    def __neg__(s):
        return K(-s.a, -s.b)

    def __mul__(s, o):
        o = K.of(o)
        return K(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__

    def __truediv__(s, o):
        o = K.of(o)
        n = o.a * o.a - 2 * o.b * o.b
        return K((s.a * o.a - 2 * s.b * o.b) / n, (s.b * o.a - s.a * o.b) / n)

    def __rtruediv__(s, o):
        return K.of(o) / s

    def __eq__(s, o):
        o = K.of(o)
        return s.a == o.a and s.b == o.b

    def __hash__(s):
        return hash((s.a, s.b))

    def sgn(s):
        # sign of a + b sqrt2 :  compare a and -b sqrt2
        a, b = s.a, s.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if (a > 0) == (b > 0):
            return 1 if a > 0 else -1
        d = a * a - 2 * b * b                      # sign of a + b sqrt2 equals sign(a) * sign(d) when signs differ
        return (1 if a > 0 else -1) * (1 if d > 0 else -1)

    def __float__(s):
        return float(s.a) + float(s.b) * 2 ** 0.5

    def __repr__(s):
        return f"({s.a}+{s.b}r2)"


R2 = K(0, 1)
INV_R2 = K(0, Fr(1, 2))


# ------------------------------------------------------------------------------------------------------------------
# A. behaviour from projectors
# ------------------------------------------------------------------------------------------------------------------
def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum((A[i][k] * B[k][j] for k in range(m)), K(0)) for j in range(p)] for i in range(n)]


def competitor_projectors(d):
    I2 = [[K(1), K(0)], [K(0), K(1)]]
    sz = [[K(1), K(0)], [K(0), K(-1)]]
    sx = [[K(0), K(1)], [K(1), K(0)]]
    Aobs = [sz, sx]
    Bobs = [[[(sz[i][j] + sx[i][j]) * INV_R2 for j in range(2)] for i in range(2)],
            [[(sz[i][j] - sx[i][j]) * INV_R2 for j in range(2)] for i in range(2)]]

    def proj(O, sign):
        return [[(I2[i][j] + sign * O[i][j]) * Fr(1, 2) for j in range(2)] for i in range(2)]

    def embed(M, extra):
        Z = [[K(0)] * d for _ in range(d)]
        if d % 2 == 0:
            h = d // 2
            for i in range(2):
                for j in range(2):
                    for k in range(h):
                        Z[i * h + k][j * h + k] = M[i][j]          # M (x) 1_{d/2}, |i>|k> -> |i h + k>
        else:
            for blk in range((d - 1) // 2):
                for i in range(2):
                    for j in range(2):
                        Z[2 * blk + i][2 * blk + j] = M[i][j]
            Z[d - 1][d - 1] = K(extra)
        return Z

    zero = [[K(0)] * d for _ in range(d)]
    P = [[embed(proj(Aobs[x], 1), 1), embed(proj(Aobs[x], -1), 0)] + [zero] * (d - 2) for x in range(2)]
    Q = [[embed(proj(Bobs[y], 1), 1), embed(proj(Bobs[y], -1), 0)] + [zero] * (d - 2) for y in range(2)]
    return P, Q


def check_behaviour_A(d):
    P, Q = competitor_projectors(d)
    ok = True
    for M in (P, Q):
        for x in range(2):
            S = [[K(0)] * d for _ in range(d)]
            for a in range(d):
                Pa = M[x][a]
                P2 = matmul(Pa, Pa)
                ok &= all(P2[i][j] == Pa[i][j] and Pa[i][j] == Pa[j][i] for i in range(d) for j in range(d))
                S = [[S[i][j] + Pa[i][j] for j in range(d)] for i in range(d)]
            ok &= all(S[i][j] == K(int(i == j)) for i in range(d) for j in range(d))
    s = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    # p = Tr(P^T Q)/d ; all real symmetric
                    PT = P[x][a]
                    val = sum((PT[j][i] * Q[y][b][j][i] for i in range(d) for j in range(d)), K(0)) * Fr(1, d)
                    if a < 2 and b < 2:
                        ch = (K(1) + (1 if a == b else -1) * s[(x, y)] * INV_R2) * Fr(1, 4)
                    else:
                        ch = K(0)
                    want = ch if d % 2 == 0 else ch * Fr(d - 1, d) + (Fr(1, d) if a == b == 0 else 0)
                    ok &= val == want
    return ok


# ------------------------------------------------------------------------------------------------------------------
# 3-outcome behaviours as polynomials in t:  dict (x,y,a,b) -> list of K coefficients (power basis)
# ------------------------------------------------------------------------------------------------------------------
def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else K(0)) + (q[i] if i < len(q) else K(0)) for i in range(n)]


def pmul(p, q):
    r = [K(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] = r[i + j] + x * y
    return r


def pscale(p, c):
    return [x * c for x in p]


def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == K(0):
        p.pop()
    return p


def peval(p, t):
    r = K(0)
    for c in reversed(p):
        r = r * t + c
    return r


SG = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}


def beh_chsh():
    return {(x, y, a, b): [((K(1) + (1 if a == b else -1) * SG[(x, y)] * INV_R2) * Fr(1, 4))
                           if a < 2 and b < 2 else K(0)]
            for x in range(2) for y in range(2) for a in range(3) for b in range(3)}


def beh_det(c):
    return {(x, y, a, b): [K(int(a == c[x] and b == c[2 + y]))]
            for x in range(2) for y in range(2) for a in range(3) for b in range(3)}


def beh_noise():
    m = [[K(0), K(1)], [K(0), K(1)], [K(1), K(-2)]]          # t, t, 1 - 2t
    return {(x, y, a, b): pmul(m[a], m[b]) for x in range(2) for y in range(2) for a in range(3) for b in range(3)}


def beh_mix(p, q, wp, wq):
    return {k: padd(pmul(p[k], wp), pmul(q[k], wq)) for k in p}


def facet_on_beh(f, p):
    """f in MY coordinates (ref_facets.coords): [h0, pAB(x,y,a,b) a,b in {1,2}, pA(a|x), pB(b|y)] -> poly."""
    r = [K(f[0])]
    idx = 1
    for x in range(2):
        for y in range(2):
            for a in (1, 2):
                for b in (1, 2):
                    if f[idx]:
                        r = padd(r, pscale(p[(x, y, a, b)], f[idx]))
                    idx += 1
    for x in range(2):
        for a in (1, 2):
            if f[idx]:
                marg = [K(0)]
                for b in range(3):
                    marg = padd(marg, p[(x, 0, a, b)])
                r = padd(r, pscale(marg, f[idx]))
            idx += 1
    for y in range(2):
        for b in (1, 2):
            if f[idx]:
                marg = [K(0)]
                for a in range(3):
                    marg = padd(marg, p[(0, y, a, b)])
                r = padd(r, pscale(marg, f[idx]))
            idx += 1
    return ptrim(r)


def to_sympy(p, t):
    A = sum(sp.Rational(c.a.numerator, c.a.denominator) * t ** k for k, c in enumerate(p))
    B = sum(sp.Rational(c.b.numerator, c.b.denominator) * t ** k for k, c in enumerate(p))
    return sp.expand(A), sp.expand(B)


def nonneg_on(p, lo=Fr(0), hi=Fr(1, 3)):
    """exact: polynomial p (K coefficients) >= 0 on [lo, hi] ?  via real roots of the norm polynomial."""
    p = ptrim(p)
    if all(c == K(0) for c in p):
        return True, "zero"
    t = sp.symbols("t")
    A, B = to_sympy(p, t)
    N = sp.Poly(sp.expand(A * A - 2 * B * B), t, domain="QQ")
    pts = [lo, hi]
    if N.degree() > 0:
        ivs = N.intervals(inf=sp.Rational(lo.numerator, lo.denominator) - 1,
                          sup=sp.Rational(hi.numerator, hi.denominator) + 1, eps=sp.Rational(1, 10 ** 12))
        cuts = []
        for (l, u), _ in ivs:
            cuts += [Fr(int(l.p), int(l.q)), Fr(int(u.p), int(u.q))]
        cuts = sorted(set(c for c in cuts if lo <= c <= hi))
        # sample points: all cut points and midpoints between consecutive cut points (and the ends)
        grid = sorted(set([lo, hi] + cuts))
        pts = grid + [(grid[i] + grid[i + 1]) / 2 for i in range(len(grid) - 1)]
    vals = [peval(p, x).sgn() for x in pts]
    # every open interval between consecutive roots of N contains a sample point (isolating intervals are disjoint
    # and of width < 1e-12; consecutive midpoints separate them), so p >= 0 on [lo, hi] iff all samples >= 0
    return min(vals) >= 0, len(pts)


def part_B(verbose=True):
    V = [RF.coords(s) for s in RF.STRATS]
    A = [[1] + v for v in V]
    rays = RF.dd(A, list(range(81)))
    F = sorted(set(RF.prim(list(r)) for r in rays))
    assert len(F) == 1116 and all(RF.is_facet(f, V) for f in F)
    # coarse-grained CHSH in my coordinates: find it by its tight set
    beta = {}
    for (x, y), s in SG.items():
        for a in range(3):
            for b in range(3):
                beta[(x, y, a, b)] = s * (1 if a == 0 else -1) * (1 if b == 0 else -1)
    okc, Tc = RF.full_functional_tight(beta, 2)
    fc = [f for f in F if RF.tight_set(f, V) == Tc]
    assert okc and len(fc) == 1
    fc = fc[0]
    n = beh_noise()
    ch = beh_chsh()
    cases = {"even (q = CHSH)": ch,
             "odd (q = (1-t) CHSH + t delta_0000)": beh_mix(ch, beh_det((0, 0, 0, 0)), [K(1), K(-1)], [K(0), K(1)])}
    allok = True
    for name, q in cases.items():
        fcn, fcq = facet_on_beh(fc, n), facet_on_beh(fc, q)
        # f_c(q) < 0 on [0, 1/3]: -f_c(q) - 1/1000 >= 0 there (exact)
        ok1, _ = nonneg_on(padd(pscale(fcq, -1), [K(Fr(-1, 1000))]))
        # f_c(n) = k (8 t - 8 t^2) with k > 0 (hence > 0 on (0, 1/3])
        fcn = ptrim(fcn)
        kk = fcn[1] * Fr(1, 8) if len(fcn) > 1 else K(0)
        okn = kk.sgn() > 0 and len(fcn) == 3 and fcn[0] == K(0) and fcn[2] == kk * (-8)
        bad, nz = [], 0
        for f in F:
            G = ptrim(padd(pmul(fcn, facet_on_beh(f, q)), pscale(pmul(facet_on_beh(f, n), fcq), -1)))
            if all(c == K(0) for c in G):
                nz += 1
                continue
            ok, _ = nonneg_on(G)
            if not ok:
                bad.append(f)
        # closed form of v* = fcn / (fcn - fcq) vs v_even / v_odd at t = 1/d, d = 3..60
        okv = True
        for d in range(3, 61):
            t = Fr(1, d)
            vs = peval(fcn, t) / (peval(fcn, t) - peval(fcq, t))
            if name.startswith("even"):
                want = K(4 * (d - 1)) / ((R2 - 1) * (d * d) + 4 * (d - 1))
            else:
                want = K(4) / ((R2 - 1) * d + 4)
            okv &= vs == want
        good = ok1 and okn and not bad and okv
        allok &= good
        if verbose:
            print(f"  B [{name}]: f_c(q) < 0 on [0,1/3]: {ok1}; f_c(n) > 0 on (0,1/3]: {okn}; "
                  f"G_F >= 0 for all {len(F)} facets: {not bad} ({nz} identically 0); v* = closed form d=3..60: {okv}",
                  flush=True)
    return allok, F, fc


# ------------------------------------------------------------------------------------------------------------------
# C. explicit exact local models at v*
# ------------------------------------------------------------------------------------------------------------------
def solve_exact(M, rhs):
    """solve square system M w = rhs over Q(sqrt2) (Gauss)."""
    n = len(M)
    A = [list(M[i]) + [rhs[i]] for i in range(n)]
    for c in range(n):
        piv = next((i for i in range(c, n) if not A[i][c] == K(0)), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for i in range(n):
            if i != c and not A[i][c] == K(0):
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [A[i][n] for i in range(n)]


def local_model_at_vstar(d, kind):
    t = Fr(1, d)
    n = {k: peval(v, t) for k, v in beh_noise().items()}
    q = beh_chsh() if kind == "even" else beh_mix(beh_chsh(), beh_det((0, 0, 0, 0)), [K(1), K(-1)], [K(0), K(1)])
    q = {k: peval(v, t) for k, v in q.items()}
    # binarised CHSH values to get v*
    def chsh(p):
        return sum((SG[(x, y)] * (1 if a == 0 else -1) * (1 if b == 0 else -1) * p[(x, y, a, b)]
                    for x in range(2) for y in range(2) for a in range(3) for b in range(3)), K(0))
    vs = (2 - chsh(n)) / (chsh(q) - chsh(n))
    target = {k: vs * q[k] + (1 - vs) * n[k] for k in q}
    # float LP over the 81 deterministic strategies, constraints = all 36 joint probabilities
    keys = sorted(target)
    Aeq = np.array([[1.0 if (s[k[0]] == k[2] and s[2 + k[1]] == k[3]) else 0.0 for s in RF.STRATS] for k in keys])
    beq = np.array([float(target[k]) for k in keys])
    # prefer an interior-ish solution: maximise the smallest weight on the support of a first solution
    res = linprog(np.zeros(81), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * 81, method="highs")
    assert res.status == 0, (d, kind, res.message)
    supp = [i for i in range(81) if res.x[i] > 1e-11]
    # exact: find a set of linearly independent columns within the support spanning the system, solve exactly
    cols = []
    for i in supp:
        trial = cols + [i]
        if np.linalg.matrix_rank(Aeq[:, trial]) == len(trial):
            cols = trial
    # least squares system restricted to independent rows
    sub = Aeq[:, cols]
    rows = []
    for r in range(len(keys)):
        trial = rows + [r]
        if np.linalg.matrix_rank(sub[trial, :]) == len(trial):
            rows = trial
        if len(rows) == len(cols):
            break
    M = [[K(int(Aeq[r, c])) for c in cols] for r in rows]
    w = solve_exact(M, [target[keys[r]] for r in rows])
    if w is None:
        return False, None
    # exact verification of ALL 36 equations and nonnegativity
    ok = all(x.sgn() >= 0 for x in w)
    for k in keys:
        val = sum((w[j] for j, c in enumerate(cols)
                   if RF.STRATS[c][k[0]] == k[2] and RF.STRATS[c][2 + k[1]] == k[3]), K(0))
        ok &= val == target[k]
    model = {RF.STRATS[c]: w[j] for j, c in enumerate(cols)}
    return ok, (vs, model)


def lift_and_check(d, kind, vs, model):
    """Lemma 3 post-processing: R -> uniform on {2..d-1}; check the full d-outcome behaviour equals v* p + (1-v*) u."""
    full = {}
    for s, w in model.items():
        choices = [[c] if c < 2 else list(range(2, d)) for c in s]
        k = 1
        for c in s:
            k *= 1 if c < 2 else (d - 2)
        for lam in itertools.product(*choices):
            full[lam] = full.get(lam, K(0)) + w * Fr(1, k)
    ok = True
    s2 = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    val = sum((w for lam, w in full.items() if lam[x] == a and lam[2 + y] == b), K(0))
                    if a < 2 and b < 2:
                        ch = (K(1) + (1 if a == b else -1) * s2[(x, y)] * INV_R2) * Fr(1, 4)
                    else:
                        ch = K(0)
                    p = ch if kind == "even" else ch * Fr(d - 1, d) + (Fr(1, d) if a == b == 0 else 0)
                    ok &= val == vs * p + (1 - vs) * Fr(1, d * d)
    return ok and all(w.sgn() >= 0 for w in full.values())


def main():
    t0 = time.time()
    okA = True
    for d in range(3, 13):
        r = check_behaviour_A(d)
        okA &= r
    print(f"A competitor projectors and behaviour (exact, own Q(sqrt2)), d = 3..12: {okA}  ({time.time() - t0:.0f}s)",
          flush=True)
    okB, F, fc = part_B()
    print(f"B Prop. 5 by root isolation (own facet list, all t in [0,1/3]): {okB}  ({time.time() - t0:.0f}s)",
          flush=True)
    okC = True
    for d in range(3, 25):
        for kind in (["even"] if d % 2 == 0 else ["odd", "even"]):
            ok, data = local_model_at_vstar(d, kind)
            okC &= ok
            msg = f"  C d={d:2d} [{kind:4s}{'(Phi_2)' if kind == 'even' and d % 2 else ''}]: exact local model at v* = " \
                  f"{float(data[0]) if data else float('nan'):.12f}: {ok}"
            if ok and d in (4, 5):
                okl = lift_and_check(d, kind, *data)
                okC &= okl
                msg += f"; lifted to full {d}-outcome model, exact: {okl}"
            print(msg, flush=True)
    print(f"C explicit exact local models at v*, d = 3..24: {okC}  ({time.time() - t0:.0f}s)")
    print("RESULT:", "PASS" if okA and okB and okC else "FAIL")


if __name__ == "__main__":
    main()
