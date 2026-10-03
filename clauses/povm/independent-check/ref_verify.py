"""
ref_verify.py -- referee's independent exact checker for the P1 POVM certificates (cert_povm_d{d}.pkl).

Nothing is imported from the P1 code.  Independent choices:
  * arithmetic: lazy ring R = Z[x]/(x^N - 1), N = 4d (cyclic convolution of integer vectors, common denominators
    cleared); the projection R -> Q(zeta_N) (reduction mod Phi_N, Phi_N taken from sympy) is applied only at the
    zero test.  R -> Q(zeta_N) is a ring homomorphism commuting with x -> x^-1 (complex conjugation).
  * target: S_op built from the definition S = E<X1-Y1>_d + E<Y1-X2>_d + E<X2-Y2>_d + E<Y2-X1-1>_d with the Fourier
    coefficients h^(n) = (1/d) sum_k h(k) w^{-nk} of h(k) = <k - delta>_d computed directly.
  * symmetry: explicit finite group G of word maps (perm of the 4 chain positions, sign of n, phase vector t, reversal)
    obtained by closure from rho, sigma, transposition; orbits by applying ALL of G; canonical form = MAX rotation and
    MAX orbit element.  Relation used: L(u) = w^{sum_letters t[g] n} L(f(u)).
  * Gram blocks: X = N Y N^* computed in R; identity  S_op - lam = sum_M sum_ij X_ij e_j^* e_i
    + sum_c sum_ij X_ij u_j^* E^0_c u_i E^1_0  checked orbit by orbit, words concatenated, never merged.
  * positivity: rigorous interval enclosure (mpmath.iv) of the real 2k x 2k embedding, rational midpoint matrix,
    exact rational LDL of (M_q - mu I) with mu >= ||M - M_q||_2  (Weyl)  =>  Y positive definite.
  * equality vectors: exact Gaussian elimination over Q(zeta_N) (power basis, Galois-norm inverses).
usage: python ref_verify.py [--cert PATH] [--skip-pd] [--skip-eq] d
"""
import sys
import time
import pickle
from fractions import Fraction
from math import lcm, gcd
import sympy
import mpmath


def cyclotomic_coeffs(N):
    x = sympy.Symbol('x')
    P = sympy.Poly(sympy.cyclotomic_poly(N, x), x)
    co = [int(c) for c in reversed(P.all_coeffs())]
    assert co[-1] == 1
    return co


class Lazy:
    """Z[x]/(x^N - 1): elements are lists of N ints."""

    def __init__(self, N):
        self.N = N
        self.Phi = cyclotomic_coeffs(N)
        self.m = len(self.Phi) - 1

    def reduce(self, v):
        """remainder of sum v_k x^k modulo Phi_N (monic), list of length m"""
        r = list(v)
        m, P = self.m, self.Phi
        for k in range(len(r) - 1, m - 1, -1):
            c = r[k]
            if c:
                r[k] = 0
                base = k - m
                for j in range(m):
                    if P[j]:
                        r[base + j] -= c * P[j]
        return r[:m]

    def mul_bs(self, big, small):
        """big (list of N ints) times small (list of (exponent, int))"""
        N = self.N
        out = [0] * N
        for e, c in small:
            e %= N
            sh = big if e == 0 else big[N - e:] + big[:N - e]      # sh[k] = big[k - e]
            if c == 1:
                out = [o + s for o, s in zip(out, sh)]
            elif c == -1:
                out = [o - s for o, s in zip(out, sh)]
            else:
                out = [o + c * s for o, s in zip(out, sh)]
        return out

    @staticmethod
    def add(a, b):
        return [x + y for x, y in zip(a, b)]

    def conj_big(self, a):
        N = self.N
        out = [0] * N
        for k, x in enumerate(a):
            out[(-k) % N] = x
        return out


def small_mul(a, b, N):
    """sparse small elements: dict exp -> int"""
    out = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = (e1 + e2) % N
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c}


def small_conj(a, N):
    return {(-e) % N: c for e, c in a.items()}


# ----------------------------------------------------------------------------------------------- words, group
def adj(w, d):
    return tuple((g, (-n) % d) for (g, n) in reversed(w))


def canon_rot(u):
    if len(u) <= 1:
        return u
    return max(u[i:] + u[:i] for i in range(len(u)))


def make_group(d):
    ident = ((0, 1, 2, 3), 1, (0, 0, 0, 0), 0)
    gens = [((1, 2, 3, 0), 1, (0, 0, 0, 1), 0),     # rho: (g,n)->(g+1,n), letter (3,n) carries phase w^n
            ((3, 2, 1, 0), -1, (0, 0, 0, 0), 0),    # sigma: (g,n)->(3-g,-n)
            ((0, 1, 2, 3), 1, (0, 0, 0, 0), 1)]     # transposition: word reversal

    def compose(f2, f1):   # f2 o f1
        p1, e1, t1, r1 = f1
        p2, e2, t2, r2 = f2
        return (tuple(p2[p1[g]] for g in range(4)), e1 * e2,
                tuple((t1[g] + e1 * t2[p1[g]]) % d for g in range(4)), r1 ^ r2)
    G = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for f in frontier:
            for g in gens:
                h = compose(g, f)
                if h not in G:
                    G.add(h)
                    new.append(h)
        frontier = new
    return sorted(G)


def apply(f, u, d):
    p, e, t, r = f
    ph = 0
    v = []
    for (g, n) in u:
        ph += t[g] * n
        v.append((p[g], (e * n) % d))
    if r:
        v.reverse()
    return tuple(v), ph % d


class Orbits:
    """L(w) = w^{e} L(rep) (e mod d) or None if L(w) = 0 is forced."""

    def __init__(self, d):
        self.d = d
        self.G = make_group(d)
        self.memo = {}
        self.nbad = 0

    def __call__(self, w):
        w = canon_rot(w)
        r = self.memo.get(w)
        if r is not None or w in self.memo:
            return r
        d = self.d
        img = {}
        bad = False
        for f in self.G:
            v, ph = apply(f, w, d)
            v = canon_rot(v)
            if v in img:
                if img[v] != ph:
                    bad = True
            else:
                img[v] = ph
        if bad:
            self.nbad += 1
            for v in img:
                self.memo[v] = None
            return None
        rep = max(img)
        prep = img[rep]
        for v, pv in img.items():
            self.memo[v] = ((prep - pv) % d, rep)     # L(v) = w^{-pv} L(w) = w^{prep - pv} L(rep)
        return self.memo[w]


# ----------------------------------------------------------------------------------------------- certificate
def parse_elem(x, N):
    a, den = x
    a = [int(t) for t in a]
    den = int(den)
    assert den > 0
    return a + [0] * (N - len(a)), den


def to_small(x, N, scale):
    a, den = parse_elem(x, N)
    assert scale % den == 0
    f = scale // den
    return {k: v * f for k, v in enumerate(a) if v}


def verify_identity(d, cert, R, orb, log):
    N = 4 * d
    phiN = R.m
    keep = list(cert["keep"])
    nb = len(cert["bdata"])
    assert sorted(set(keep)) == keep and all(0 <= b < nb for b in keep)
    # common denominators
    LY = 1
    LK = 1
    LE = 1
    for b in keep:
        for row in cert["Y"][b]:
            for x in row:
                assert len(x[0]) == phiN
                LY = lcm(LY, int(x[1]))
        for col in cert["kernels"][b]:
            for x in col:
                assert len(x[0]) == phiN
                LK = lcm(LK, int(x[1]))
        for el in cert["bdata"][b][1]:
            for (cf, w) in el:
                assert len(cf[0]) == phiN
                LE = lcm(LE, int(cf[1]))
                for (g, n) in w:
                    assert g in (0, 1, 2, 3) and 1 <= n <= d - 1, (g, n)
    SCALE = LY * LK * LK * LE * LE * d * d
    log(f"  denominators: Y lcm {LY.bit_length()} bits, kernels {LK}, elements {LE}")
    Vtot = {}
    nterms = 0
    nM = nD = 0
    for b in keep:
        lab, els, _ent = cert["bdata"][b]
        Y = cert["Y"][b]
        ker = cert["kernels"][b]
        k = len(ker)
        n = len(els)
        assert len(Y) == k and all(len(row) == k for row in Y)
        assert all(len(col) == n for col in ker)
        # exact Hermiticity of Y (in Q(zeta_N)): Y_rs - conj(Y_sr) = 0
        Yb = [[None] * k for _ in range(k)]
        for r in range(k):
            for s in range(k):
                a, den = parse_elem(Y[r][s], N)
                Yb[r][s] = [t * (LY // den) for t in a]
        for r in range(k):
            for s in range(r, k):
                diff = [x - y for x, y in zip(Yb[r][s], R.conj_big(Yb[s][r]))]
                assert not any(R.reduce(diff)), ("Y not Hermitian", b, r, s)
        Ns = [[to_small(ker[r][a], N, LK) for r in range(k)] for a in range(n)]     # N[a][r] = ker[r][a]
        # X = N Y N^*  (scale LY * LK^2), in the lazy ring
        NY = [[None] * k for _ in range(n)]
        for a in range(n):
            for c in range(k):
                acc = [0] * N
                for r in range(k):
                    if Ns[a][r]:
                        acc = R.add(acc, R.mul_bs(Yb[r][c], list(Ns[a][r].items())))
                NY[a][c] = acc
        X = [[None] * n for _ in range(n)]
        for a in range(n):
            for bb in range(n):
                acc = [0] * N
                for c in range(k):
                    if Ns[bb][c]:
                        acc = R.add(acc, R.mul_bs(NY[a][c], list(small_conj(Ns[bb][c], N).items())))
                X[a][bb] = acc
        elc = [[(to_small(cf, N, LE), w) for (cf, w) in el] for el in els]
        if lab[0] == 'M':
            nM += 1
            extra = d * d          # D blocks carry the factor d^2 from the two effects
            pieces = None
        elif lab[0] == 'D':
            nD += 1
            assert lab[1] == 1 and 0 <= lab[2] < d
            c0 = lab[2]
            extra = 1
            # E^0_c = (1/d) sum_m w^{-m c} Z^0_m ;  E^1_0 = (1/d) sum_m Z^1_m   (scaled by d each)
            Eexp = [({(4 * (-m * c0)) % N: 1}, (() if m == 0 else ((0, m),))) for m in range(d)]
            Fexp = [({0: 1}, (() if m == 0 else ((1, m),))) for m in range(d)]
        else:
            raise ValueError(lab)
        for i in range(n):
            for j in range(n):
                if not any(X[i][j]):
                    continue
                K = {}
                for (cj, wj) in elc[j]:
                    cjc = small_conj(cj, N)
                    wja = adj(wj, d)
                    for (ci, wi) in elc[i]:
                        base = small_mul(cjc, ci, N)
                        if lab[0] == 'M':
                            combos = [(base, wja + wi)]
                        else:
                            combos = []
                            for (ce, we) in Eexp:
                                b2 = small_mul(base, ce, N)
                                for (cf2, wf) in Fexp:
                                    combos.append((small_mul(b2, cf2, N), wja + we + wi + wf))
                        for (cc, word) in combos:
                            nterms += 1
                            o = orb(word)
                            if o is None:
                                continue
                            e, rep = o
                            acc = K.setdefault(rep, {})
                            for ex, v in cc.items():
                                ee = (ex + 4 * e) % N
                                acc[ee] = acc.get(ee, 0) + v * extra
                for rep, cc in K.items():
                    cc = [(ex, v) for ex, v in cc.items() if v]
                    if not cc:
                        continue
                    contrib = R.mul_bs(X[i][j], cc)
                    if rep in Vtot:
                        Vtot[rep] = R.add(Vtot[rep], contrib)
                    else:
                        Vtot[rep] = contrib
    # left side as Fraction vectors in the power basis of Q(zeta_N)
    P = {rep: [Fraction(t, SCALE) for t in R.reduce(v)] for rep, v in Vtot.items()}
    # target T = S_op - lam, S_op built from the definition
    T = {}

    def addT(word, vec_scaled, den):
        o = orb(word)
        if o is None:
            return
        e, rep = o
        sh = [0] * N
        for k2, v in enumerate(vec_scaled):
            sh[(k2 + 4 * e) % N] += v
        red = R.reduce(sh)
        cur = T.get(rep, [Fraction(0)] * phiN)
        T[rep] = [x + Fraction(y, den) for x, y in zip(cur, red)]
    lam_a, lam_den = parse_elem(cert["lam"], N)
    const = [0] * N
    const[0] = 2 * (d - 1) * lam_den
    const = [x - y for x, y in zip(const, lam_a)]
    addT((), const, lam_den)
    links = [(0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, 1)]     # E< X^first - X^second - delta >_d
    for (g1, g2, delta) in links:
        h = [(kk - delta) % d for kk in range(d)]
        assert sum(h) * 2 == d * (d - 1)                    # h^(0) = (d-1)/2 for every link
        for nn in range(1, d):
            vec = [0] * N
            for kk in range(d):
                vec[(4 * (-nn * kk)) % N] += h[kk]          # d * h^(n) in R
            addT(((g1, nn), (g2, (-nn) % d)), vec, d)
    keys = set(P) | set(T)
    zero = [Fraction(0)] * phiN
    bad = [kk for kk in keys if P.get(kk, zero) != T.get(kk, zero)]
    log(f"  identity: {len(keys)} orbit classes (P {len(P)}, T {len(T)}), {nterms} expanded word terms, "
        f"{nM} moment + {nD} doubly-localizing blocks, |G| = {len(orb.G)}, forced-zero orbits met: {orb.nbad} "
        f"-> {'OK' if not bad else 'FAILED on %d classes' % len(bad)}")
    return not bad, bad


# ----------------------------------------------------------------------------------------------- positivity
def pd_check(d, cert, log, prec=320):
    """rigorous: interval enclosure -> rational midpoints -> exact LDL of (M_q - mu I), mu >= ||M - M_q||_2"""
    N = 4 * d
    iv = mpmath.iv
    iv.prec = prec
    cosv = [iv.cos(2 * iv.pi * kk / N) for kk in range(N)]
    sinv = [iv.sin(2 * iv.pi * kk / N) for kk in range(N)]

    def raw_to_frac(t):
        # exact value of an mpmath raw mpf tuple (sign, man, exp, bc); no rounding
        sign, man, exp, _bc = t
        assert man != 0 or exp == 0, "special value (inf/nan) in interval endpoint"
        v = Fraction(int(man)) * (Fraction(2) ** int(exp)) if exp >= 0 else Fraction(int(man), 2 ** int(-exp))
        return -v if sign else v

    def endpoints(z):
        lo_raw, hi_raw = z._mpi_
        return raw_to_frac(lo_raw), raw_to_frac(hi_raw)
    minpiv = None
    for b in cert["keep"]:
        Y = cert["Y"][b]
        k = len(Y)
        K2 = 2 * k
        Mq = [[Fraction(0)] * K2 for _ in range(K2)]
        epsmax = Fraction(0)
        for r in range(k):
            for s in range(r, k):
                a, den = Y[r][s]
                re = iv.mpf(0)
                im = iv.mpf(0)
                for kk, t in enumerate(a):
                    if t:
                        re += int(t) * cosv[kk]
                        im += int(t) * sinv[kk]
                re = re / int(den)
                im = im / int(den)
                vals = []
                for z in (re, im):
                    lo, hi = endpoints(z)
                    assert lo <= hi and hi - lo < Fraction(1, 2 ** 200), (lo, hi)
                    mid = (lo + hi) / 2
                    # round the midpoint to a 2^-100 grid (cheaper LDL), error accounted for
                    q = Fraction(round(mid * 2 ** 100), 2 ** 100)
                    err = max(abs(hi - q), abs(q - lo))
                    vals.append((q, err))
                (A, eA), (B, eB) = vals
                if r == s:
                    # exact Hermiticity was checked separately (Im of diagonal is 0); enclosure must contain 0
                    assert abs(B) <= eB
                    B, eB = Fraction(0), Fraction(0)
                epsmax = max(epsmax, eA, eB)
                # M = [[A, -B], [B, A]] with Y = A + iB;  M[r][s] = A_rs, M[r][k+s] = -B_rs, M[k+r][s] = B_rs
                Mq[r][s] = A
                Mq[k + r][k + s] = A
                Mq[s][r] = A
                Mq[k + s][k + r] = A
                Mq[r][k + s] = -B
                Mq[k + r][s] = B
                Mq[s][k + r] = B          # (M^T)[s][k+r] = M[k+r][s]
                Mq[k + s][r] = -B
        mu = K2 * epsmax * 2 + Fraction(1, 2 ** 90)
        # exact LDL of Mq - mu I
        A = [row[:] for row in Mq]
        for i in range(K2):
            A[i][i] -= mu
        for c in range(K2):
            p = A[c][c]
            assert p > 0, f"block {b}: pivot {c} not positive ({float(p)})"
            minpiv = p if minpiv is None else min(minpiv, p)
            for r in range(c + 1, K2):
                if A[r][c] == 0:
                    continue
                f = A[r][c] / p
                Ar, Ac = A[r], A[c]
                for j in range(c + 1, K2):
                    if Ac[j]:
                        Ar[j] -= f * Ac[j]
    log(f"  positivity: every Y_b positive definite (exact rational LDL of the 2k x 2k real embedding minus "
        f"mu I; min pivot {float(minpiv):.4e})")
    return True


# ----------------------------------------------------------------------------------------------- Q(zeta_N) field
class QZ:
    def __init__(self, N):
        self.N = N
        self.Phi = cyclotomic_coeffs(N)
        self.m = len(self.Phi) - 1
        self.units = [t for t in range(1, N) if gcd(t, N) == 1]

    def red(self, v):
        r = list(v)
        m, P = self.m, self.Phi
        for k in range(len(r) - 1, m - 1, -1):
            c = r[k]
            if c:
                r[k] = 0
                for j in range(m):
                    if P[j]:
                        r[k - m + j] -= c * P[j]
        r = r[:m] + [Fraction(0)] * (m - len(r))
        return tuple(r[:m])

    def mul(self, a, b):
        out = [Fraction(0)] * (2 * self.m)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        out[i + j] += x * y
        return self.red(out)

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def galois(self, a, t):
        out = [Fraction(0)] * self.N
        for k, x in enumerate(a):
            if x:
                out[(k * t) % self.N] += x
        return self.red(out)

    def inv(self, a):
        prod = None
        for t in self.units:
            if t == 1:
                continue
            g = self.galois(a, t)
            prod = g if prod is None else self.mul(prod, g)
        if prod is None:
            prod = self.one()
        nrm = self.mul(a, prod)
        assert all(x == 0 for x in nrm[1:]) and nrm[0] != 0
        return tuple(x / nrm[0] for x in prod)

    def one(self):
        return tuple([Fraction(1)] + [Fraction(0)] * (self.m - 1))

    def zpow(self, e):
        v = [Fraction(0)] * self.N
        v[e % self.N] = Fraction(1)
        return self.red(v)

    def iszero(self, a):
        return not any(a)

    def elem(self, x):
        a, den = x
        return self.red([Fraction(int(t), int(den)) for t in a])


def eq_check(d, cert, log):
    """for every D block (E^0_c, E^1_0): f = Z^0_n - w^{nc} and f = Z^1_n - 1 lie in range(N_c)."""
    N = 4 * d
    K = QZ(N)
    cnt = 0
    for b in cert["keep"]:
        lab, els, _ = cert["bdata"][b]
        if lab[0] != 'D':
            continue
        c0 = lab[2]
        n = len(els)
        words = []
        coefs = []
        for el in els:
            assert len(el) == 1
            cf, w = el[0]
            words.append(w)
            coefs.append(K.elem(cf))
        pos = {w: i for i, w in enumerate(words)}
        assert len(pos) == n
        rows = [[K.elem(x) for x in col] for col in cert["kernels"][b]]
        # row echelon form (full reduction)
        basis = []      # list of (pivot, row) with row[pivot] = 1
        for row in rows:
            row = list(row)
            for (p, br) in basis:
                if not K.iszero(row[p]):
                    f = row[p]
                    row = [K.sub(x, K.mul(f, y)) for x, y in zip(row, br)]
            p = next((i for i in range(n) if not K.iszero(row[i])), None)
            assert p is not None, "kernel vectors linearly dependent"
            ip = K.inv(row[p])
            row = [K.mul(ip, x) for x in row]
            # keep previous basis rows reduced at the new pivot
            nb2 = []
            for (q, br) in basis:
                if not K.iszero(br[p]):
                    f = br[p]
                    br = [K.sub(x, K.mul(f, y)) for x, y in zip(br, row)]
                nb2.append((q, br))
            basis = nb2 + [(p, row)]
        assert len(basis) == len(rows)
        for nn in range(1, d):
            for (g, const) in ((0, K.zpow(4 * nn * c0)), (1, K.one())):
                v = [tuple([Fraction(0)] * K.m) for _ in range(n)]
                # f = 1 * Z^g_n - const * 1 expressed in the basis u_i = coef_i * word_i
                v[pos[((g, nn),)]] = K.inv(coefs[pos[((g, nn),)]])
                v[pos[()]] = K.sub(v[pos[()]], K.mul(const, K.inv(coefs[pos[()]])))
                for (p, br) in basis:
                    if not K.iszero(v[p]):
                        f = v[p]
                        v = [K.sub(x, K.mul(f, y)) for x, y in zip(v, br)]
                assert all(K.iszero(x) for x in v), ("equality vector not in range", lab, g, nn)
                cnt += 1
    log(f"  equality case: {cnt} vectors (Z^0_n - w^(nc), Z^1_n - 1) lie in range(N_c) of the doubly-localizing "
        f"blocks (exact elimination over Q(zeta_{N}))")
    return True


# ----------------------------------------------------------------------------------------------- lam
def lam_check(d, cert, log):
    """4 - 2 lam/(d-1) = 4/(d(d-1)) sum_j (d-j) sec(pi j/2d), sec = 2/(z^j + z^-j), z = zeta_{4d}; checked
    without inverses: multiply by prod_j C_j, C_j = z^j + z^-j."""
    N = 4 * d
    R = Lazy(N)
    a, den = parse_elem(cert["lam"], N)

    def mul(x, y):
        out = [0] * N
        for i, s in enumerate(x):
            if s:
                for j, t in enumerate(y):
                    if t:
                        out[(i + j) % N] += s * t
        return out
    C = []
    for j in range(1, d):
        v = [0] * N
        v[j % N] += 1
        v[(-j) % N] += 1
        C.append(v)
    one = [1] + [0] * (N - 1)
    prodC = one
    for v in C:
        prodC = mul(prodC, v)
    # LHS * den*d*(d-1):  (4 den (d-1) - 2 lam_num) * d * prod C
    lhs_core = [0] * N
    lhs_core[0] = 4 * den * (d - 1)
    lhs_core = [x - 2 * y for x, y in zip(lhs_core, a)]
    lhs = [x * d for x in mul(lhs_core, prodC)]
    # RHS * den*d*(d-1):  4 den sum_j (d-j) 2 prod_{i != j} C_i
    rhs = [0] * N
    for j in range(1, d):
        pr = one
        for i, v in enumerate(C, start=1):
            if i != j:
                pr = mul(pr, v)
        rhs = [x + 8 * den * (d - j) * y for x, y in zip(rhs, pr)]
    ok = not any(R.reduce([x - y for x, y in zip(lhs, rhs)]))
    mpmath.mp.dps = 40
    z = mpmath.exp(2j * mpmath.pi / N)
    lamv = sum(int(t) * z ** kk for kk, t in enumerate(cert["lam"][0])) / int(cert["lam"][1])
    I_me = 4 * mpmath.fsum((d - j) * mpmath.sec(mpmath.pi * j / (2 * d)) for j in range(1, d)) / (d * (d - 1))
    log(f"  lam: exact closed form 4 - 2 lam/(d-1) = I_ME(d): {'OK' if ok else 'FAILED'}  (lam ~ {mpmath.nstr(lamv.real, 15)}, "
        f"Im ~ {mpmath.nstr(abs(lamv.imag), 3)}, I_ME ~ {mpmath.nstr(I_me, 15)})")
    return ok


def main():
    args = sys.argv[1:]
    path = None
    skip_pd = skip_eq = False
    ds = []
    i = 0
    while i < len(args):
        if args[i] == "--cert":
            path = args[i + 1]
            i += 2
            continue
        if args[i] == "--skip-pd":
            skip_pd = True
        elif args[i] == "--skip-eq":
            skip_eq = True
        else:
            ds.append(int(args[i]))
        i += 1
    for d in ds:
        p = path or rf"..\P1_povm_numerics\certs\cert_povm_d{d}.pkl"
        cert = pickle.load(open(p, "rb"))
        assert cert["d"] == d and cert["N"] == 4 * d

        def log(s):
            print(f"d={d}: {s}", flush=True)
        t0 = time.time()
        R = Lazy(4 * d)
        orb = Orbits(d)
        ok_lam = lam_check(d, cert, log)
        ok_id, _ = verify_identity(d, cert, R, orb, log)
        log(f"  (identity time {time.time() - t0:.1f} s)")
        ok_pd = True if skip_pd else pd_check(d, cert, log)
        ok_eq = True if skip_eq else eq_check(d, cert, log)
        verdict = ok_lam and ok_id and ok_pd and ok_eq
        log(f"RESULT {'PASS' if verdict else 'FAIL'} (lam {ok_lam}, identity {ok_id}, pd {ok_pd if not skip_pd else 'skipped'}, "
            f"eq {ok_eq if not skip_eq else 'skipped'})  total {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
