"""
modsolve.py -- multi-modular exact solver for square linear systems  M z = r  over
   F = Q(zeta_N)                      (elements: (tuple of ints, den))            or
   L = F[t]/(p(t)), p monic over F    (elements: tuple of k F-elements)
using primes P = 1 mod N that split completely in L (so L (x) F_P = F_P^{phi(N) k}),
vectorised Gaussian elimination mod P over all embeddings, CRT and rational reconstruction.
The result is returned in the same exact representation; the caller verifies it exactly.
Singular systems: pivot rows/cols are fixed from the first prime; free unknowns are set to 0.
"""
import math
import random
import numpy as np
from fractions import Fraction


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    dd, s = n - 1, 0
    while dd % 2 == 0:
        dd //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, dd, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def prim_root_of_unity(N, P):
    """a primitive N-th root of unity mod P (P = 1 mod N)."""
    fac = []
    n = N
    q = 2
    while q * q <= n:
        if n % q == 0:
            fac.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        fac.append(n)
    for g in range(2, 10000):
        r = pow(g, (P - 1) // N, P)
        if all(pow(r, N // f, P) != 1 for f in fac):
            return r
    raise ValueError


# ---- polynomial helpers mod P (coefficient lists low->high)
def pmod(a, m, P):
    a = [x % P for x in a]
    while len(a) and a[-1] == 0:
        a.pop()
    dm = len(m) - 1
    inv_lead = pow(m[-1], P - 2, P)
    while len(a) - 1 >= dm and a:
        c = a[-1] * inv_lead % P
        sh = len(a) - 1 - dm
        for i in range(len(m)):
            a[sh + i] = (a[sh + i] - c * m[i]) % P
        while len(a) and a[-1] == 0:
            a.pop()
    return a


def pmul(a, b, P):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % P
    return out


def pgcd(a, b, P):
    a = [x % P for x in a]
    b = [x % P for x in b]
    while b and any(b):
        a, b = b, pmod(a, b, P)
        while b and b[-1] == 0:
            b.pop()
    while a and a[-1] == 0:
        a.pop()
    if a:
        inv = pow(a[-1], P - 2, P)
        a = [x * inv % P for x in a]
    return a


def ppow_mod(base, e, m, P):
    result = [1]
    base = pmod(base, m, P)
    while e:
        if e & 1:
            result = pmod(pmul(result, base, P), m, P)
        base = pmod(pmul(base, base, P), m, P)
        e >>= 1
    return result


def roots_mod(poly, P, rng):
    """all roots of poly mod P if it splits into distinct linear factors, else None."""
    poly = [x % P for x in poly]
    while poly and poly[-1] == 0:
        poly.pop()
    deg = len(poly) - 1
    if deg == 1:
        return [(-poly[0]) * pow(poly[1], P - 2, P) % P]
    # check split: t^P = t mod poly
    tp = ppow_mod([0, 1], P, poly, P)
    diff = pmod([(tp[i] if i < len(tp) else 0) - (1 if i == 1 else 0) for i in range(max(len(tp), 2))], poly, P)
    if any(diff):
        return None
    # squarefree check
    dpoly = [(i * poly[i]) % P for i in range(1, len(poly))]
    if len(pgcd(poly, dpoly, P)) > 1:
        return None
    # Cantor-Zassenhaus equal-degree splitting (degree 1)
    def split(f):
        if len(f) - 1 == 1:
            return [(-f[0]) * pow(f[1], P - 2, P) % P]
        while True:
            a = rng.randrange(P)
            h = ppow_mod([a, 1], (P - 1) // 2, f, P)
            h = h + [0] * max(0, 1 - len(h))
            h[0] = (h[0] - 1) % P
            g = pgcd(f, h, P)
            if 1 < len(g) < len(f):
                q = pdiv_exact(f, g, P)
                return split(g) + split(q)
    return split(poly)


def pdiv_exact(a, b, P):
    a = [x % P for x in a]
    q = [0] * (len(a) - len(b) + 1)
    inv = pow(b[-1], P - 2, P)
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1] * inv % P
        q[i] = c
        for j in range(len(b)):
            a[i + j] = (a[i + j] - c * b[j]) % P
    return q


class ModEmbed:
    """all embeddings of F (or L) into F_P."""

    def __init__(self, N, phi_poly_deg, p_ext, P, rng):
        self.N, self.P = N, P
        self.units = [j for j in range(1, N) if math.gcd(j, N) == 1]
        assert len(self.units) == phi_poly_deg
        self.n = phi_poly_deg
        r = prim_root_of_unity(N, P)
        self.rj = [pow(r, j, P) for j in self.units]
        # power table T[j][i] = rj^i
        self.T = np.array([[pow(rv, i, P) for i in range(self.n)] for rv in self.rj], dtype=object)
        self.k = 1
        self.roots = None
        if p_ext is not None:
            self.k = len(p_ext) - 1
            self.roots = []
            for jj in range(len(self.units)):
                coeffs = [self.evalF_single(c, jj) for c in p_ext]
                rts = roots_mod(coeffs, P, rng)
                if rts is None or len(rts) != self.k:
                    raise ValueError("p does not split mod P")
                self.roots.append(rts)
        self.E = self.n * self.k

    def evalF_single(self, x, jj):
        a, den = x
        P = self.P
        s = 0
        rv = self.rj[jj]
        pw = 1
        for ai in a:
            if ai:
                s += ai * pw
            pw = pw * rv % P
        dm = den % P
        if dm == 0:
            raise ZeroDivisionError
        return s % P * pow(dm, P - 2, P) % P

    def evalF(self, x):
        """values of F element under all phi(N) embeddings (list of ints)."""
        a, den = x
        P = self.P
        dm = den % P
        if dm == 0:
            raise ZeroDivisionError
        dinv = pow(dm, P - 2, P)
        am = [ai % P for ai in a]
        out = []
        for jj in range(self.n):
            s = 0
            row = self.T[jj]
            for i, ai in enumerate(am):
                if ai:
                    s += ai * row[i]
            out.append(s % P * dinv % P)
        return out

    def eval(self, x):
        """values under all E embeddings; x is F element (k==1) or tuple of F elements."""
        P = self.P
        if self.k == 1 and not (isinstance(x, tuple) and len(x) > 0 and isinstance(x[0], tuple) and isinstance(x[0][0], tuple)):
            return self.evalF(x)
        coeffs = [self.evalF(c) for c in x]      # k lists of length n
        out = []
        for jj in range(self.n):
            for s in range(self.k):
                rt = self.roots[jj][s]
                acc, pw = 0, 1
                for b in range(self.k):
                    acc += coeffs[b][jj] * pw
                    pw = pw * rt % P
                out.append(acc % P)
        return out

    def recon_matrix_inv(self):
        """inverse (mod P) of the E x E evaluation matrix: rows = embeddings (jj, s), cols = monomials (i, b)."""
        P = self.P
        E = self.E
        M = []
        for jj in range(self.n):
            for s in range(self.k):
                rt = self.roots[jj][s] if self.k > 1 else 1
                row = []
                for i in range(self.n):
                    for b in range(self.k):
                        row.append(pow(self.rj[jj], i, P) * pow(rt, b, P) % P)
                M.append(row)
        return mat_inv_mod(M, P)


def mat_inv_mod(M, P):
    n = len(M)
    A = [list(r) + [1 if i == j else 0 for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] % P)
        A[c], A[p] = A[p], A[c]
        iv = pow(A[c][c], P - 2, P)
        A[c] = [x * iv % P for x in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]
                A[r] = [(x - f * y) % P for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]


def rat_recon(x, M):
    """rational reconstruction of x mod M; returns Fraction or None."""
    x %= M
    bound = math.isqrt(M // 2)
    r0, r1 = M, x
    s0, s1 = 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    if math.gcd(r1, abs(s1)) != 1:
        return None
    return Fraction(r1, s1)


def solve(Mat, rhs, N, n_phi, p_ext=None, verbose=False, max_primes=4000, check=None, seed=1):
    """Mat: m x m list of lists of exact elements, rhs: m exact elements.
    Returns list of m exact elements (F or L representation), or raises."""
    rng = random.Random(seed)
    m = len(Mat)
    k = 1 if p_ext is None else len(p_ext) - 1
    P = (1 << 31) - 1
    # step P down to primes = 1 mod N
    P = P - (P % N) + 1
    if P >= (1 << 31):
        P -= N
    residues = []          # list of (P, array of shape (m, n*k) coefficients mod P)
    flat = flatten(Mat, rhs, m, k, n_phi)
    pivots = None
    last = None
    M_acc = 1
    acc = None
    nprimes = 0
    while nprimes < max_primes:
        P -= N
        if not is_prime(P):
            continue
        try:
            emb = ModEmbed(N, n_phi, p_ext, P, rng)
        except (ValueError, ZeroDivisionError):
            continue
        E = emb.E
        try:
            A = eval_all(emb, flat, m, k, P)
        except ZeroDivisionError:
            continue
        # Gaussian elimination (Gauss-Jordan) vectorised over embeddings
        piv_this = []
        rows_used = np.zeros(m, dtype=bool)
        ok = True
        cols_iter = range(m) if pivots is None else [c for (_, c) in pivots]
        order = []
        for c in cols_iter:
            if pivots is None:
                cand = [r for r in range(m) if not rows_used[r] and np.all(A[:, r, c] % P != 0)]
                if not cand:
                    continue
                r = cand[0]
            else:
                r = dict((cc, rr) for (rr, cc) in pivots)[c]
                if not np.all(A[:, r, c] % P != 0):
                    ok = False
                    break
            rows_used[r] = True
            order.append((r, c))
            pv = A[:, r, c] % P
            inv = np.array([pow(int(v), P - 2, P) for v in pv], dtype=np.int64)
            A[:, r, :] = (A[:, r, :] * inv[:, None]) % P
            f = A[:, :, c].copy()
            f[:, r] = 0
            # A[e, i, :] -= f[e, i] * A[e, r, :]
            A = (A - (f[:, :, None] * A[:, r, None, :]) % P) % P
        if not ok:
            continue
        if pivots is None:
            pivots = order
            if verbose:
                print(f"   modsolve: rank {len(pivots)} of {m}", flush=True)
        # consistency of non-pivot rows
        used_rows = set(r for r, c in pivots)
        for r in range(m):
            if r not in used_rows:
                if np.any(A[:, r, m] % P != 0):
                    raise ValueError("inconsistent system (mod P)")
        # solution values per embedding: z_c = A[:, r, m] for pivot (r, c); others 0
        Z = np.zeros((E, m), dtype=object)
        for (r, c) in pivots:
            Z[:, c] = A[:, r, m]
        # reconstruct monomial coefficients mod P: coeff = Rinv @ values
        if k == 1:
            Rinv = mat_inv_mod([[pow(emb.rj[jj], i, P) for i in range(emb.n)] for jj in range(emb.n)], P)
        else:
            Rinv = emb.recon_matrix_inv()
        Rinv = np.array(Rinv, dtype=object)
        C = (Rinv.dot(Z)) % P            # shape (n*k, m): coefficient (i,b) of unknown c
        nprimes += 1
        if acc is None:
            acc = C.astype(object)
            M_acc = P
        else:
            # CRT combine
            inv = pow(M_acc % P, P - 2, P)
            diff = ((C - acc) % P * inv) % P
            acc = acc + M_acc * diff
            M_acc *= P
        if nprimes % 20 == 0 or nprimes < 3:
            # attempt reconstruction
            rec = try_recon(acc, M_acc)
            if rec is not None:
                sol = to_elements(rec, m, emb.n, k)
                if not modcheck(Mat, rhs, sol, m, k, N, n_phi, p_ext, P - 2 * N, rng, pivots):
                    continue
                if check is None or check(sol):
                    if verbose:
                        print(f"   modsolve: success with {nprimes} primes ({M_acc.bit_length()} bits)", flush=True)
                    return sol
            if verbose and nprimes % 100 == 0:
                print(f"   modsolve: {nprimes} primes, {M_acc.bit_length()} bits", flush=True)
    raise RuntimeError("modsolve: too many primes")


def is_zero_elem(x):
    if isinstance(x[0], tuple) and len(x) and isinstance(x[0][0], tuple):
        return all(all(v == 0 for v in c[0]) for c in x)
    return all(v == 0 for v in x[0])


def try_recon(acc, M):
    out = np.empty(acc.shape, dtype=object)
    for idx in np.ndindex(acc.shape):
        v = int(acc[idx])
        if v == 0:
            out[idx] = Fraction(0)
            continue
        fr = rat_recon(v, M)
        if fr is None:
            return None
        out[idx] = fr
    return out


def to_elements(rec, m, n, k):
    sol = []
    for c in range(m):
        comps = []
        for b in range(k):
            coeffs = [rec[i * k + b, c] for i in range(n)]
            den = 1
            for fr in coeffs:
                den = den * fr.denominator // math.gcd(den, fr.denominator)
            a = tuple(int(fr * den) for fr in coeffs)
            g = den
            for ai in a:
                g = math.gcd(g, ai)
            if g > 1:
                a = tuple(ai // g for ai in a)
                den //= g
            comps.append((a, den))
        sol.append(comps[0] if k == 1 else tuple(comps))
    return sol


def flatten(Mat, rhs, m, k, n):
    """numerators num[(i,j), b, c] and denominators den[(i,j), b] as Python-int lists (column m = rhs)."""
    nums, dens = [], []
    for i in range(m):
        row = list(Mat[i]) + [rhs[i]]
        for x in row:
            comps = [x] if k == 1 else list(x)
            for (a, dn) in comps:
                nums.append(a)
                dens.append(dn)
    return nums, dens


def eval_all(emb, flat, m, k, P):
    nums, dens = flat
    n = emb.n
    cnt = len(dens)
    num = np.array([[ai % P for ai in a] for a in nums], dtype=np.int64)     # (cnt, n)
    den = np.array([dn % P for dn in dens], dtype=np.int64)
    if np.any(den == 0):
        raise ZeroDivisionError
    # modular inverse of den (vectorised via Fermat with repeated squaring)
    inv = np.ones(cnt, dtype=np.int64)
    base = den.copy()
    e = P - 2
    while e:
        if e & 1:
            inv = (inv * base) % P
        base = (base * base) % P
        e >>= 1
    T = np.array(emb.T, dtype=np.int64)     # (n_emb, n)
    vals = np.zeros((cnt, n), dtype=np.int64)
    for i in range(n):
        vals = (vals + (num[:, i:i + 1] * T[None, :, i]) % P) % P
    vals = (vals * inv[:, None]) % P       # (cnt, n) : F-embedding values
    if k == 1:
        W = vals                            # (cnt, n)
    else:
        vals = vals.reshape(m * (m + 1), k, n)          # entry, b, j
        R = np.array(emb.roots, dtype=np.int64)          # (n, k): root s for embedding j
        W = np.zeros((m * (m + 1), n, k), dtype=np.int64)
        pw = np.ones((n, k), dtype=np.int64)
        for b in range(k):
            W = (W + (vals[:, b, :, None] * pw[None, :, :]) % P) % P
            pw = (pw * R) % P
        W = W.reshape(m * (m + 1), n * k)
    E = W.shape[1]
    return np.ascontiguousarray(W.T.reshape(E, m, m + 1))


def modcheck(Mat, rhs, sol, m, k, N, n_phi, p_ext, Pstart, rng, pivots):
    """probabilistic check of Mat sol = rhs modulo a fresh prime (rows of the pivot pattern)."""
    P = Pstart - (Pstart % N) + 1
    while True:
        P -= N
        if not is_prime(P):
            continue
        try:
            emb = ModEmbed(N, n_phi, p_ext, P, rng)
            A = eval_all(emb, flatten(Mat, rhs, m, k, n_phi), m, k, P)       # (E, m, m+1)
            Z = eval_all(emb, flatten([[x] for x in sol], [F0 for F0 in sol], m, k, n_phi), m, k, P) if False else None
        except (ValueError, ZeroDivisionError):
            continue
        break
    # evaluate solution entries
    E = emb.E
    zs = np.zeros((E, m), dtype=np.int64)
    for c in range(m):
        x = sol[c]
        if is_zero_elem(x):
            continue
        zs[:, c] = np.array(emb.eval(x), dtype=np.int64) % P
    lhs = np.zeros((E, m), dtype=np.int64)
    for c in range(m):
        lhs = (lhs + (A[:, :, c] * zs[:, c:c + 1]) % P) % P
    return bool(np.all((lhs - A[:, :, m]) % P == 0))
