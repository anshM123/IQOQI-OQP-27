"""
modsolve2.py -- multi-modular exact solver for square systems M z = r over
   F = Q(zeta_N)  or  L = F[t]/(p(t))  (p monic over F),
using primes P = 1 mod N (zeta -> r^j, j in (Z/N)^*) and, for L, the algebras
A_j = F_P[t]/(p^{sigma_j}(t)) (no root finding; p^{sigma_j} squarefree mod P required).
Vectorised Gauss-Jordan over all embeddings; coefficient reconstruction by inverting the
Vandermonde in zeta; CRT + rational reconstruction; fast modular re-check; caller's exact check.
"""
import math
import random
import numpy as np
from fractions import Fraction
from modsolve import is_prime, prim_root_of_unity, rat_recon, mat_inv_mod, try_recon, to_elements, is_zero_elem


def _flatten(rows_list, k):
    nums, dens = [], []
    for row in rows_list:
        for x in row:
            comps = [x] if k == 1 else list(x)
            for (a, dn) in comps:
                nums.append(a)
                dens.append(dn)
    return nums, dens


def _modinv_vec(den, P):
    inv = np.ones(den.shape, dtype=np.int64)
    base = den.copy() % P
    e = P - 2
    while e:
        if e & 1:
            inv = (inv * base) % P
        base = (base * base) % P
        e >>= 1
    return inv


class Emb:
    def __init__(self, N, n, p_ext, P):
        self.N, self.n, self.P = N, n, P
        self.units = [j for j in range(1, N) if math.gcd(j, N) == 1]
        assert len(self.units) == n
        r = prim_root_of_unity(N, P)
        self.rj = [pow(r, j, P) for j in self.units]
        self.T = np.array([[pow(rv, i, P) for i in range(n)] for rv in self.rj], dtype=np.int64)
        self.k = 1 if p_ext is None else len(p_ext) - 1
        if p_ext is not None:
            # p_j coefficients (monic): pc[j, b] for b = 0..k
            vals = self.evalF_many([c for c in p_ext])      # (k+1, n)
            self.pc = vals.T.copy()                          # (n, k+1)
            for j in range(n):
                pj = [int(v) for v in self.pc[j]]
                dp = [(i * pj[i]) % P for i in range(1, len(pj))]
                if len(_pgcd(pj, dp, P)) > 1:
                    raise ValueError("not squarefree")

    def evalF_many(self, elems):
        """elems: list of F elements -> array (len, n) of values mod P"""
        P = self.P
        num = np.array([[ai % P for ai in a] for (a, dn) in elems], dtype=np.int64)
        den = np.array([dn % P for (a, dn) in elems], dtype=np.int64)
        if np.any(den == 0):
            raise ZeroDivisionError
        inv = _modinv_vec(den, P)
        vals = np.zeros((len(elems), self.n), dtype=np.int64)
        for i in range(self.n):
            vals = (vals + (num[:, i:i + 1] * self.T[None, :, i]) % P) % P
        return (vals * inv[:, None]) % P


def _pgcd(a, b, P):
    from modsolve import pgcd
    return pgcd(a, b, P)


# ---- polynomial arithmetic in A_j = F_P[t]/(p_j), vectorised: arrays (..., n, k)
def amul(x, y, pc, P):
    """x, y: (..., n, k); pc: (n, k+1) monic. returns (..., n, k)"""
    k = x.shape[-1]
    prod = np.zeros(x.shape[:-1] + (2 * k - 1,), dtype=np.int64)
    for a in range(k):
        for b in range(k):
            prod[..., a + b] = (prod[..., a + b] + (x[..., a] * y[..., b]) % P) % P
    for dgr in range(2 * k - 2, k - 1, -1):
        c = prod[..., dgr]
        for j in range(k):
            prod[..., dgr - k + j] = (prod[..., dgr - k + j] - (c * pc[:, j]) % P) % P
        prod[..., dgr] = 0
    return prod[..., :k]


def ainv_scalar(xs, pc, P):
    """invert elements xs: (n, k) in A_j (per j), via extended Euclid on polynomials mod P."""
    from modsolve import pmod, pmul
    n, k = xs.shape
    out = np.zeros((n, k), dtype=np.int64)
    for j in range(n):
        a = [int(v) for v in xs[j]]
        m = [int(v) for v in pc[j]]
        # extended Euclid: find u with u*a = 1 mod m
        r0, r1 = m[:], pmod(a, m, P)
        s0, s1 = [0], [1]
        while r1 and any(r1):
            # polynomial division r0 / r1
            q, r = _pdivmod(r0, r1, P)
            r0, r1 = r1, r
            s0, s1 = s1, _psub(s0, pmul(q, s1, P), P)
        # r0 is gcd (constant if invertible)
        while r0 and r0[-1] == 0:
            r0.pop()
        if len(r0) != 1:
            raise ZeroDivisionError
        c = pow(r0[0], P - 2, P)
        u = pmod([x * c % P for x in s0], m, P)
        u = u + [0] * (k - len(u))
        out[j] = u[:k]
    return out


def _psub(a, b, P):
    L = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % P for i in range(L)]


def _pdivmod(a, b, P):
    a = [x % P for x in a]
    while a and a[-1] == 0:
        a.pop()
    b = [x % P for x in b]
    while b and b[-1] == 0:
        b.pop()
    if len(a) < len(b):
        return [0], a
    q = [0] * (len(a) - len(b) + 1)
    inv = pow(b[-1], P - 2, P)
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1] * inv % P
        q[i] = c
        for j in range(len(b)):
            a[i + j] = (a[i + j] - c * b[j]) % P
    r = a[:len(b) - 1]
    while r and r[-1] == 0:
        r.pop()
    return q, r


def solve(Mat, rhs, N, n_phi, p_ext=None, verbose=False, max_primes=6000, check=None):
    m = len(Mat)
    k = 1 if p_ext is None else len(p_ext) - 1
    n = n_phi
    rows_list = [list(Mat[i]) + [rhs[i]] for i in range(m)]
    nums, dens = _flatten(rows_list, k)
    P = (1 << 31) - 1
    P = P - (P % N) + 1
    while P >= (1 << 31):
        P -= N
    pivots = None
    acc = None
    M_acc = 1
    nprimes = 0
    used_primes = []
    while nprimes < max_primes:
        P -= N
        if not is_prime(P):
            continue
        try:
            emb = Emb(N, n, p_ext, P)
            num = np.array([[ai % P for ai in a] for a in nums], dtype=np.int64)
            den = np.array([dn % P for dn in dens], dtype=np.int64)
            if np.any(den == 0):
                continue
            inv = _modinv_vec(den, P)
            vals = np.zeros((len(dens), n), dtype=np.int64)
            for i in range(n):
                vals = (vals + (num[:, i:i + 1] * emb.T[None, :, i]) % P) % P
            vals = (vals * inv[:, None]) % P                 # (m*(m+1)*k, n)
            A = vals.reshape(m, m + 1, k, n).transpose(3, 0, 1, 2).copy()   # (n, m, m+1, k)
        except (ValueError, ZeroDivisionError):
            continue
        pc = emb.pc if k > 1 else None
        # Gauss-Jordan over all n embeddings simultaneously, entries in A_j (k-vectors)
        ok = True
        order = []
        rows_used = np.zeros(m, dtype=bool)
        cols_iter = range(m) if pivots is None else [c for (_, c) in pivots]
        pivmap = None if pivots is None else {c: r for (r, c) in pivots}
        try:
            for c in cols_iter:
                if pivots is None:
                    r = None
                    for rr in range(m):
                        if rows_used[rr]:
                            continue
                        if np.all(np.any(A[:, rr, c, :] % P != 0, axis=-1)):
                            r = rr
                            break
                    if r is None:
                        continue
                else:
                    r = pivmap[c]
                rows_used[r] = True
                order.append((r, c))
                pv = A[:, r, c, :]                                    # (n, k)
                if k == 1:
                    if np.any(pv[:, 0] % P == 0):
                        raise ZeroDivisionError
                    ivv = _modinv_vec(pv[:, 0], P)[:, None]
                    A[:, r, :, :] = (A[:, r, :, :] * ivv[:, None, :]) % P
                    f = A[:, :, c, :].copy()
                    f[:, r, :] = 0
                    A = (A - (f[:, :, None, :] * A[:, r, None, :, :]) % P) % P
                else:
                    ivv = ainv_scalar(pv, pc, P)                      # (n, k)
                    rowr = A[:, r, :, :]                              # (n, m+1, k)
                    A[:, r, :, :] = amul(rowr.transpose(1, 0, 2), np.broadcast_to(ivv, rowr.transpose(1, 0, 2).shape), pc, P).transpose(1, 0, 2)
                    f = A[:, :, c, :].copy()                          # (n, m, k)
                    f[:, r, :] = 0
                    # A[j, i, :, :] -= f[j, i] * A[j, r, :, :]
                    prod = amul(np.broadcast_to(f[:, :, None, :], A.shape).transpose(1, 2, 0, 3),
                                np.broadcast_to(A[:, r, None, :, :], A.shape).transpose(1, 2, 0, 3), pc, P).transpose(2, 0, 1, 3)
                    A = (A - prod) % P
        except ZeroDivisionError:
            continue
        if pivots is None:
            pivots = order
            if verbose:
                print(f"   modsolve2: rank {len(pivots)} of {m}", flush=True)
        # solution per embedding j: z_c(j) = A[j, r, m, :] (k-vector in t)
        Z = np.zeros((n, m, k), dtype=np.int64)
        for (r, c) in pivots:
            Z[:, c, :] = A[:, r, m, :]
        # coefficients: for each (c, b): values over j -> coefficients in zeta^i via inverse Vandermonde
        V = [[pow(emb.rj[j], i, P) for i in range(n)] for j in range(n)]
        Vinv = np.array(mat_inv_mod(V, P), dtype=object)
        Zo = Z.astype(object).reshape(n, m * k)
        C = (Vinv.dot(Zo)) % P                     # (n [i], m*k)
        # order coefficients as (i*k + b, c) like modsolve.to_elements expects
        C2 = np.empty((n * k, m), dtype=object)
        for i in range(n):
            for c in range(m):
                for b in range(k):
                    C2[i * k + b, c] = C[i, c * k + b]
        nprimes += 1
        used_primes.append(P)
        if acc is None:
            acc = C2
            M_acc = P
        else:
            invM = pow(M_acc % P, P - 2, P)
            diff = ((C2 - acc) % P * invM) % P
            acc = acc + M_acc * diff
            M_acc *= P
        if nprimes % 10 == 0 or nprimes < 3:
            rec = try_recon(acc, M_acc)
            if rec is not None:
                sol = to_elements(rec, m, n, k)
                if check is None or check(sol):
                    if verbose:
                        print(f"   modsolve2: success with {nprimes} primes ({M_acc.bit_length()} bits)", flush=True)
                    return sol
            if verbose and nprimes % 100 == 0:
                print(f"   modsolve2: {nprimes} primes, {M_acc.bit_length()} bits", flush=True)
    raise RuntimeError("modsolve2: too many primes")
