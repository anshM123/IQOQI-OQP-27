"""
dixon2.py -- memory-lean version of dixon.py (same algorithm and interface, SOLVER=dixon2 in cert_povm.py):
the integer matrix Mi is stored as n sparse CSR matrices (one per power-basis coefficient), the embedded
matrices are factorised IN PLACE with the trailing update done in row chunks, so peak memory is about
8 n m^2 bytes (one dense int64 copy of the embedded system) plus small chunks.

Solves M z = r over Q(zeta_N) exactly by p-adic (Dixon) lifting; see dixon.py for the description.
"""
import math
import time
import numpy as np
import scipy.sparse as sp
from fractions import Fraction
from modsolve import is_prime, prim_root_of_unity, mat_inv_mod, rat_recon
from cyclo import cyclotomic_poly

CHUNK = 128


def _lu_mod_inplace(A, P):
    """in-place LU of A (n, m, m) int64 mod P with a common row permutation; returns perm, invdiag."""
    n, m, _ = A.shape
    perm = np.arange(m)
    invdiag = np.zeros((n, m), dtype=np.int64)
    for c in range(m):
        cand = np.all(A[:, c:, c] != 0, axis=0)
        idx = np.nonzero(cand)[0]
        if len(idx) == 0:
            raise ZeroDivisionError("no common pivot")
        r = c + int(idx[0])
        if r != c:
            tmp = A[:, c, :].copy()
            A[:, c, :] = A[:, r, :]
            A[:, r, :] = tmp
            perm[[c, r]] = perm[[r, c]]
        inv = np.array([pow(int(x), P - 2, P) for x in A[:, c, c]], dtype=np.int64)
        invdiag[:, c] = inv
        if c + 1 < m:
            urow = A[:, c, c + 1:]                                  # (n, m-c-1)
            for r0 in range(c + 1, m, CHUNK):
                r1 = min(m, r0 + CHUNK)
                L = (A[:, r0:r1, c] * inv[:, None]) % P             # (n, chunk)
                A[:, r0:r1, c] = L
                A[:, r0:r1, c + 1:] = (A[:, r0:r1, c + 1:] - (L[:, :, None] * urow[:, None, :]) % P) % P
    return perm, invdiag


def _lu_solve(LU, perm, invdiag, b, P):
    n, m, _ = LU.shape
    y = b[:, perm].copy()
    for c in range(1, m):
        y[:, c] = (y[:, c] - np.sum((LU[:, c, :c] * y[:, :c]) % P, axis=1)) % P
    x = np.zeros_like(y)
    for c in range(m - 1, -1, -1):
        s = np.sum((LU[:, c, c + 1:] * x[:, c + 1:]) % P, axis=1) % P if c + 1 < m else 0
        x[:, c] = (((y[:, c] - s) % P) * invdiag[:, c]) % P
    return x


def _polymul_reduce(Ms, C, phi, n):
    m = C.shape[0]
    full = np.zeros((m, 2 * n - 1), dtype=np.int64)
    for a, Ma in enumerate(Ms):
        if Ma.nnz:
            full[:, a:a + n] += Ma @ C
    for k in range(2 * n - 2, n - 1, -1):
        coef = full[:, k].copy()
        if coef.any():
            full[:, k - n:k] -= coef[:, None] * phi[None, :n]
        full[:, k] = 0
    return full[:, :n]


def _exact_check(rows_nz, A0, R, Zn, Den, phi, n):
    m = len(A0)
    for i in range(m):
        acc = [0] * (2 * n - 1)
        for (k, mk) in rows_nz[i]:
            zk = Zn[k]
            for a, ma in mk:
                for b_, zb in enumerate(zk):
                    if zb:
                        acc[a + b_] += ma * zb
        for k in range(2 * n - 2, n - 1, -1):
            c = acc[k]
            if c:
                for s in range(n):
                    acc[k - n + s] -= c * phi[s]
            acc[k] = 0
        if [R[i] * acc[s] for s in range(n)] != [Den * A0[i][s] for s in range(n)]:
            return False
    return True


def solve(Mat, rhs, N, n, verbose=False, check=None, max_steps=3000, recon_every=6):
    t0 = time.time()
    m = len(Mat)
    phi = np.array(cyclotomic_poly(N), dtype=np.int64)
    assert len(phi) == n + 1 and phi[-1] == 1
    Dm = 1
    for row in Mat:
        for (a, den) in row:
            if any(a):
                Dm = Dm * den // math.gcd(Dm, den)
    rows_a = [[] for _ in range(n)]
    cols_a = [[] for _ in range(n)]
    vals_a = [[] for _ in range(n)]
    rows_nz = [[] for _ in range(m)]
    maxM = 0
    for i, row in enumerate(Mat):
        for k, (a, den) in enumerate(row):
            if any(a):
                f = Dm // den
                mk = []
                for s, v in enumerate(a):
                    if v:
                        vv = int(v) * f
                        assert abs(vv) < 2 ** 40
                        maxM = max(maxM, abs(vv))
                        rows_a[s].append(i)
                        cols_a[s].append(k)
                        vals_a[s].append(vv)
                        mk.append((s, vv))
                rows_nz[i].append((k, mk))
    Ms = [sp.csr_matrix((np.array(vals_a[s], dtype=np.int64), (rows_a[s], cols_a[s])), shape=(m, m))
          for s in range(n)]
    A = [[Dm * int(v) for v in a] for (a, R_) in rhs]
    A0 = [list(row) for row in A]
    R = [int(R_) for (a, R_) in rhs]
    phimax = int(np.abs(phi).max())
    budget = 61 - math.ceil(math.log2(max(1, maxM) * m * n * (1 + phimax) * n + 1))
    pbits = min(31, budget)
    assert pbits >= 20, f"matrix entries too large for int64 lifting (budget {budget} bits)"
    P = (1 << pbits) - 1
    P = P - (P % N) + 1
    while True:
        P -= N
        if P < (1 << (pbits - 1)):
            raise RuntimeError("no prime found")
        if not is_prime(P) or any(Ri % P == 0 for Ri in R):
            continue
        w = prim_root_of_unity(N, P)
        ex = [e for e in range(1, N) if math.gcd(e, N) == 1]
        assert len(ex) == n
        roots = [pow(w, e, P) for e in ex]
        V = [[pow(r, s, P) for s in range(n)] for r in roots]
        Vinv = mat_inv_mod(V, P)
        Vn = np.array(V, dtype=np.int64)
        Vinvn = np.array([[int(x) for x in row] for row in Vinv], dtype=np.int64)
        Me = np.zeros((n, m, m), dtype=np.int64)
        for s in range(n):
            if Ms[s].nnz == 0:
                continue
            coo = Ms[s].tocoo()
            vmod = coo.data % P
            for j in range(n):
                np.add.at(Me[j], (coo.row, coo.col), (vmod * Vn[j, s]) % P)
        Me %= P
        try:
            perm, invdiag = _lu_mod_inplace(Me, P)
        except ZeroDivisionError:
            del Me
            continue
        break
    LU = Me
    if verbose:
        print(f"   dixon2: m={m} n={n} prime {P} ({pbits} bits), LU done [{time.time() - t0:.1f}s]", flush=True)
    invR = [pow(Ri % P, P - 2, P) for Ri in R]
    Zacc = [[0] * n for _ in range(m)]
    Ppow = 1
    for t in range(max_steps):
        rc = np.array([[((A[i][s] % P) * invR[i]) % P for s in range(n)] for i in range(m)], dtype=np.int64)
        re = np.sum((Vn[:, None, :] * rc[None, :, :]) % P, axis=2) % P
        xe = _lu_solve(LU, perm, invdiag, re, P)
        cc = np.sum((Vinvn[None, :, :] * xe.T[:, None, :]) % P, axis=2) % P
        for i in range(m):
            zi = Zacc[i]
            ci = cc[i]
            for s in range(n):
                if ci[s]:
                    zi[s] += int(ci[s]) * Ppow
        Ppow *= P
        Mc = _polymul_reduce(Ms, cc, phi, n)
        for i in range(m):
            Ri = R[i]
            Ai = A[i]
            mci = Mc[i]
            for s in range(n):
                q, rem = divmod(Ai[s] - Ri * int(mci[s]), P)
                assert rem == 0, "Dixon lifting: residual not divisible"
                Ai[s] = q
        if (t + 1) % recon_every == 0:
            ok = True
            fr = [[None] * n for _ in range(m)]
            for i in range(m):
                for s in range(n):
                    v = Zacc[i][s] % Ppow
                    if v == 0:
                        fr[i][s] = Fraction(0)
                        continue
                    x = rat_recon(v, Ppow)
                    if x is None:
                        ok = False
                        break
                    fr[i][s] = x
                if not ok:
                    break
            if ok:
                Den = 1
                for i in range(m):
                    for x in fr[i]:
                        Den = Den * x.denominator // math.gcd(Den, x.denominator)
                Zn = [[int(x * Den) for x in fr[i]] for i in range(m)]
                if _exact_check(rows_nz, A0, R, Zn, Den, [int(v) for v in phi], n):
                    sol = []
                    for i in range(m):
                        a = tuple(Zn[i])
                        g = Den
                        for ai in a:
                            g = math.gcd(g, ai)
                        sol.append((tuple(ai // g for ai in a), Den // g))
                    if verbose:
                        print(f"   dixon2: solved after {t + 1} lifting steps ({Ppow.bit_length()} bits), exact check OK "
                              f"[{time.time() - t0:.1f}s]", flush=True)
                    return sol
            if verbose and (t + 1) % (recon_every * 5) == 0:
                print(f"   dixon2: {t + 1} steps ({Ppow.bit_length()} bits) [{time.time() - t0:.1f}s]", flush=True)
    raise RuntimeError("dixon2: no reconstruction")
