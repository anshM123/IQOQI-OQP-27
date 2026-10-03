"""
dixon.py -- exact solver for square linear systems  M z = r  over Q(zeta_N) by p-adic (Dixon) lifting.

Used by cert_povm.py (SOLVER=dixon) for the exact projection step; much faster than multi-modular CRT
(modsolve2.py) when many primes are needed: ONE LU factorisation modulo a prime p = 1 (mod N) per embedding
zeta -> r_j (p splits completely, Z[zeta]/p = F_p^n), then each lifting step costs only triangular solves and one
exact matrix-vector product over Z[zeta].
  M = Mi / Dm with Mi in Z[zeta]^{m x m} (small integer coefficients), r_i = A_i / R_i (A_i in Z[zeta], R_i in Z).
  Lifting:  c_t = Mi^{-1} b^(t) mod p (coefficient form in [0, p)),  b^(t+1) = (b^(t) - Mi c_t)/p  (exact),
  z = sum_t p^t c_t solves Mi z = Dm r;  rational reconstruction coefficient-wise; exact verification
  R_i (Mi Zn)_i = Den A_i  (z = Zn/Den, A_i = Dm a_i, r_i = a_i/R_i).
Elements are (tuple of n ints, positive int denominator) in the power basis 1, zeta, ..., zeta^{n-1} mod Phi_N,
as in cyclo.py.
"""
import math
import time
import numpy as np
from fractions import Fraction
from modsolve import is_prime, prim_root_of_unity, mat_inv_mod, rat_recon
from cyclo import cyclotomic_poly


def _lu_mod(Me, P):
    """LU with a common row permutation for all embeddings; Me (n, m, m) int64 mod P. Returns LU, perm, invdiag."""
    n, m, _ = Me.shape
    A = Me.copy()
    perm = np.arange(m)
    invdiag = np.zeros((n, m), dtype=np.int64)
    for c in range(m):
        cand = np.all(A[:, c:, c] != 0, axis=0)
        idx = np.nonzero(cand)[0]
        if len(idx) == 0:
            raise ZeroDivisionError("no common pivot")
        r = c + int(idx[0])
        if r != c:
            A[:, [c, r], :] = A[:, [r, c], :]
            perm[[c, r]] = perm[[r, c]]
        piv = A[:, c, c]
        inv = np.array([pow(int(x), P - 2, P) for x in piv], dtype=np.int64)
        invdiag[:, c] = inv
        if c + 1 < m:
            L = (A[:, c + 1:, c] * inv[:, None]) % P
            A[:, c + 1:, c] = L
            A[:, c + 1:, c + 1:] = (A[:, c + 1:, c + 1:] - (L[:, :, None] * A[:, c, None, c + 1:]) % P) % P
    return A, perm, invdiag


def _lu_solve(LU, perm, invdiag, b, P):
    """solve LU x = b[:, perm] for all embeddings; b (n, m)."""
    n, m, _ = LU.shape
    y = b[:, perm].copy()
    for c in range(1, m):
        y[:, c] = (y[:, c] - np.sum((LU[:, c, :c] * y[:, :c]) % P, axis=1)) % P
    x = np.zeros_like(y)
    for c in range(m - 1, -1, -1):
        s = np.sum((LU[:, c, c + 1:] * x[:, c + 1:]) % P, axis=1) % P if c + 1 < m else 0
        x[:, c] = (((y[:, c] - s) % P) * invdiag[:, c]) % P
    return x


def _polymul_reduce(Mi, C, phi):
    """exact (Mi C) over Z[zeta]: Mi (m, m, n) int64, C (m, n) int64 -> (m, n) int64, reduced mod Phi_N (monic)."""
    m, _, n = Mi.shape
    full = np.zeros((m, 2 * n - 1), dtype=np.int64)
    for a in range(n):
        Ma = Mi[:, :, a]
        if not Ma.any():
            continue
        full[:, a:a + n] += Ma @ C
    for k in range(2 * n - 2, n - 1, -1):
        coef = full[:, k].copy()
        if coef.any():
            full[:, k - n:k] -= coef[:, None] * phi[None, :n]
        full[:, k] = 0
    return full[:, :n]


def _exact_check(Mi, Dm, A0, R, Zn, Den, phi):
    """exact: R_i * (Mi Zn)_i == Den * A0_i  (python ints), with z = Zn/Den, M = Mi/Dm, r_i = A0_i/(Dm R_i)...
    here A0 already includes the factor Dm (b = Dm r = A0/R)."""
    m, _, n = Mi.shape
    nz = [[(k, [int(v) for v in Mi[i, k]]) for k in np.nonzero(np.any(Mi[i] != 0, axis=1))[0]] for i in range(m)]
    for i in range(m):
        acc = [0] * (2 * n - 1)
        for (k, mk) in nz[i]:
            zk = Zn[k]
            for a, ma in enumerate(mk):
                if ma:
                    for b_, zb in enumerate(zk):
                        if zb:
                            acc[a + b_] += ma * zb
        for k in range(2 * n - 2, n - 1, -1):
            c = acc[k]
            if c:
                for s in range(n):
                    acc[k - n + s] -= c * phi[s]
            acc[k] = 0
        lhs = [R[i] * acc[s] for s in range(n)]
        rhs = [Den * A0[i][s] for s in range(n)]
        if lhs != rhs:
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
    Mi = np.zeros((m, m, n), dtype=np.int64)
    maxM = 0
    for i, row in enumerate(Mat):
        for k, (a, den) in enumerate(row):
            if any(a):
                f = Dm // den
                for s, v in enumerate(a):
                    if v:
                        vv = v * f
                        maxM = max(maxM, abs(vv))
                        assert abs(vv) < 2 ** 40
                        Mi[i, k, s] = vv
    # rhs: b_i = Dm * r_i = A_i / R_i
    A = [[Dm * int(v) for v in a] for (a, R) in rhs]
    A0 = [list(row) for row in A]
    R = [int(R_) for (a, R_) in rhs]
    # prime size: products Mi*c accumulate over <= m*n terms, then reduction by Phi_N (|coeffs| small)
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
        Mm = Mi % P
        Me = np.zeros((n, m, m), dtype=np.int64)
        for j in range(n):
            acc = np.zeros((m, m), dtype=np.int64)
            for s in range(n):
                if Vn[j, s]:
                    acc = (acc + (Mm[:, :, s] * Vn[j, s]) % P) % P
            Me[j] = acc
        try:
            LU, perm, invdiag = _lu_mod(Me, P)
        except ZeroDivisionError:
            continue
        break
    del Me
    if verbose:
        print(f"   dixon: m={m} n={n} prime {P} ({pbits} bits), LU done [{time.time() - t0:.1f}s]", flush=True)
    invR = [pow(Ri % P, P - 2, P) for Ri in R]
    Zacc = [[0] * n for _ in range(m)]
    Ppow = 1
    for t in range(max_steps):
        rc = np.array([[((A[i][s] % P) * invR[i]) % P for s in range(n)] for i in range(m)], dtype=np.int64)
        re = np.sum((Vn[:, None, :] * rc[None, :, :]) % P, axis=2) % P          # (n, m)
        xe = _lu_solve(LU, perm, invdiag, re, P)                                 # (n, m)
        cc = np.sum((Vinvn[None, :, :] * xe.T[:, None, :]) % P, axis=2) % P     # (m, n) coefficients in [0, P)
        for i in range(m):
            zi = Zacc[i]
            ci = cc[i]
            for s in range(n):
                if ci[s]:
                    zi[s] += int(ci[s]) * Ppow
        Ppow *= P
        Mc = _polymul_reduce(Mi, cc, phi)
        for i in range(m):
            Ri = R[i]
            Ai = A[i]
            mci = Mc[i]
            for s in range(n):
                v = Ai[s] - Ri * int(mci[s])
                q, rem = divmod(v, P)
                assert rem == 0, "Dixon lifting: residual not divisible"
                Ai[s] = q
        if (t + 1) % recon_every == 0:
            # rational reconstruction of z' = Mi^{-1} b mod P^(t+1); z = z' (b already scaled by Dm: M z = r <=> Mi z = Dm r)
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
                if _exact_check(Mi, Dm, A0, R, Zn, Den, [int(v) for v in phi]):
                    sol = []
                    for i in range(m):
                        a = tuple(Zn[i])
                        g = Den
                        for ai in a:
                            g = math.gcd(g, ai)
                        sol.append((tuple(ai // g for ai in a), Den // g))
                    if verbose:
                        print(f"   dixon: solved after {t + 1} lifting steps ({Ppow.bit_length()} bits), exact check OK "
                              f"[{time.time() - t0:.1f}s]", flush=True)
                    return sol
            if verbose and (t + 1) % (recon_every * 5) == 0:
                print(f"   dixon: {t + 1} steps ({Ppow.bit_length()} bits) [{time.time() - t0:.1f}s]", flush=True)
    raise RuntimeError("dixon: no reconstruction")
