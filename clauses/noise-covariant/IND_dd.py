"""
IND_dd.py -- independent exact double description (Motzkin), written from scratch 2026-10-09 (imports nothing from
the earlier DD files dd_exact.py / dd_fast.py / dd_numba.py / CLOSE_dd_safe.py).

  extreme_rays(A)        extreme rays of the pointed cone {h : A h >= 0}, A integer (m x n), rank n
  facets_of_points(P)    facets of conv(P) (P integer points spanning R^k): extreme rays of {(h0,h) : h0 + h.p >= 0}

Exactness.  int64 throughout with a CERTIFIED bound: after every step all ray entries satisfy |r| <= RMAX = 2^27
(checked; abort otherwise).  With |A| <= AMAX and n columns, |a.r| <= n AMAX RMAX and every combination
v_p r_q - v_q r_p is bounded by 2 n AMAX RMAX^2 < 2^63 (asserted at start).  New rays are divided by the gcd.
Adjacency (Fukuda-Prodon combinatorial test): rays p in R+, q in R- of the current cone are adjacent iff
|Z(p) & Z(q)| >= n-2 and no third current ray r has Z(r) containing Z(p) & Z(q); the containment test scans the
rays tight on the rarest constraint of Z(p) & Z(q).  Two parallel passes per step (count, then write).
Output check (always run): every output ray satisfies A r >= 0 exactly, its tight set equals the tracked zero set,
and the tight rows have rank n-1 (rank modulo the prime 2^31-1, which is a lower bound of the rational rank and is
<= n-1 for a nonzero ray; exact python-flint rank if the modular rank is deficient).  Rays are pairwise distinct.
"""
import time
import math
import numpy as np
import numba as nb
import flint

RMAX = 2 ** 27
PRIME = 2147483647

_M1 = np.uint64(0x5555555555555555)
_M2 = np.uint64(0x3333333333333333)
_M4 = np.uint64(0x0F0F0F0F0F0F0F0F)
_H1 = np.uint64(0x0101010101010101)


@nb.njit(cache=True, inline="always")
def _pc(x):
    x = x - ((x >> np.uint64(1)) & _M1)
    x = (x & _M2) + ((x >> np.uint64(2)) & _M2)
    x = (x + (x >> np.uint64(4))) & _M4
    return np.int64((x * _H1) >> np.uint64(56))


@nb.njit(cache=True)
def _gcd(a, b):
    a = abs(a)
    b = abs(b)
    while b != 0:
        a, b = b, a % b
    return a


@nb.njit(cache=True)
def _build_lists(Z, nr, W):
    M = 64 * W
    cnt = np.zeros(M + 1, np.int64)
    for k in range(nr):
        for w in range(W):
            x = Z[k, w]
            while x != np.uint64(0):
                low = x & (~x + np.uint64(1))
                b = _pc(low - np.uint64(1))
                cnt[64 * w + b + 1] += 1
                x = x ^ low
    for c in range(M):
        cnt[c + 1] += cnt[c]
    fill = cnt[:M].copy()
    lst = np.empty(cnt[M], np.int64)
    for k in range(nr):
        for w in range(W):
            x = Z[k, w]
            while x != np.uint64(0):
                low = x & (~x + np.uint64(1))
                b = _pc(low - np.uint64(1))
                c = 64 * w + b
                lst[fill[c]] = k
                fill[c] += 1
                x = x ^ low
    return cnt, lst


@nb.njit(cache=True, inline="always")
def _adjacent(p, q, Z, W, n, cnt, lst, common):
    pc = 0
    for w in range(W):
        common[w] = Z[p, w] & Z[q, w]
        pc += _pc(common[w])
    if pc < n - 2:
        return False
    best = -1
    bestlen = 1 << 62
    for w in range(W):
        x = common[w]
        while x != np.uint64(0):
            low = x & (~x + np.uint64(1))
            c = 64 * w + _pc(low - np.uint64(1))
            ln = cnt[c + 1] - cnt[c]
            if ln < bestlen:
                bestlen = ln
                best = c
            x = x ^ low
    for t in range(cnt[best], cnt[best + 1]):
        r = lst[t]
        if r == p or r == q:
            continue
        inside = True
        for w in range(W):
            if (Z[r, w] & common[w]) != common[w]:
                inside = False
                break
        if inside:
            return False
    return True


@nb.njit(cache=True, parallel=True)
def _pass_count(pos, neg, Z, W, n, cnt, lst):
    out = np.zeros(pos.shape[0], np.int64)
    for ip in nb.prange(pos.shape[0]):
        common = np.empty(W, np.uint64)
        p = pos[ip]
        c = 0
        for iq in range(neg.shape[0]):
            if _adjacent(p, neg[iq], Z, W, n, cnt, lst, common):
                c += 1
        out[ip] = c
    return out


@nb.njit(cache=True, parallel=True)
def _pass_write(pos, neg, offs, R, Z, vals, W, n, cnt, lst, ci, Rout, Zout, base):
    word = ci // 64
    bit = np.uint64(1) << np.uint64(ci % 64)
    bad = np.zeros(pos.shape[0], np.int64)
    for ip in nb.prange(pos.shape[0]):
        common = np.empty(W, np.uint64)
        p = pos[ip]
        k = base + offs[ip]
        for iq in range(neg.shape[0]):
            q = neg[iq]
            if _adjacent(p, q, Z, W, n, cnt, lst, common):
                vp = vals[p]
                vq = -vals[q]
                g = 0
                for j in range(n):
                    x = vp * R[q, j] + vq * R[p, j]
                    Rout[k, j] = x
                    g = _gcd(g, x)
                if g > 1:
                    for j in range(n):
                        Rout[k, j] //= g
                for j in range(n):
                    if Rout[k, j] > 134217728 or Rout[k, j] < -134217728:
                        bad[ip] = 1
                for w in range(W):
                    Zout[k, w] = common[w]
                Zout[k, word] |= bit
                k += 1
    return bad.sum()


@nb.njit(cache=True, parallel=True)
def _pass_nbhd(pos, isneg, Z, W, n, nr, write, offs, R, vals, ci, Rout, Zout, base, chunk):
    """'neighbourhood' variant of the combinatorial test.  For p in R+ let N(p) = {r != p : |Z(p) & Z(r)| >= n-2}.
    Any r with Z(r) containing C = Z(p) & Z(q) satisfies |Z(p) & Z(r)| >= |C| >= n-2, i.e. r in N(p); hence (p,q)
    is adjacent iff q in N(p) and no r in N(p), r != q, has Z(r) containing C.  Exact, same criterion."""
    npos = pos.shape[0]
    nch = (npos + chunk - 1) // chunk
    counts = np.zeros(npos, np.int64)
    bad = np.zeros(nch, np.int64)
    word = ci // 64
    bit = np.uint64(1) << np.uint64(ci % 64)
    for ch in nb.prange(nch):
        Np = np.empty(nr, np.int64)
        common = np.empty(W, np.uint64)
        for ip in range(ch * chunk, min(npos, (ch + 1) * chunk)):
            p = pos[ip]
            m = 0
            for r in range(nr):
                if r == p:
                    continue
                c = 0
                for w in range(W):
                    c += _pc(Z[p, w] & Z[r, w])
                if c >= n - 2:
                    Np[m] = r
                    m += 1
            k = 0
            if write:
                k = base + offs[ip]
            cnt = 0
            for a in range(m):
                q = Np[a]
                if not isneg[q]:
                    continue
                for w in range(W):
                    common[w] = Z[p, w] & Z[q, w]
                adj = True
                for b in range(m):
                    r = Np[b]
                    if r == q:
                        continue
                    inside = True
                    for w in range(W):
                        if (Z[r, w] & common[w]) != common[w]:
                            inside = False
                            break
                    if inside:
                        adj = False
                        break
                if adj:
                    if write:
                        vp = vals[p]
                        vq = -vals[q]
                        g = 0
                        for j in range(n):
                            x = vp * R[q, j] + vq * R[p, j]
                            Rout[k, j] = x
                            g = _gcd(g, x)
                        if g > 1:
                            for j in range(n):
                                Rout[k, j] //= g
                        for j in range(n):
                            if Rout[k, j] > 134217728 or Rout[k, j] < -134217728:
                                bad[ch] = 1
                        for w in range(W):
                            Zout[k, w] = common[w]
                        Zout[k, word] |= bit
                        k += 1
                    cnt += 1
            counts[ip] = cnt
    return counts, bad.sum()


@nb.njit(cache=True, parallel=True)
def _values(R, a, nr, n):
    v = np.empty(nr, np.int64)
    for k in nb.prange(nr):
        s = 0
        for j in range(n):
            s += R[k, j] * a[j]
        v[k] = s
    return v


@nb.njit(cache=True)
def _rank_mod(Mi, p):
    M = Mi.copy()
    rows, cols = M.shape
    for i in range(rows):
        for j in range(cols):
            M[i, j] %= p
    r = 0
    for c in range(cols):
        piv = -1
        for i in range(r, rows):
            if M[i, c] != 0:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            for j in range(cols):
                t = M[r, j]; M[r, j] = M[piv, j]; M[piv, j] = t
        # inverse of pivot (Fermat)
        a = M[r, c]
        e = p - 2
        inv = 1
        base = a
        while e > 0:
            if e & 1:
                inv = (inv * base) % p
            base = (base * base) % p
            e >>= 1
        for j in range(cols):
            M[r, j] = (M[r, j] * inv) % p
        for i in range(r + 1, rows):
            f = M[i, c]
            if f != 0:
                for j in range(cols):
                    M[i, j] = (M[i, j] - f * M[r, j]) % p
        r += 1
        if r == rows:
            break
    return r


def _initial_basis(A, rng, perm=None):
    m, n = A.shape
    order = rng.permutation(m) if perm is None else perm
    rows = []
    basis = []
    for i in order:
        trial = rows + [[int(x) for x in A[i]]]
        if flint.fmpz_mat(trial).rank() == len(trial):
            rows = trial
            basis.append(int(i))
            if len(basis) == n:
                break
    assert len(basis) == n, "constraint matrix does not have full column rank (cone not pointed)"
    return basis


def extreme_rays(A, seed=0, nthreads=2, verbose=False, label="", mode="nbhd", order="zeros", max_steps=None,
                 max_rays=None):
    """extreme rays of {h : A h >= 0}.  Returns (R, T): R (k x n) int64 primitive rays, T (k x W) uint64 tight
    bitsets over the rows of A.  All checks of the module docstring are run.  mode: 'nbhd' (neighbourhood scan)
    or 'lists' (rarest-constraint lists); both implement the same exact combinatorial adjacency criterion.
    order (insertion heuristic; correctness does not depend on it): 'zeros' = random initial basis, then min
    |R+||R-| with ties broken by most zeros; 'index' = initial basis and ties by row index; 'revindex' = the same
    with rows taken in reverse order; 'seedindex' = random row permutation, ties by that permutation."""
    nb.set_num_threads(nthreads)
    A = np.ascontiguousarray(np.asarray(A, dtype=np.int64))
    m, n = A.shape
    AMAX = int(np.abs(A).max())
    assert 2 * n * AMAX * RMAX * RMAX < 2 ** 63
    W = (m + 63) // 64
    rng = np.random.default_rng(seed)
    if order == "zeros":
        perm = None
    elif order == "index":
        perm = np.arange(m)
    elif order == "revindex":
        perm = np.arange(m)[::-1].copy()
    else:
        perm = rng.permutation(m)
    basis = _initial_basis(A, rng, perm)
    rank_of = np.empty(m, np.int64)
    rank_of[perm if perm is not None else np.arange(m)] = np.arange(m)
    B = flint.fmpz_mat([[int(x) for x in A[i]] for i in basis])
    det = B.det()
    Binv = B.inv()                                   # fmpq_mat
    sgn = 1 if det > 0 else -1
    R = np.zeros((n, n), np.int64)
    for j in range(n):
        col = [Binv[i, j] * det * sgn for i in range(n)]   # column j of |det| B^-1 : integer
        coli = [int(c) for c in col]
        assert all(flint.fmpq(c) == ci for c, ci in zip(col, coli))
        g = 0
        for c in coli:
            g = math.gcd(g, c)
        R[j] = [c // g for c in coli]
        assert np.abs(R[j]).max() <= RMAX
    Z = np.zeros((n, W), np.uint64)
    for j in range(n):
        for t, i in enumerate(basis):
            if t != j:
                Z[j, i // 64] |= np.uint64(1) << np.uint64(i % 64)
    # check initial rays exactly
    V = R @ A[basis].T
    for j in range(n):
        for t in range(n):
            assert (V[j, t] > 0) if t == j else (V[j, t] == 0)
    bset = set(basis)
    rest = [i for i in (perm if perm is not None else range(m)) if i not in bset]
    rest = [int(i) for i in rest]
    nr = n
    t0 = time.time()
    step = 0
    peak = nr
    while rest:
        step += 1
        if max_steps is not None and step > max_steps:
            return None, None, dict(peak=peak, steps=step - 1, aborted=True, nr=nr)
        Rf = R[:nr].astype(np.float64)
        Vr = Rf @ A[rest].T.astype(np.float64)          # exact: |entries| < 2^53
        npos = (Vr > 0).sum(axis=0).astype(np.int64)
        nneg = (Vr < 0).sum(axis=0).astype(np.int64)
        nzer = (Vr == 0).sum(axis=0).astype(np.int64)
        if order == "zeros":
            score = npos * nneg * (4 * nr + 1) - nzer       # min |R+||R-|, ties: most zeros
        else:
            score = npos * nneg                             # min |R+||R-|, ties: first in the row order
        k = int(np.argmin(score))
        ci = rest.pop(k)
        a = A[ci]
        vals = _values(R, a, nr, n)
        pos = np.nonzero(vals > 0)[0].astype(np.int64)
        neg = np.nonzero(vals < 0)[0].astype(np.int64)
        zer = np.nonzero(vals == 0)[0].astype(np.int64)
        if mode == "lists":
            cnt, lst = _build_lists(Z, nr, W)
            c1 = _pass_count(pos, neg, Z, W, n, cnt, lst)
        else:
            isneg = vals < 0
            dummyR = np.empty((1, n), np.int64)
            dummyZ = np.empty((1, W), np.uint64)
            c1, _ = _pass_nbhd(pos, isneg, Z, W, n, nr, False, np.zeros(len(pos), np.int64), R, vals, ci,
                               dummyR, dummyZ, 0, 16)
        offs = np.zeros(len(pos), np.int64)
        if len(pos):
            offs[1:] = np.cumsum(c1)[:-1]
        nnew = int(c1.sum())
        keep = np.concatenate([pos, zer])
        nk = len(keep)
        Rout = np.empty((nk + nnew, n), np.int64)
        Zout = np.empty((nk + nnew, W), np.uint64)
        Rout[:nk] = R[keep]
        Zout[:nk] = Z[keep]
        if len(zer):
            Zout[len(pos):nk, ci // 64] |= np.uint64(1) << np.uint64(ci % 64)
        if mode == "lists":
            bad = _pass_write(pos, neg, offs, R, Z, vals, W, n, cnt, lst, ci, Rout, Zout, nk)
        else:
            c2, bad = _pass_nbhd(pos, isneg, Z, W, n, nr, True, offs, R, vals, ci, Rout, Zout, nk, 16)
            assert np.array_equal(c1, c2)
        if bad:
            raise OverflowError("ray entry above the certified bound 2^27")
        R, Z, nr = Rout, Zout, nk + nnew
        peak = max(peak, nr)
        if max_rays is not None and nr > max_rays:
            return None, None, dict(peak=peak, steps=step, aborted=True, nr=nr)
        if verbose and (step % 10 == 0 or not rest):
            print(f"    [{label}] step {step}: |R+| {len(pos)} |R-| {len(neg)} |R0| {len(zer)} -> {nr} rays "
                  f"(max entry {int(np.abs(R).max())})  [{time.time() - t0:.0f}s]", flush=True)
    # ------------------------------------------------------------------ output checks
    assert int(np.abs(R).max()) <= RMAX
    V = R @ A.T
    assert (V >= 0).all(), "output ray violates a constraint"
    Tb = np.zeros((nr, W), np.uint64)
    zr, zc = np.nonzero(V == 0)
    np.bitwise_or.at(Tb, (zr, zc // 64), np.left_shift(np.uint64(1), (zc % 64).astype(np.uint64)))
    assert np.array_equal(Tb, Z), "tracked zero sets differ from the recomputed tight sets"
    nexact = 0
    for k in range(nr):
        T = np.nonzero(V[k] == 0)[0]
        rk = _rank_mod(A[T], PRIME)
        if rk != n - 1:
            nexact += 1
            rk = flint.fmpz_mat([[int(x) for x in A[i]] for i in T]).rank()
        assert rk == n - 1, "output ray is not extreme"
    assert len({R[k].tobytes() for k in range(nr)}) == nr, "duplicate rays"
    info = dict(peak=peak, steps=step, time=time.time() - t0, exact_rank_fallbacks=nexact,
                maxentry=int(np.abs(R).max()))
    return R, Z, info


def facets_of_points(P, seed=0, nthreads=2, verbose=False, label="", mode="nbhd", order="zeros", max_steps=None,
                     max_rays=None):
    """facets (h0, h) of conv(P), h0 + h.p >= 0 on P, P integer (k-dim full-dimensional point set)."""
    P = np.asarray(P, dtype=np.int64)
    A = np.hstack([np.ones((len(P), 1), np.int64), P])
    return extreme_rays(A, seed=seed, nthreads=nthreads, verbose=verbose, label=label, mode=mode, order=order,
                        max_steps=max_steps, max_rays=max_rays)
