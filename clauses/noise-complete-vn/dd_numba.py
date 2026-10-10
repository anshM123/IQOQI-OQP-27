"""
dd_numba.py -- the exact Motzkin double description of dd_fast.py compiled with numba (int64 rays, uint64 tight-set
bitsets, combinatorial adjacency test with a popcount filter), for the large facets of L(2,2,4).
Same interface: facets_of_points(P, verbose=False, order="adaptive").  All arithmetic is exact integer arithmetic
(int64 with an overflow guard: every new ray is checked against a bound 2^40 before normalisation, abort otherwise).
"""
import numpy as np
import numba as nb
from dd_exact import solve_simplicial_rays

M1 = np.uint64(0x5555555555555555)
M2 = np.uint64(0x3333333333333333)
M4 = np.uint64(0x0F0F0F0F0F0F0F0F)
H01 = np.uint64(0x0101010101010101)


@nb.njit(cache=True)
def popc(x):
    x = x - ((x >> np.uint64(1)) & M1)
    x = (x & M2) + ((x >> np.uint64(2)) & M2)
    x = (x + (x >> np.uint64(4))) & M4
    return (x * H01) >> np.uint64(56)


@nb.njit(cache=True)
def gcd(a, b):
    a = abs(a); b = abs(b)
    while b:
        a, b = b, a % b
    return a


@nb.njit(cache=True)
def dd_step(R, Z, nr, a, i, n, W, Rout, Zout):
    """add constraint a (index i).  R: (nr, n) int64, Z: (nr, W) uint64.  Writes new rays to Rout/Zout,
    returns count (or -1 on capacity overflow, -2 on int overflow).  Adjacency: combinatorial test using an
    inverted index (rays tight on the rarest constraint of the common tight set)."""
    vals = np.zeros(nr, np.int64)
    for k in range(nr):
        s = 0
        for j in range(n):
            s += R[k, j] * a[j]
        vals[k] = s
    pcs = np.zeros(nr, np.int64)
    for k in range(nr):
        c = 0
        for w in range(W):
            c += popc(Z[k, w])
        pcs[k] = c
    # inverted index over constraints 0..64W-1
    M = 64 * W
    cntc = np.zeros(M + 1, np.int64)
    for k in range(nr):
        for w in range(W):
            x = Z[k, w]
            b = 0
            while x != np.uint64(0):
                if x & np.uint64(1):
                    cntc[64 * w + b + 1] += 1
                x = x >> np.uint64(1)
                b += 1
    for c in range(M):
        cntc[c + 1] += cntc[c]
    fill = cntc[:M].copy()
    idx = np.zeros(cntc[M], np.int64)
    for k in range(nr):
        for w in range(W):
            x = Z[k, w]
            b = 0
            while x != np.uint64(0):
                if x & np.uint64(1):
                    c = 64 * w + b
                    idx[fill[c]] = k
                    fill[c] += 1
                x = x >> np.uint64(1)
                b += 1
    cap = Rout.shape[0]
    cnt = 0
    word = i // 64
    bit = np.uint64(1) << np.uint64(i % 64)
    for k in range(nr):
        if vals[k] >= 0:
            if cnt >= cap:
                return -1
            for j in range(n):
                Rout[cnt, j] = R[k, j]
            for w in range(W):
                Zout[cnt, w] = Z[k, w]
            if vals[k] == 0:
                Zout[cnt, word] |= bit
            cnt += 1
    common = np.zeros(W, np.uint64)
    for p in range(nr):
        if vals[p] <= 0:
            continue
        for q in range(nr):
            if vals[q] >= 0:
                continue
            pc = 0
            for w in range(W):
                common[w] = Z[p, w] & Z[q, w]
                pc += popc(common[w])
            if pc < n - 2:
                continue
            # rarest constraint in common
            best_c = -1
            best_n = nr + 1
            for w in range(W):
                x = common[w]
                b = 0
                while x != np.uint64(0):
                    if x & np.uint64(1):
                        c = 64 * w + b
                        ncnt = cntc[c + 1] - cntc[c]
                        if ncnt < best_n:
                            best_n = ncnt
                            best_c = c
                    x = x >> np.uint64(1)
                    b += 1
            adj = True
            for t in range(cntc[best_c], cntc[best_c + 1]):
                r = idx[t]
                if r == p or r == q or pcs[r] < pc:
                    continue
                sub = True
                for w in range(W):
                    if (Z[r, w] & common[w]) != common[w]:
                        sub = False
                        break
                if sub:
                    adj = False
                    break
            if not adj:
                continue
            if cnt >= cap:
                return -1
            vp = vals[p]
            vm = vals[q]
            g = 0
            for j in range(n):
                x2 = vp * R[q, j] - vm * R[p, j]
                if x2 > (1 << 40) or x2 < -(1 << 40):
                    return -2
                Rout[cnt, j] = x2
                g = gcd(g, x2)
            if g > 1:
                for j in range(n):
                    Rout[cnt, j] //= g
            for w in range(W):
                Zout[cnt, w] = common[w]
            Zout[cnt, word] |= bit
            cnt += 1
    return cnt


def facets_of_points(P, verbose=False, order="adaptive", cap=4_000_000):
    C = np.array([[1] + list(p) for p in P], dtype=np.int64)
    m, n = C.shape
    W = (m + 63) // 64
    basis, rows = [], []
    for i in range(m):
        trial = rows + [C[i].astype(float)]
        if np.linalg.matrix_rank(np.array(trial)) > len(rows):
            rows = trial
            basis.append(i)
            if len(basis) == n:
                break
    R0 = np.array(solve_simplicial_rays([list(map(int, C[i])) for i in basis]), dtype=np.int64)
    nr = len(R0)
    R = R0.copy()
    Z = np.zeros((nr, W), np.uint64)
    for k in range(nr):
        for i in basis:
            if int(C[i] @ R0[k]) == 0:
                Z[k, i // 64] |= np.uint64(1) << np.uint64(i % 64)
    rest = [i for i in range(m) if i not in set(basis)]
    nsteps = len(rest)
    for step in range(nsteps):
        if order == "adaptive":
            V = R[:nr] @ C[rest].T
            score = (V > 0).sum(axis=0).astype(np.int64) * (V < 0).sum(axis=0).astype(np.int64)
            i = rest.pop(int(np.argmin(score)))
        else:
            i = rest.pop(0)
        capn = max(1024, 4 * nr)
        while True:
            Rout = np.zeros((capn, n), np.int64)
            Zout = np.zeros((capn, W), np.uint64)
            cnt = dd_step(R, Z, nr, C[i], i, n, W, Rout, Zout)
            if cnt == -2:
                raise OverflowError("int64 guard")
            if cnt == -1:
                capn *= 4
                continue
            break
        R, Z, nr = Rout[:cnt].copy(), Zout[:cnt].copy(), cnt
        if verbose and (step % 10 == 0 or step == nsteps - 1):
            print(f"    dd step {step + 1}/{nsteps}: {nr} rays", flush=True)
    out = []
    for k in range(nr):
        r = tuple(int(x) for x in R[k])
        if all(x == 0 for x in r[1:]):
            continue
        tight = frozenset(j for j in range(m) if (int(Z[k, j // 64]) >> (j % 64)) & 1)
        out.append((r, tight))
    return out
