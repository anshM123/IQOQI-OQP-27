"""
CLOSE_dd_safe.py -- the exact Motzkin double description of dd_numba.py (same compiled step dd_numba.dd_step, same
adaptive insertion order) with a CERTIFICATE THAT NO INTEGER OVERFLOW CAN HAVE OCCURRED.

dd_numba.dd_step computes, in int64,  vals[k] = sum_j R[k,j] a[j]  and  vp*R[q,j] - vm*R[p,j],  and only afterwards
compares the result with 2^40; a wrap-around of an intermediate product would not be detected.  Here, before every
step, the driver checks (with python integers) the bound
        2 * S * M^2  <  2^62,      M = max |entry| of the current rays,  S = max_i sum_j |C[i,j]|,
which implies |vals| <= S*M, |vp*R| <= S*M^2 < 2^61 and |vp*R - vm*R| < 2^62: every int64 operation of the step is
exact.  If the bound fails the computation is aborted (OverflowError) -- it never fails for the polytopes used here.
The final rays are also re-checked exactly (C r >= 0 with the reported tight sets) in python integers.
The maximal entry seen is reported (attribute LAST_MAX_ENTRY).
"""
import numpy as np
import dd_numba
from dd_exact import solve_simplicial_rays

LAST_MAX_ENTRY = 0
LIM = 2 ** 62


def _check(R, nr, S):
    global LAST_MAX_ENTRY
    M = int(np.abs(R[:nr]).max()) if nr else 0
    LAST_MAX_ENTRY = max(LAST_MAX_ENTRY, M)
    if 2 * S * M * M >= LIM:
        raise OverflowError(f"bound 2 S M^2 < 2^62 violated (S = {S}, M = {M})")


def cone_rays_safe(C, verbose=False, label="dd"):
    """extreme rays of the pointed cone {r : C r >= 0}; returns list of (ray tuple, tight frozenset)."""
    R, Z, m = cone_rays_safe_arrays(C, verbose=verbose, label=label)
    out = []
    for k in range(len(R)):
        r = tuple(int(x) for x in R[k])
        tight = frozenset(j for j in range(m) if (int(Z[k, j // 64]) >> (j % 64)) & 1)
        out.append((r, tight))
    return out


def cone_rays_safe_arrays(C, verbose=False, label="dd"):
    """same as cone_rays_safe, returning (R int64 array, Z uint64 tight-set bitsets, m) after the exact re-check
    (C r >= 0 for every ray, and the zero pattern of C r equals the bitset)."""
    global LAST_MAX_ENTRY
    LAST_MAX_ENTRY = 0
    C = np.array(C, dtype=np.int64)
    m, n = C.shape
    S = int(max(sum(abs(int(x)) for x in row) for row in C.tolist()))
    W = (m + 63) // 64
    basis, rows = [], []
    for i in range(m):
        trial = rows + [C[i].astype(float)]
        if np.linalg.matrix_rank(np.array(trial)) > len(rows):
            rows = trial
            basis.append(i)
            if len(basis) == n:
                break
    assert len(basis) == n, "cone not pointed / points not affinely spanning"
    R0 = solve_simplicial_rays([list(map(int, C[i])) for i in basis])
    assert max(abs(x) for r in R0 for x in r) < 2 ** 31
    R0 = np.array(R0, dtype=np.int64)
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
        _check(R, nr, S)
        V = R[:nr] @ C[rest].T
        score = (V > 0).sum(axis=0).astype(np.int64) * (V < 0).sum(axis=0).astype(np.int64)
        i = rest.pop(int(np.argmin(score)))
        capn = max(1024, 4 * nr)
        while True:
            Rout = np.zeros((capn, n), np.int64)
            Zout = np.zeros((capn, W), np.uint64)
            cnt = dd_numba.dd_step(R, Z, nr, C[i], i, n, W, Rout, Zout)
            if cnt == -2:
                raise OverflowError("int64 guard")
            if cnt == -1:
                capn *= 4
                continue
            break
        R, Z, nr = Rout[:cnt].copy(), Zout[:cnt].copy(), cnt
        if verbose and (step % 10 == 0 or step == nsteps - 1):
            print(f"    {label} step {step + 1}/{nsteps}: {nr} rays (max entry {LAST_MAX_ENTRY})", flush=True)
    _check(R, nr, S)
    R, Z = R[:nr], Z[:nr]
    # exact re-check of all final rays: |entries| <= M and S*M < 2^61 (checked above), so the int64 product is exact;
    # done in blocks to bound memory
    for s0 in range(0, nr, 20000):
        Vb = R[s0:s0 + 20000] @ C.T
        assert (Vb >= 0).all(), "ray re-check failed (C r >= 0)"
        bits = np.zeros((Vb.shape[0], Z.shape[1]), np.uint64)
        zr, zc = np.nonzero(Vb == 0)
        np.bitwise_or.at(bits, (zr, zc // 64), np.left_shift(np.uint64(1), (zc % 64).astype(np.uint64)))
        assert np.array_equal(bits, Z[s0:s0 + 20000]), "ray re-check failed (tight set)"
    return R, Z, m


def facets_of_points_safe(P, verbose=False):
    """facets of conv(P) (integer points spanning R^k affinely) as (r, tight) with r0 + r.p >= 0 on P (same
    interface as dd_numba.facets_of_points); the trivial ray (1, 0, ..., 0) is discarded."""
    C = [[1] + [int(x) for x in p] for p in P]
    rays = cone_rays_safe(C, verbose=verbose)
    return [(r, t) for (r, t) in rays if any(x != 0 for x in r[1:])]


def facets_of_points_safe_arrays(P, verbose=False):
    """array version: (R, Z, m) with the trivial ray removed."""
    C = [[1] + [int(x) for x in p] for p in P]
    R, Z, m = cone_rays_safe_arrays(C, verbose=verbose)
    keep = np.any(R[:, 1:] != 0, axis=1)
    return R[keep], Z[keep], m
