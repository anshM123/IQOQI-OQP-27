"""
dd_fast.py -- exact incremental double description (Motzkin) with
  * rays stored as int64 numpy rows (primitive integer vectors; overflow guard: |entries| < 2^50, else abort),
  * tight sets as python-int bitsets over constraints,
  * the combinatorial adjacency test via per-constraint ray bitsets:
       r+, r- adjacent  <=>  |Z+ & Z-| >= n-2  and  the only rays tight on all of Z+ & Z- are r+ and r-.
All decisions are exact integer computations (no floating point).
facets_of_points(P) has the same interface as dd_exact.facets_of_points.
"""
import math
import numpy as np
from dd_exact import solve_simplicial_rays

LIM = 2 ** 50


def popcount(x):
    return bin(x).count("1")


def dd_cone(constraints, order=None, verbose=False):
    C = np.array(constraints, dtype=np.int64)
    m, n = C.shape
    idx = list(range(m)) if (order is None or order == "adaptive") else list(order)
    # initial basis: first n linearly independent constraints in the given order (exact rank via fractions in
    # solve_simplicial_rays; candidate selection by float rank)
    basis = []
    rows = []
    for i in idx:
        trial = rows + [C[i].astype(float)]
        if np.linalg.matrix_rank(np.array(trial)) > len(rows):
            rows = trial
            basis.append(i)
            if len(basis) == n:
                break
    assert len(basis) == n
    R = np.array(solve_simplicial_rays([list(map(int, C[i])) for i in basis]), dtype=np.int64)
    # tight sets
    Z = []
    for r in R:
        t = 0
        for i in basis:
            if int(C[i] @ r) == 0:
                t |= 1 << i
        Z.append(t)
    processed = set(basis)
    rest = [i for i in idx if i not in processed]
    adaptive = (order == "adaptive")
    nsteps = len(rest)
    for step in range(nsteps):
        if adaptive:
            # choose the remaining constraint minimising |plus| * |minus| (fewest candidate pairs)
            Vall = R @ C[rest].T
            score = (Vall > 0).sum(axis=0).astype(np.int64) * (Vall < 0).sum(axis=0).astype(np.int64)
            pick = int(np.argmin(score))
            i = rest.pop(pick)
        else:
            i = rest[step]
        a = C[i]
        vals = R @ a
        plus = np.where(vals > 0)[0]
        minus = np.where(vals < 0)[0]
        zero = np.where(vals == 0)[0]
        # per-constraint ray bitsets over current rays (only constraints processed so far matter)
        nr = len(R)
        tight_at = {}
        for c in processed:
            col = (R @ C[c]) == 0
            bits = 0
            for k in np.where(col)[0]:
                bits |= 1 << int(k)
            tight_at[c] = bits
        newR = [R[k] for k in plus] + [R[k] for k in zero]
        newZ = [Z[k] for k in plus] + [Z[k] | (1 << i) for k in zero]
        for kp in plus:
            zp = Z[kp]
            for km in minus:
                common = zp & Z[km]
                if popcount(common) < n - 2:
                    continue
                # rays tight on all constraints of `common`
                acc = (1 << nr) - 1
                c = common
                while c:
                    low = c & -c
                    j = low.bit_length() - 1
                    acc &= tight_at[j]
                    c ^= low
                    if acc == ((1 << int(kp)) | (1 << int(km))):
                        break
                if acc != ((1 << int(kp)) | (1 << int(km))):
                    continue
                vp, vm = int(vals[kp]), int(vals[km])
                r = vp * R[km].astype(object) - vm * R[kp].astype(object)
                g = 0
                for x in r:
                    g = math.gcd(g, int(x))
                r = np.array([int(x) // g for x in r], dtype=object)
                if max(abs(int(x)) for x in r) >= LIM:
                    raise OverflowError("ray entries too large for int64 path")
                newR.append(r.astype(np.int64))
                newZ.append(common | (1 << i))
        R = np.array(newR, dtype=np.int64) if newR else np.zeros((0, n), dtype=np.int64)
        Z = newZ
        processed.add(i)
        if verbose and (step % 10 == 0 or step == nsteps - 1):
            print(f"    dd step {step + 1}/{nsteps}: {len(R)} rays", flush=True)
    return [(tuple(int(x) for x in r), frozenset(j for j in range(m) if (z >> j) & 1)) for r, z in zip(R, Z)]


def facets_of_points(P, verbose=False, order=None):
    cons = [tuple([1] + list(p)) for p in P]
    rays = dd_cone(cons, order=order, verbose=verbose)
    return [(r, t) for (r, t) in rays if any(x != 0 for x in r[1:])]
