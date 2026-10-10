"""
kd_facets.py -- facets of the cyclic (covariant) local polytope K_d, exact (IND_dd.py double description).

Covariant behaviours of (2,2,d) are determined by the four link-difference laws.  In cycle coordinates
n1 = b0 - a0, n3 = a1 - b0, n4 = b1 - a1, n2 = a0 - b1 (mod d) every deterministic point has n1 + n2 + n3 + n4 = 0, and
K_d = conv{ (e_{n1}, e_{n2}, e_{n3}, e_{n4}) : n1 + n2 + n3 + n4 = 0 mod d }  (twirl of L(2,2,d)).
A covariant behaviour p is local iff its link laws lie in K_d, so for covariant p the white-noise critical
visibility is decided by the facets of K_d.  Physical symmetries: translations (sum zero), units u in Z_d^*,
dihedral D_4 on the cycle order (n1, n3, n4, n2) (orientation reversal combined with negation).
Output: facet inequalities sum_i sum_n c_i(n) Q_i(n) <= c0 (c_i(0) normalised to 0), grouped into classes.
"""
import os
import sys
import itertools
import math
import json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from IND_dd import facets_of_points


def kd_points(d):
    pts = []
    for n1, n2, n3 in itertools.product(range(d), repeat=3):
        n4 = (-n1 - n2 - n3) % d
        v = np.zeros(4 * (d - 1), np.int64)
        for i, n in enumerate((n1, n2, n3, n4)):
            if n > 0:
                v[i * (d - 1) + n - 1] = 1
        pts.append(v)
    return np.array(pts)


def to_table(f, d):
    """facet ray (h0, h) with h0 + h.v >= 0  ->  table c[i][n] with sum_i c_i(n_i) <= c0 on K_d vertices,
    i.e. c = -h (n >= 1), c_i(0) = 0, c0 = h0."""
    h0 = int(f[0]); h = np.asarray(f[1:], dtype=np.int64)
    c = np.zeros((4, d), np.int64)
    for i in range(4):
        c[i, 1:] = -h[i * (d - 1):(i + 1) * (d - 1)]
    return c, h0


def slack_tensor(c, c0, d):
    s = {}
    for n1, n2, n3 in itertools.product(range(d), repeat=3):
        n4 = (-n1 - n2 - n3) % d
        s[(n1, n2, n3)] = c0 - (c[0, n1] + c[1, n2] + c[2, n3] + c[3, n4])
    return s


def canon(c, c0, d, group="phys"):
    """canonical form of the facet under the symmetry group (translations, units, positions)."""
    units = [u for u in range(1, d) if math.gcd(u, d) == 1]
    cyc = [0, 2, 3, 1]                           # cycle order positions: n1, n3, n4, n2 -> indices 0, 2, 3, 1
    perms = []
    if group == "phys":
        for r in range(4):
            for refl in (False, True):
                order = [cyc[(r + k) % 4] for k in range(4)]
                if refl:
                    order = order[::-1]
                # position j of the new facet takes the old position order[j] in cycle order
                p = [None] * 4
                for j in range(4):
                    p[cyc[j]] = order[j]
                perms.append(tuple(p))
    else:
        perms = list(itertools.permutations(range(4)))
    best = None
    for p in set(perms):
        for u in units:
            for t in itertools.product(range(d), repeat=3):
                t4 = (-sum(t)) % d
                tt = t + (t4,)
                # new c'_j(n) = c_{p[j]}(u n + tt_j)  (n_j -> u n_j + t_j keeps the sum zero)
                cc = np.zeros((4, d), np.int64)
                for j in range(4):
                    for n in range(d):
                        cc[j, n] = c[p[j], (u * n + tt[j]) % d]
                # normalise: subtract c_j(0) and adjust c0
                off = cc[:, 0].copy()
                cc = cc - off[:, None]
                key = (int(c0 - off.sum()),) + tuple(cc.flatten().tolist())
                if best is None or key < best:
                    best = key
    return best


def normalise(c, c0):
    off = c[:, 0].copy()
    c = c - off[:, None]
    c0 = c0 - int(off.sum())
    g = 0
    for v in np.concatenate([c.flatten(), [c0]]):
        g = math.gcd(g, int(abs(v)))
    if g > 1:
        c = c // g; c0 = c0 // g
    return c, int(c0)


def group_elements(d):
    units = [u for u in range(1, d) if math.gcd(u, d) == 1]
    cyc = [0, 2, 3, 1]
    perms = set()
    for r in range(4):
        for refl in (False, True):
            order = [cyc[(r + k) % 4] for k in range(4)]
            if refl:
                order = order[::-1]
            p = [None] * 4
            for j in range(4):
                p[cyc[j]] = order[j]
            perms.add(tuple(p))
    trans = [t + ((-sum(t)) % d,) for t in itertools.product(range(d), repeat=3)]
    return [(p, u, tt) for p in sorted(perms) for u in units for tt in trans]


def act(c, c0, g, d):
    p, u, tt = g
    n = np.arange(d)
    cc = np.stack([c[p[j], (u * n + tt[j]) % d] for j in range(4)])
    return normalise(cc, c0)


if __name__ == "__main__":
    import time
    d = int(sys.argv[1])
    P = kd_points(d)
    A = np.hstack([np.ones((len(P), 1), np.int64), P])
    print(f"K_{d}: {len(P)} vertices in R^{P.shape[1]}, affine rank", np.linalg.matrix_rank(A.astype(float)) - 1,
          flush=True)
    t0 = time.time()
    order = sys.argv[2] if len(sys.argv) > 2 else "zeros"
    tag = "" if order == "zeros" else "_" + order
    F, _Z, info = facets_of_points(P, nthreads=2, verbose=True, label=f"K{d}{tag}", order=order)
    print("facets:", len(F), " DD info:", info, f"[{time.time()-t0:.0f}s]", flush=True)
    np.save(f"kd_facets_d{d}{tag}_raw.npy", F)
    pool = {}
    for f in F:
        c, c0 = to_table(f, d)
        c, c0 = normalise(c, c0)
        pool[(c0,) + tuple(c.flatten().tolist())] = (c, c0)
    G = group_elements(d)
    print("group size", len(G), flush=True)
    out = []
    while pool:
        key, (c, c0) = next(iter(pool.items()))
        orbit = set()
        for g in G:
            cc, cc0 = act(c, c0, g, d)
            k = (cc0,) + tuple(cc.flatten().tolist())
            orbit.add(k)
        missing = [k for k in orbit if k not in pool]
        assert not missing, "orbit element is not a listed facet"
        for k in orbit:
            del pool[k]
        rep = min(orbit)
        cr = np.array(rep[1:]).reshape(4, d)
        s = slack_tensor(cr, rep[0], d)
        tight = sum(1 for v in s.values() if v == 0)
        out.append({"size": len(orbit), "c0": rep[0], "c": cr.tolist(), "tight": tight})
    out.sort(key=lambda o: -o["size"])
    print("physical classes:", len(out), " total", sum(o["size"] for o in out))
    for o in out:
        print(f"  class size {o['size']:6d}  tight {o['tight']:4d}  c0={o['c0']}  c={o['c']}")
    json.dump(out, open(f"kd_facets_d{d}{tag}.json", "w"))
