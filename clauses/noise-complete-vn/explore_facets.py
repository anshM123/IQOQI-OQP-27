"""
explore_facets.py -- randomized adjacency exploration of the facet classes of the (2,2,d) local polytope.

Seeds: ray shooting from u in random directions (Gaussian, towards generalised PR boxes, towards DKZ).
Exploration: for every class representative, sample random ridges (ray shooting inside the facet) and rotate
exactly to the adjacent facet; classify by a cheap G-invariant; repeat until a full pass finds nothing new.
Finally: exact facet check, stabiliser and orbit size of each class (exhaustive over G), total facet count.
Output: classes_d{d}.pkl (list of dicts with integer facet vectors) and a log on stdout.
NOTE: this is a search, not a completeness proof.
usage: python explore_facets.py d n_seed_rays ridges_per_class max_passes seed
"""
import sys
import time
import itertools
import pickle
import numpy as np
from facet_lib import Scenario, Facet, facet_in_direction, random_ridge_neighbour, Classifier
from core import dkz


def medium_invariant(F):
    """G-invariant signature: multiset over vertices lam of (s(lam), 1-change and 2-change neighbourhoods)."""
    sc = F.sc
    d = sc.d
    s = F.slack
    S = s.reshape(d, d, d, d)
    sigs = []
    for lam in itertools.product(range(d), repeat=4):
        one = []
        for i in range(4):
            vals = []
            for v in range(d):
                if v == lam[i]:
                    continue
                mu = list(lam); mu[i] = v
                vals.append(int(S[tuple(mu)]))
            one.append(tuple(sorted(vals)))
        two = []
        for i in range(4):
            for j in range(i + 1, 4):
                vals = []
                for v in range(d):
                    if v == lam[i]:
                        continue
                    for w in range(d):
                        if w == lam[j]:
                            continue
                        mu = list(lam); mu[i] = v; mu[j] = w
                        vals.append(int(S[tuple(mu)]))
                # pair type: same party {0,1},{2,3} vs cross party -- invariant under the 8 axis maps
                ptype = 0 if (i, j) in ((0, 1), (2, 3)) else 1
                two.append((ptype, tuple(sorted(vals))))
        sigs.append((int(S[lam]), tuple(sorted(one)), tuple(sorted(two))))
    sigs.sort()
    return (len(F.tight), hash(tuple(sigs)))


def pr_box_cg(sc, rng):
    d = sc.d
    k = rng.integers(2, d + 1)
    q = np.zeros((2, 2, d, d))
    injA = [rng.permutation(d)[:k] for _ in range(2)]
    injB = [rng.permutation(d)[:k] for _ in range(2)]
    for x in range(2):
        for y in range(2):
            for a in range(k):
                b = (a + x * y) % k
                q[x, y, injA[x][a], injB[y][b]] += 1.0 / k
    return sc.cg_of_full(q)


if __name__ == "__main__":
    d, nseed, nridge, maxpass, seed = (int(a) for a in sys.argv[1:6])
    rng = np.random.default_rng(seed)
    sc = Scenario(d)
    classes = {}      # medium invariant -> dict(rep=Facet, hits=int)
    order = []
    t0 = time.time()

    def add(F, src):
        key = medium_invariant(F)
        if key in classes:
            classes[key]['hits'] += 1
            return False
        classes[key] = dict(rep=F, hits=1, src=src)
        order.append(key)
        print(f"  NEW class {len(order) - 1:3d} (from {src}): tight {len(F.tight):4d}, rhs {F.f[0]}, "
              f"max|coef| {max(abs(x) for x in F.f[1:])}  [{time.time() - t0:.0f}s]", flush=True)
        return True

    # seeds
    targets = [sc.cg_of_full(dkz(d)) - sc.u]
    for i in range(nseed):
        if i % 2 == 0:
            targets.append(rng.normal(size=sc.dim))
        else:
            targets.append(pr_box_cg(sc, rng) - sc.u + 0.3 * rng.normal(size=sc.dim) / np.sqrt(sc.dim))
    for c in targets:
        F = facet_in_direction(sc, c)
        if F is not None:
            add(F, "ray")
    print(f"after seeding: {len(order)} classes", flush=True)
    # exploration passes
    for ps in range(maxpass):
        new = 0
        for key in list(order):
            F = classes[key]['rep']
            for r in range(nridge):
                out = random_ridge_neighbour(F, rng)
                if out is None:
                    continue
                if add(out[0], f"ridge of class {order.index(key)}"):
                    new += 1
        print(f"pass {ps}: {len(order)} classes, {new} new  [{time.time() - t0:.0f}s]", flush=True)
        with open(f"classes_d{d}.pkl", "wb") as fh:
            pickle.dump([dict(f=classes[k]['rep'].f, hits=classes[k]['hits'], src=classes[k]['src'])
                         for k in order], fh)
        if new == 0:
            break
    # stabilisers and orbit sizes
    cl = Classifier(sc)
    total = 0
    out = []
    keys_full = {}
    for i, key in enumerate(order):
        F = classes[key]['rep']
        assert F.is_facet()
        fk, stab = cl.key_and_stab(F)
        orb = sc.group_order() // stab
        total += orb
        if fk in keys_full:
            print(f"  WARNING: class {i} has the same full key as class {keys_full[fk]} (duplicate class)")
        keys_full[fk] = i
        out.append(dict(f=F.f, tight=len(F.tight), stab=stab, orbit=orb, fullkey=fk, hits=classes[key]['hits']))
        print(f"class {i:3d}: tight {len(F.tight):4d}, |Stab| {stab:7d}, orbit {orb:9d}, hits "
              f"{classes[key]['hits']}", flush=True)
    print(f"TOTAL: {len(order)} classes, {total} facets  [{time.time() - t0:.0f}s]", flush=True)
    with open(f"classes_d{d}.pkl", "wb") as fh:
        pickle.dump(out, fh)
