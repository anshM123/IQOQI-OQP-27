"""
adjacency_d4.py -- EXACT adjacency decomposition of the (2,2,d) local polytope (intended for d = 4).

Queue of facet-class representatives (seeded from a class pickle).  For each representative F:
  1. all ridges of F by exact double description (dd_fast.py) in the affine hull of F;
  2. exact rotation of every ridge to the neighbouring facet F' (closure_check.rotate);
  3. exact classification of F': candidate class by the G-invariant signature, then an explicit relabelling g
     (axis permutation + four outcome permutations) with g.slack(F') = slack(rep) is SEARCHED and VERIFIED exactly;
     if no candidate verifies, F' becomes a new class representative (appended to the queue).
Termination with an empty queue proves that the union of the listed orbits is closed under ridge adjacency, hence
(the dual graph of a polytope being connected) equals the set of ALL facets.  Finally: exact stabilisers, orbit
sizes, and the total number of facets.
usage: python adjacency_d4.py d seed_classes.pkl out.pkl [vmax]
   vmax: only representatives with <= vmax tight vertices are expanded (others are listed but their ridges are
   not enumerated; the run then proves closure only relative to the unexpanded classes).
"""
import sys
import time
import pickle
import itertools
import numpy as np
from facet_lib import Scenario, Facet, Classifier
from dd_exact import affine_coords
import dd_fast
from closure_check import rotate
from explore_facets import medium_invariant


def slice_sigs(T, axis):
    d = T.shape[0]
    return [tuple(np.sort(np.take(T, v, axis=axis).reshape(-1))) for v in range(d)]


def find_g(S1, S2, sc):
    """explicit relabelling mapping slack tensor S1 to S2:  transpose(S1, ax)[p0][:,p1][:,:,p2][:,:,:,p3] == S2.
    Returns (ax, p0, p1, p2, p3) or None.  Exhaustive over the 8 axis maps; outcome permutations restricted to
    slice-signature-compatible bijections, with partial-consistency pruning."""
    d = S1.shape[0]
    for ax in sc.axis_perms():
        T = np.transpose(S1, ax)
        cand = []
        ok = True
        for i in range(4):
            sT = slice_sigs(T, i)
            sS = slice_sigs(S2, i)
            c = [[w for w in range(d) if sT[w] == sS[v]] for v in range(d)]
            if any(len(x) == 0 for x in c):
                ok = False
                break
            cand.append(c)
        if not ok:
            continue

        def bijections(c):
            for perm in itertools.product(*c):
                if len(set(perm)) == d:
                    yield list(perm)

        for p0 in bijections(cand[0]):
            T0 = T[p0]
            # prune: 3-dim sub-tensor multisets along axis 0 already matched by signatures; check pairs (a0,a1)
            for p1 in bijections(cand[1]):
                T1 = T0[:, p1]
                # 2-index slices (a0, a1) must match as multisets
                good = True
                for a0 in range(d):
                    for a1 in range(d):
                        if not np.array_equal(np.sort(T1[a0, a1].reshape(-1)), np.sort(S2[a0, a1].reshape(-1))):
                            good = False
                            break
                    if not good:
                        break
                if not good:
                    continue
                for p2 in bijections(cand[2]):
                    T2 = T1[:, :, p2]
                    good2 = True
                    for a0 in range(d):
                        for a1 in range(d):
                            for b0 in range(d):
                                if not np.array_equal(np.sort(T2[a0, a1, b0]), np.sort(S2[a0, a1, b0])):
                                    good2 = False
                                    break
                            if not good2:
                                break
                        if not good2:
                            break
                    if not good2:
                        continue
                    for p3 in bijections(cand[3]):
                        if np.array_equal(T2[:, :, :, p3], S2):
                            return (ax, p0, p1, p2, p3)
    return None


if __name__ == "__main__":
    d = int(sys.argv[1])
    seed_path, out_path = sys.argv[2], sys.argv[3]
    vmax = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    sc = Scenario(d)
    reps, sigs = [], []
    for c in pickle.load(open(seed_path, "rb")):
        F = Facet(sc, c["f"])
        assert F.slack.min() >= 0 and F.is_facet()
        reps.append(F)
        sigs.append(medium_invariant(F))
    print(f"d={d}: {len(reps)} seed classes", flush=True)
    t0 = time.time()
    verified_cache = {}          # slack bytes -> class index
    i = 0
    adjacency = {}
    skipped = []
    while i < len(reps):
        F = reps[i]
        if len(F.tight) > vmax:
            skipped.append(i)
            print(f"class {i}: {len(F.tight)} vertices > vmax -- NOT expanded", flush=True)
            i += 1
            continue
        T = [tuple(int(x) for x in sc.V[k]) for k in F.tight]
        Tp, cols = affine_coords(T)
        ridges = dd_fast.facets_of_points(Tp, order="adaptive")
        counts = {}
        for (r, tight) in ridges:
            ridge = [F.tight[k] for k in sorted(tight)]
            Fn = rotate(sc, F, ridge)
            if not Fn.is_facet():
                raise RuntimeError(f"class {i}: rotation gave a non-facet")
            kb = Fn.slack.tobytes()
            j = verified_cache.get(kb)
            if j is None:
                sg = medium_invariant(Fn)
                S2 = Fn.slack.reshape(d, d, d, d)
                j = None
                for jj, sj in enumerate(sigs):
                    if sj == sg:
                        g = find_g(reps[jj].slack.reshape(d, d, d, d), S2, sc)
                        if g is not None:
                            j = jj
                            break
                if j is None:
                    reps.append(Fn)
                    sigs.append(sg)
                    j = len(reps) - 1
                    print(f"  NEW class {j} (neighbour of {i}): tight {len(Fn.tight)}, f = {Fn.f}", flush=True)
                verified_cache[kb] = j
            counts[j] = counts.get(j, 0) + 1
        adjacency[i] = counts
        print(f"class {i}: {len(F.tight)} vertices, {len(ridges)} ridges, neighbours {dict(sorted(counts.items()))}"
              f"  [{time.time() - t0:.0f}s]", flush=True)
        pickle.dump(dict(f=[R.f for R in reps], adjacency=adjacency), open(out_path, "wb"))
        i += 1
    if skipped:
        print(f"CLOSED RELATIVE TO the unexpanded classes {skipped}: {len(reps)} classes  [{time.time() - t0:.0f}s]",
              flush=True)
    else:
        print(f"ADJACENCY-CLOSED: {len(reps)} classes  [{time.time() - t0:.0f}s]", flush=True)
    cl = Classifier(sc)
    total = 0
    orbits = []
    for j, F in enumerate(reps):
        _, stab = cl.key_and_stab(F)
        orb = sc.group_order() // stab
        orbits.append(orb)
        total += orb
        print(f"class {j}: tight {len(F.tight)}, |Stab| {stab}, orbit {orb}", flush=True)
    # double-counting consistency of the adjacency counts: orbit_i * a_ij == orbit_j * a_ji
    bad = 0
    for i2, cnt in adjacency.items():
        for j2, a in cnt.items():
            if j2 not in adjacency:
                continue                      # unexpanded class: no reverse count available
            b = adjacency[j2].get(i2, 0)
            if orbits[i2] * a != orbits[j2] * b:
                bad += 1
    print(f"TOTAL FACETS: {total} in {len(reps)} classes; adjacency double-counting violations: {bad}", flush=True)
    pickle.dump(dict(f=[R.f for R in reps], adjacency=adjacency, orbits=orbits, total=total), open(out_path, "wb"))
