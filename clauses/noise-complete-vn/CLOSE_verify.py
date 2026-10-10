"""
CLOSE_verify.py -- exact verification that a facet-class list of the (2,2,d) local polytope L is COMPLETE, by the
visibility argument (CLOSE_NOTES.md, Theorem V).  No expansion of the positivity class is needed.

  (A) class data.  Every representative is an exact facet; one class is the positivity class and ALL 4d^2
      positivity inequalities are facets of L; every NON-positivity class is expanded (all ridges of the
      representative by exact double description, every neighbour identified with a listed class by an explicit
      relabelling).  d <= 3: the expansions are recomputed here from a single seed; d = 4: read from the saved
      exact expansions (adj_d4_small_final.pkl + adj_d4_full.pkl; logs/adjacency_d4_small.log,
      logs/adjacency_d4_big.log), plus double counting.
  (B) all vertices of NS(2,2,d) by exact double description of the polar, each vertex verified exactly and
      classified: deterministic, or a generalised PR box PR_k (explicit outcome relabelling g with W = g.PR_k).
  (B') independent check of (B): closure of the vertex types under NS-adjacency (every NS-edge at one
      representative of each type, by exact DD of the tangent cone; every neighbour classified).  The graph of a
      polytope is connected, so (B') alone also proves that every vertex of NS is deterministic or a PR_k.
  (C) for every k = 2..d, PR_k violates a listed facet (LP proposal, exact re-derivation, explicit relabelling onto
      a listed representative, exact violation).  By (B)/(B') and G-equivariance every non-local vertex of NS
      violates a listed facet.
  Theorem V then gives: the listed classes are ALL facets of L.

usage: python CLOSE_verify.py d [--skip-polar] [--skip-adm] [--orbits]
"""
import sys
import time
import pickle
import itertools
from collections import Counter
from fractions import Fraction
import numpy as np
from facet_lib import Scenario, Facet, facet_in_direction, Classifier
from dd_exact import affine_coords
import dd_fast
import CLOSE_dd_safe
from closure_check import rotate
from explore_facets import medium_invariant
from adjacency_d4 import find_g
from CLOSE_lib import (positivity_forms, ns_vertices_polar, ns_neighbours, full_tensor, pr_tensor, cg_of_tensor, values_to_tensor,
                       is_deterministic, pr_structure, pr_count, violated_known_facet, u_exact, form_values)


def log(*a):
    print(*a, flush=True)


def positivity_index(sc, F, keys):
    """index of the positivity form whose facet equals F (same tight set), or None."""
    T = set(int(i) for i in F.tight)
    for i, (x, y, a, b) in enumerate(keys):
        Ti = set(np.where(~((sc.lams[:, x] == a) & (sc.lams[:, 2 + y] == b)))[0].tolist())
        if Ti == T:
            return i
    return None


def expand(sc, F, reps, sigs, new_cb=None):
    """all ridges of F (exact DD), exact rotation, classification of every neighbour by an explicit relabelling;
    unmatched neighbours become new classes.  Returns the neighbour counts {class index: count}."""
    d = sc.d
    T = [tuple(int(x) for x in sc.V[k]) for k in F.tight]
    Tp, _ = affine_coords(T)
    ridges = dd_fast.facets_of_points(Tp, order="adaptive")
    counts = {}
    cache = {}
    for (_, tight) in ridges:
        ridge = [F.tight[k] for k in sorted(tight)]
        Fn = rotate(sc, F, ridge)
        kb = Fn.slack.tobytes()
        j = cache.get(kb)
        if j is None:
            sg = medium_invariant(Fn)
            S2 = Fn.slack.reshape(d, d, d, d)
            for jj, sj in enumerate(sigs):
                if sj == sg and find_g(reps[jj].slack.reshape(d, d, d, d), S2, sc) is not None:
                    j = jj
                    break
            if j is None:
                assert Fn.is_facet(), "rotation gave a non-facet"
                reps.append(Fn)
                sigs.append(sg)
                j = len(reps) - 1
                if new_cb:
                    new_cb(j, Fn)
            cache[kb] = j
        counts[j] = counts.get(j, 0) + 1
    return counts, len(ridges)


def classes_from_seed(sc, keys, seed_F):
    """adjacency decomposition expanding ONLY non-positivity classes (d <= 3)."""
    reps, sigs = [seed_F], [medium_invariant(seed_F)]
    adjacency = {}
    i = 0
    while i < len(reps):
        F = reps[i]
        if positivity_index(sc, F, keys) is None:
            t0 = time.time()
            cnt, nr = expand(sc, F, reps, sigs,
                             new_cb=lambda j, Fn: log(f"    new class {j}: tight {len(Fn.tight)}"))
            adjacency[i] = cnt
            log(f"  class {i}: tight {len(F.tight)}, {nr} ridges, neighbours {dict(sorted(cnt.items()))}"
                f"  [{time.time() - t0:.1f}s]")
        i += 1
    return reps, adjacency


def main():
    d = int(sys.argv[1])
    flags = set(sys.argv[2:])
    T0 = time.time()
    sc = Scenario(d)
    keys, c0, A = positivity_forms(sc)
    log(f"=== CLOSE_verify d = {d}: L(2,2,{d}) dim {sc.dim}, {len(sc.lams)} deterministic points, "
        f"{len(keys)} positivity forms (verified exactly on all deterministic points)")

    # ------------------------------------------------------------------ (A) class data
    log("(A) facet classes")
    if d <= 3:
        pr = pr_tensor(d, d)
        seed = facet_in_direction(sc, np.array([float(v) for v in cg_of_tensor(sc, pr)]) - sc.u)
        assert seed is not None and seed.is_facet()
        log(f"  seed: facet maximally violated by PR_{d} (tight {len(seed.tight)}); expanding non-positivity "
            f"classes only")
        reps, adjacency = classes_from_seed(sc, keys, seed)
    else:
        S = pickle.load(open("adj_d4_small_final.pkl", "rb"))
        Fb = pickle.load(open("adj_d4_full.pkl", "rb"))
        assert S["f"] == Fb["f"], "class lists differ"
        reps = [Facet(sc, f) for f in S["f"]]
        adjacency = dict(S["adjacency"])
        adjacency.update(Fb["adjacency"])
        log(f"  loaded {len(reps)} classes; expansions saved for {len(adjacency)} classes")
    ok = True
    pos = []
    for j, F in enumerate(reps):
        assert F.slack.min() >= 0
        isf = F.is_facet()
        p = positivity_index(sc, F, keys)
        if p is not None:
            pos.append(j)
        ok &= isf
        log(f"  class {j:2d}: exact facet {isf}, tight {len(F.tight):3d}, "
            f"{'POSITIVITY ' + str(keys[p]) if p is not None else 'non-positivity'}, expanded {j in adjacency}")
    assert len(pos) == 1, f"positivity classes: {pos}"
    jpos = pos[0]
    # every positivity inequality is a facet of L
    from facet_lib import affine_rank
    allpos = True
    for i, (x, y, a, b) in enumerate(keys):
        Ti = np.where(~((sc.lams[:, x] == a) & (sc.lams[:, 2 + y] == b)))[0]
        allpos &= (affine_rank(sc.V[Ti].tolist()) == sc.dim - 1)
    log(f"  all {len(keys)} positivity inequalities are facets of L (exact affine rank {sc.dim - 1}): {allpos}")
    nonpos = [j for j in range(len(reps)) if j != jpos]
    expanded_all = all(j in adjacency for j in nonpos)
    inside = all(k < len(reps) for j in nonpos for k in adjacency[j])
    log(f"  every non-positivity class expanded: {expanded_all}; every neighbour in the list: {inside}")
    ok &= allpos and expanded_all and inside
    if "--orbits" in flags or d <= 3:
        cl = Classifier(sc)
        orbits = []
        for F in reps:
            _, stab = cl.key_and_stab(F)
            orbits.append(sc.group_order() // stab)
    else:
        orbits = pickle.load(open("adj_d4_small_final.pkl", "rb"))["orbits"]
    bad = sum(1 for i, c in adjacency.items() for k, a in c.items()
              if k in adjacency and orbits[i] * a != orbits[k] * adjacency[k].get(i, 0))
    log(f"  orbits {orbits}; total facets {sum(orbits)}; positivity orbit {orbits[jpos]} (= 4d^2: "
        f"{orbits[jpos] == 4 * d * d}); double-counting violations {bad}")
    ok &= (bad == 0) and orbits[jpos] == 4 * d * d
    sigs = [medium_invariant(F) for F in reps]

    # ------------------------------------------------------------------ (B) NS vertices
    if "--skip-polar" not in flags:
        log("(B) vertices of NS(2,2,d): exact DD of the polar conv{q_i}, q_i = -d^2 A_i")
        t0 = time.time()
        num, den = ns_vertices_polar(sc, c0, A, verbose=(d >= 4))
        log(f"  DD done: {len(num)} vertices, all verified exactly; max |ray entry| {CLOSE_dd_safe.LAST_MAX_ENTRY} "
            f"(no-overflow bound certified)  [{time.time() - t0:.0f}s]")
        det = np.all((num == 0) | (num == den[:, None]), axis=1)
        types = Counter()
        types["deterministic"] = int(det.sum())
        other = 0
        for v in np.nonzero(~det)[0]:
            W = values_to_tensor(keys, d, num[v], den[v])
            s = pr_structure(W, d)
            if s is None:
                other += 1
            else:
                types[f"PR_{s[0]}"] += 1
        log(f"  {len(num)} vertices (each verified exactly): {dict(types)}; unrecognised: {other}  "
            f"[{time.time() - t0:.0f}s]")
        expect = {"deterministic": d ** 4}
        expect.update({f"PR_{k}": pr_count(d, k) for k in range(2, d + 1)})
        log(f"  predicted (d^4 and C(d,k)^4 (k!)^3 (k-1)!): {expect}; match: {dict(types) == expect}")
        ok &= (other == 0) and dict(types) == expect

    # ------------------------------------------------------------------ (B') NS adjacency closure
    if "--skip-adm" not in flags:
        log("(B') closure of the vertex types under NS-adjacency (tangent-cone DD at one representative per type)")
        u = u_exact(sc)
        reps_ns = [("deterministic", tuple(Fraction(v) for v in sc.V[0]))]
        for k in range(2, d + 1):
            reps_ns.append((f"PR_{k}", tuple(cg_of_tensor(sc, pr_tensor(d, k)))))
        closed = True
        for name, x0 in reps_ns:
            t0 = time.time()
            nb = ns_neighbours(c0, A, x0, verbose=False)
            tc = Counter()
            for r, x1 in nb:
                W = full_tensor(sc, keys, c0, A, x1)
                if is_deterministic(W, d):
                    tc["deterministic"] += 1
                else:
                    s = pr_structure(W, d)
                    tc[f"PR_{s[0]}" if s else "UNRECOGNISED"] += 1
            closed &= ("UNRECOGNISED" not in tc)
            log(f"  {name}: {len(nb)} NS-edges, neighbour types {dict(tc)}; max |ray entry| "
                f"{CLOSE_dd_safe.LAST_MAX_ENTRY}  [{time.time() - t0:.0f}s]")
        log(f"  vertex types closed under NS-adjacency: {closed}")
        ok &= closed

    # ------------------------------------------------------------------ (C) violations
    log("(C) every non-local vertex type violates a listed facet")
    for k in range(2, d + 1):
        cgx = cg_of_tensor(sc, pr_tensor(d, k))
        res = violated_known_facet(sc, cgx, reps, sigs, find_g, medium_invariant)
        if res is None:
            log(f"  PR_{k}: no violated facet found (LP failure)")
            ok = False
            continue
        j, F, viol, g = res
        if j < 0:
            log(f"  PR_{k}: violates a facet NOT in the list: tight {len(F.tight)}, f = {F.f}")
            ok = False
        else:
            log(f"  PR_{k}: violates a facet of class {j} (tight {len(F.tight)}) by h.x - h0 = {viol} (exact; "
                f"explicit relabelling onto the representative found)")
    log(("THEOREM V HYPOTHESES VERIFIED: the list of " + str(len(reps)) + " classes (" + str(sum(orbits)) +
         " facets) is COMPLETE") if ok else "VERIFICATION FAILED")
    log(f"[total {time.time() - T0:.0f}s]")


if __name__ == "__main__":
    main()
