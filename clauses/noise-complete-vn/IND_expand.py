"""
IND_expand.py -- independent check (2026-10-09) of hypothesis (i) of Theorem V for L(2,2,4): for every requested
facet class j, ALL ridges of the class representative are enumerated by the independent exact double description
of IND_dd.py, every ridge is rotated exactly to the neighbouring facet of L, and the neighbour is identified with
one of the 34 listed representatives by an EXPLICIT relabelling g in G (IND_core.Matcher, verified entry by entry).
A neighbour that matches no representative is reported as NEW (it would refute the completeness claim).

Inputs used from the earlier work: only the 34 facet vectors (adj_d4_small_final.pkl, key 'f'), converted to slack
tensors; the saved adjacency counts are read ONLY for the final comparison.  Everything else is recomputed here in
my own coordinates (outcome 0 dropped) with my own code.

usage:
  python IND_expand.py classes             # verify the 34 representatives, stabilisers, orbits (cheap)
  python IND_expand.py expand j1 j2 ... [--threads k] [--seed s]
Results: one JSON line per class appended to logs/IND_expand_results.jsonl, certificates (ridge tight sets,
neighbour classes, explicit relabellings) in logs/IND_cert_class<j>.npz.
"""
import sys
import json
import time
import pickle
import numpy as np
import numba as nb
from IND_core import Scen, Matcher, functional_from_slack, is_facet_slack, affine_rank_exact, primitive
import IND_dd

D = 4
JPOS_EXPECTED = 25


def log(*a):
    print(*a, flush=True)


def load_reps(sc):
    S = pickle.load(open("adj_d4_small_final.pkl", "rb"))
    reps = [sc.slack_from_saved(f) for f in S["f"]]
    return reps, S


def positivity_slack(sc, x, y, a, b):
    return np.array([int(l[x] == a and l[2 + y] == b) for l in sc.lams], dtype=np.int64)


def verify_classes(sc, M, reps):
    out = {}
    ok = True
    pos_classes = []
    allpos = [positivity_slack(sc, x, y, a, b) for x in range(2) for y in range(2) for a in range(D) for b in range(D)]
    for j, s in enumerate(reps):
        isf = is_facet_slack(sc, s)
        prim = (np.gcd.reduce(s[s > 0]) == 1)
        ispos = any(np.array_equal(s, p) for p in allpos)
        if ispos:
            pos_classes.append(j)
        ok &= isf and prim
        out[j] = dict(facet=bool(isf), primitive=bool(prim), tight=int((s == 0).sum()), positivity=bool(ispos))
    # every positivity inequality is a facet
    allfac = all(is_facet_slack(sc, p) for p in allpos)
    # pairwise inequivalence (exhaustive matcher) and stabilisers
    inv = [M.invariant(s) for s in reps]
    equiv_pairs = []
    for i in range(len(reps)):
        for k in range(i + 1, len(reps)):
            if M.find(reps[i], reps[k]) is not None:
                equiv_pairs.append((i, k))
    stabs = [M.stabiliser_order(s) for s in reps]
    orbits = [sc.order // st for st in stabs]
    assert all(sc.order % st == 0 for st in stabs)
    # the positivity class: one positivity slack is equivalent to the representative
    return dict(per_class=out, positivity_classes=pos_classes, all_positivity_facets=bool(allfac),
                equivalent_pairs=equiv_pairs, stabilisers=stabs, orbits=orbits, total=int(sum(orbits)),
                invariants_distinct=len(set(inv)) == len(inv), ok=bool(ok))


@nb.njit(cache=True)
def _rotate_all(SG, sF, Tmask):
    """SG (k x L) ridge slacks extended to all points; sF (L) slack of F (>0 off F); Tmask (L) bool tight on F.
    For each ridge: theta* = max_{lam not in F} (-sg/sF) = num/den; new slack den*sg + num*sF (int64)."""
    k, L = SG.shape
    out = np.empty((k, L), np.int64)
    for r in range(k):
        bn = 0
        bd = 0
        first = True
        for l in range(L):
            if Tmask[l]:
                continue
            num = -SG[r, l]
            den = sF[l]
            if first or num * bd > bn * den:
                bn = num
                bd = den
                first = False
        for l in range(L):
            out[r, l] = bd * SG[r, l] + bn * sF[l]
    return out


def expand_class(sc, M, reps, j, seed, nthreads, verbose=True, mode="nbhd", order="zeros"):
    t0 = time.time()
    sF = reps[j]
    T = np.nonzero(sF == 0)[0]
    den, w = functional_from_slack(sc, sF)          # den * sF = h0 - h.X
    h = np.array(w[1:], dtype=object)
    nz = [i for i in range(sc.dim) if h[i] != 0]
    jdrop = nz[0]
    keepc = [i for i in range(sc.dim) if i != jdrop]
    Xd = sc.X[:, keepc]
    P = Xd[T]
    assert affine_rank_exact(P.tolist()) == sc.dim - 1, "projection of the facet is not full-dimensional"
    R, Z, info = IND_dd.facets_of_points(P, seed=seed, nthreads=nthreads, verbose=verbose, label=f"class {j}", mode=mode, order=order)
    t1 = time.time()
    nr = len(R)
    # ridge slacks extended to all deterministic points: s_g(lam) = r0 + r'.Xd(lam)
    SG = R[:, :1] + R[:, 1:] @ Xd.T
    assert (SG[:, T] >= 0).all()
    Tmask = (sF == 0)
    NS = _rotate_all(SG, sF, Tmask)
    # primitive normalisation and exact checks
    g = np.gcd.reduce(np.abs(NS), axis=1)
    assert (g > 0).all()
    NS = NS // g[:, None]
    assert (NS >= 0).all(), "rotation produced an invalid inequality"
    # the neighbour vanishes on the ridge and on at least one point off F
    for r in range(nr):
        ridge = T[SG[r, T] == 0]
        assert (NS[r, ridge] == 0).all()
        assert ((NS[r] == 0) & ~Tmask).any()
    inv_rep = {}
    for k, s in enumerate(reps):
        inv_rep.setdefault(M.invariant(s), []).append(k)
    cls = np.full(nr, -1, np.int64)
    gs = np.full((nr, 5), -1, np.int64)
    new = []
    for r in range(nr):
        cand = inv_rep.get(M.invariant(NS[r]), [])
        for k in cand:
            gg = M.find(reps[k], NS[r])
            if gg is not None:
                cls[r] = k
                gs[r] = gg
                break
        if cls[r] < 0:
            # exhaustive fallback against every representative (invariant mismatch => not equivalent, but
            # we check anyway), then report NEW
            for k in range(len(reps)):
                gg = M.find(reps[k], NS[r])
                if gg is not None:
                    cls[r] = k
                    gs[r] = gg
                    break
            if cls[r] < 0:
                new.append(r)
    counts = {}
    for c in cls.tolist():
        counts[c] = counts.get(c, 0) + 1
    t2 = time.time()
    ridge_bits = np.zeros((nr, 4), np.uint64)
    for r in range(nr):
        for t in T[SG[r, T] == 0]:
            ridge_bits[r, t // 64] |= np.uint64(1) << np.uint64(int(t) % 64)
    np.savez_compressed(f"logs/IND_cert_class{j}.npz", ridge_bits=ridge_bits, neighbour_class=cls, relabelling=gs,
                        neighbour_slack=NS.astype(np.int16) if NS.max() < 32000 else NS)
    res = dict(cls=j, tight=int(len(T)), ridges=int(nr), counts={str(k): v for k, v in sorted(counts.items())},
               new=len(new), dd=info, t_dd=round(t1 - t0, 1), t_classify=round(t2 - t1, 1), seed=seed, mode=mode, order=order)
    return res, new, NS


def main():
    command = sys.argv[1]
    args = sys.argv[2:]
    nthreads = 2
    seed = 7
    if "--threads" in args:
        i = args.index("--threads"); nthreads = int(args[i + 1]); del args[i:i + 2]
    mode = "nbhd"
    if "--mode" in args:
        i = args.index("--mode"); mode = args[i + 1]; del args[i:i + 2]
    order = "zeros"
    if "--order" in args:
        i = args.index("--order"); order = args[i + 1]; del args[i:i + 2]
    if "--seed" in args:
        i = args.index("--seed"); seed = int(args[i + 1]); del args[i:i + 2]
    sc = Scen(D)
    M = Matcher(sc)
    reps, S = load_reps(sc)
    if command == "classes":
        t0 = time.time()
        r = verify_classes(sc, M, reps)
        for j in range(len(reps)):
            log(f"class {j:2d}: {r['per_class'][j]}, stabiliser {r['stabilisers'][j]}, orbit {r['orbits'][j]}")
        log(f"positivity classes: {r['positivity_classes']}; all 64 positivity inequalities are facets: "
            f"{r['all_positivity_facets']}")
        log(f"equivalent pairs among the 34 representatives (should be none): {r['equivalent_pairs']}")
        log(f"invariants pairwise distinct: {r['invariants_distinct']}")
        log(f"orbits {r['orbits']}; total {r['total']}; equal to saved orbits: {r['orbits'] == S['orbits']}")
        log(f"ALL REPRESENTATIVES ARE FACETS: {r['ok']}   [{time.time() - t0:.0f}s]")
        json.dump(dict(stabilisers=r['stabilisers'], orbits=r['orbits'], positivity=r['positivity_classes']),
                  open("logs/IND_classes.json", "w"))
        return
    saved = dict(S["adjacency"])
    saved.update(pickle.load(open("adj_d4_full.pkl", "rb"))["adjacency"])
    for jj in args:
        j = int(jj)
        res, new, NS = expand_class(sc, M, reps, j, seed, nthreads, mode=mode, order=order)
        sv = {str(k): v for k, v in sorted(saved.get(j, {}).items())}
        res["equal_to_saved"] = (res["counts"] == sv)
        log(f"class {j}: tight {res['tight']}, {res['ridges']} ridges, neighbours {res['counts']}, NEW {res['new']}, "
            f"equal to saved expansion: {res['equal_to_saved']}; DD peak {res['dd']['peak']} rays, max entry "
            f"{res['dd']['maxentry']}, exact-rank fallbacks {res['dd']['exact_rank_fallbacks']}  "
            f"[DD {res['t_dd']}s, classify {res['t_classify']}s]")
        for r in new[:5]:
            log(f"   NEW neighbour slack: {NS[r].tolist()}")
        with open("logs/IND_expand_results.jsonl", "a") as fh:
            fh.write(json.dumps(res) + "\n")


if __name__ == "__main__":
    main()
