"""trace_sdp.py -- tracial (unnormalised-trace) moment relaxation of Lemma PA2.

PA2: projections A_{x,a}, B_{y,b} (x, y in {0,1}, a, b in Z_k) on a Hilbert space, A_{x,a} A_{x,a'} = delta A_{x,a},
same for B, Tr A_{x,a} = Tr B_{y,b} = 1 (rank one; rank r by scaling).  Claim: sum c_k[x,y,a,b] Tr(A_{x,a} B_{y,b})
<= k I_ME(k).  Relaxation: moment matrix over NONEMPTY reduced words of length <= L (no identity is needed, so the
Hilbert space dimension never enters), entries Tr(u^* v), real (complex conjugation symmetry), invariant under cyclic
rotation and reversal, PSD.  Any value <= k I_ME(k) at some level PROVES PA2 for that k (all r, all dimensions).
usage: python trace_sdp.py k [L] [solver]"""
import sys, os, itertools, time
import numpy as np
import cvxpy as cp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402


def cglmp_tensor(k):
    C = np.zeros((2, 2, k, k))
    for x, y, a, b in itertools.product(range(2), range(2), range(k), range(k)):
        E = np.zeros((2, 2, k, k)); E[x, y, a, b] = 1.0
        C[x, y, a, b] = core.cglmp(E)
    return C


def reduce_lin(w):
    w = list(w); i = 0
    while i < len(w) - 1:
        g1, o1 = w[i]; g2, o2 = w[i + 1]
        if g1 == g2:
            if o1 != o2: return None
            del w[i + 1]; i = max(i - 1, 0)
        else:
            i += 1
    return w


def reduce_cyc(w):
    w = reduce_lin(w)
    if w is None: return None
    while len(w) > 1 and w[0][0] == w[-1][0]:
        if w[0][1] != w[-1][1]: return None
        w = w[:-1]
        w = reduce_lin(w)
        if w is None: return None
    return tuple(w)


def canon(w):
    n = len(w); cands = []
    for s in (w, tuple(reversed(w))):
        for i in range(n):
            cands.append(s[i:] + s[:i])
    return min(cands)


def build(k, L):
    letters = [(g, o) for g in range(4) for o in range(k)]
    words = [(l,) for l in letters]
    frontier = [(l,) for l in letters]
    for _ in range(L - 1):
        new = []
        for w in frontier:
            for l in letters:
                if l[0] != w[-1][0]:
                    new.append(w + (l,))
        words += new; frontier = new
    n = len(words)
    cls = {}; code = np.zeros((n, n), dtype=np.int64)     # -1 zero, -2 one (single letter), >= 0 class id
    for i, u in enumerate(words):
        ur = tuple(reversed(u))
        for j in range(i, n):
            w = reduce_cyc(ur + words[j])
            if w is None: c = -1
            elif len(w) == 1: c = -2
            else:
                key = canon(w)
                c = cls.setdefault(key, len(cls))
            code[i, j] = code[j, i] = c
    return words, code, len(cls)


def solve(k, L=2, solver='CLARABEL'):
    t0 = time.time()
    words, code, ncls = build(k, L)
    n = len(words)
    C = cglmp_tensor(k)
    X = cp.Variable((n, n), symmetric=True)
    xv = cp.vec(X, order='F')
    flat = code.flatten(order='F')
    cons = [X >> 0]
    zi = np.nonzero(flat == -1)[0]; oi = np.nonzero(flat == -2)[0]
    if len(zi): cons.append(xv[zi] == 0)
    cons.append(xv[oi] == 1)
    # equal entries within each class: tie every entry to the first occurrence
    order = np.argsort(flat, kind='stable'); fs = flat[order]
    pos = order[fs >= 0]; ids = fs[fs >= 0]
    first = np.r_[True, ids[1:] != ids[:-1]]
    rep = np.maximum.accumulate(np.where(first, np.arange(len(ids)), 0))
    tie = ~first
    cons.append(xv[pos[tie]] == xv[pos[rep[tie]]])
    idx = {w: i for i, w in enumerate(words)}
    obj = 0
    for x, y, a, b in itertools.product(range(2), range(2), range(k), range(k)):
        obj = obj + C[x, y, a, b] * X[idx[((x, a),)], idx[((2 + y, b),)]]
    prob = cp.Problem(cp.Maximize(obj), cons)
    prob.solve(solver=solver)
    target = k * core.ime(k)
    print(f"k={k} L={L}: n={n} classes={ncls}  SDP bound = {prob.value:.9f}  k*I_ME(k) = {target:.9f}  "
          f"ratio = {prob.value / target:.9f}  status={prob.status}  ({time.time() - t0:.0f}s)", flush=True)
    return prob.value, target


if __name__ == '__main__':
    k = int(sys.argv[1]); L = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    solver = sys.argv[3] if len(sys.argv) > 3 else 'CLARABEL'
    solve(k, L, solver)
