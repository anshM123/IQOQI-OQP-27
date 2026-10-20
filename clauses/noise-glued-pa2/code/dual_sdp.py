"""dual_sdp.py -- DUAL (sum-of-squares) form of the level-2 PA2 trace relaxation restricted to the words
{letters} u {A_x B_y, B_y A_x}  (enough in all cases tested), reduced by the global shift (Fourier sectors s).
SOS identity sought:  lambda * sum(Tr letters) - S  =  sum_s (1/k) Tr(X_s^* Z_s X_s)  (mod trace relations), Z_s >= 0.
Stage 1: minimal bound.  Stage 2 (optional): among (near-)optimal duals minimise sum_s Tr Z_s (low rank).
usage: python dual_sdp.py k [stage2]"""
import sys, os, itertools, time
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from trace_sdp import cglmp_tensor, reduce_cyc   # noqa: E402
from trace_sdp_sym import canon_shift            # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402


def build(k):
    reps = [((g, 0),) for g in range(4)]
    reps += [((g1, 0), (g2, dl)) for g1 in range(4) for g2 in range(4)
             if (g1 < 2) != (g2 < 2) for dl in range(k)]
    n = len(reps); cls = {}
    code = np.zeros((n, n, k), dtype=np.int64)
    for i, u in enumerate(reps):
        ur = tuple(reversed(u))
        for j, v in enumerate(reps):
            for r in range(k):
                vs = tuple((g, (o + r) % k) for g, o in v)
                w = reduce_cyc(ur + vs)
                code[i, j, r] = -1 if w is None else (-2 if len(w) == 1 else cls.setdefault(canon_shift(w, k), len(cls)))
    return reps, code, cls


def sector_mats(k, code, ncls):
    n = code.shape[0]; om = np.exp(2j * np.pi / k)
    out = []
    for s in range(k):
        ph = om ** (s * np.arange(k))
        Cs = np.zeros((n, n), complex)
        rows, cols, vals = [], [], []
        for i in range(n):
            for j in range(n):
                for r in range(k):
                    c = code[i, j, r]
                    if c == -2: Cs[i, j] += ph[r]
                    elif c >= 0: rows.append(i * n + j); cols.append(c); vals.append(ph[r])   # vec_F index of Z[j,i]: Tr(Z E) = sum Z[j,i] E[i,j]
        Es = sp.csr_matrix((vals, (rows, cols)), shape=(n * n, ncls))
        out.append((Cs, Es))
    return out


def solve(k, stage2=False, tol=2e-6, opts=None):
    t0 = time.time()
    reps, code, cls = build(k); n = len(reps); ncls = len(cls)
    mats = sector_mats(k, code, ncls)
    C = cglmp_tensor(k)
    b = np.zeros(ncls)
    for x, y, a, bb in itertools.product(range(2), range(2), range(k), range(k)):
        b[cls[canon_shift(reduce_cyc(((x, a), (2 + y, bb))), k)]] += C[x, y, a, bb]
    Z = [cp.Variable((n, n), hermitian=True) for _ in range(k)]
    lin = sum(cp.real(Es.T @ cp.vec(Zs, order='F')) for (Cs, Es), Zs in zip(mats, Z))
    obj = sum(cp.real(cp.trace(Zs @ Cs)) for (Cs, Es), Zs in zip(mats, Z))
    cons = [Zs >> 0 for Zs in Z] + [lin == -b]
    opts = dict(opts or {})
    solver = opts.pop('solver', 'CLARABEL')
    p1 = cp.Problem(cp.Minimize(obj), cons); p1.solve(solver=solver, **opts)
    target = k * core.ime(k)
    print(f"k={k}: n={n}/sector, classes={ncls}; dual bound = {p1.value:.10f} target {target:.10f} "
          f"ratio-1 = {p1.value / target - 1:+.2e} ({p1.status}, {time.time() - t0:.0f}s)", flush=True)
    if stage2:
        p2 = cp.Problem(cp.Minimize(sum(cp.real(cp.trace(Zs)) for Zs in Z)),
                        cons + [obj <= target * (1 + tol)])
        p2.solve(solver='CLARABEL')
        print(f"  stage 2 (min trace): {p2.status}, sum Tr Z = {p2.value:.6f}", flush=True)
    return reps, [Zs.value for Zs in Z], cls, code


if __name__ == '__main__':
    k = int(sys.argv[1]); st2 = len(sys.argv) > 2 and sys.argv[2] == 'stage2'
    reps, Zs, cls, code = solve(k, st2)
    names = ['A0', 'A1', 'B0', 'B1']
    for s, Zv in enumerate(Zs):
        w = np.linalg.eigvalsh(Zv)
        print(f"  sector {s}: rank(>1e-6 max) = {(w > 1e-6 * max(w.max(), 1e-12)).sum()}, top eigs {np.round(w[::-1][:6], 5)}")
    np.save(os.path.join(HERE, f'dualZ_k{k}.npy'), np.array(Zs, dtype=object), allow_pickle=True)
