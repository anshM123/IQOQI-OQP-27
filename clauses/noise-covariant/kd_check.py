"""
kd_check.py -- INDEPENDENT re-check (separate code; imports nothing from kd_facets.py / kd_sdp.py / IND_dd.py) of
  (a) the facet list of the cyclic local polytope K_d (naive exact double description in python integers), and
  (b) the max-ent ratio bound of a K_d facet class, by a DIFFERENT relaxation: level-2 moments in PROJECTOR words.

(b) Model.  p(ab|xy) = tau(P^x_a Q^y_b), all projections in one algebra, tau a tracial state; WLOG
tau(w) = tau(reverse w) (direct sum with the transposed strategy).  For projector words w^* = reverse(w), so every
moment tau(w) = tau(w^*) = conj tau(w) is REAL.  Basis W: 1, P^g_a, P^g_a P^h_b (g != h), all a, b in Z_d.
Moments: classes of words up to length 4 reduced by P^g_a P^g_a = P^g_a, P^g_a P^g_b = 0 (a != b), cyclically and
under reversal.  Constraints: M >= 0 (real symmetric), M[1,1] = 1, tau(P^g_a) = 1/d (balanced), completeness
sum_a M[u, v P^g_a] = M[u, v] for every row u and every basis word v with v P^g_a in W.  All data are integers or
1/d, so the certificate is exactly rational:
   F(x) = sum_r c_r x_r <= <Z', M0> + lam.e + sum_r |c_r + <Z', F_r> - (E^T lam)_r| + s N
for Z' + s I = L L^T + R >= 0 (exact LDL check), any lam, every feasible x (|x_r| <= 1, E x = e).
usage: python kd_check.py d [class indices]   (reads kd_facets_d{d}.json only for the class representatives
and compares the facet COUNT with the naive DD below)
"""
import sys
import json
import math
import time
import itertools
from fractions import Fraction
import numpy as np
import cvxpy as cp


# ------------------------------------------------------------------ (a) naive exact DD
def naive_facets(points):
    """facets of conv(points) (integer points, full-dimensional): extreme rays of {(h0,h): h0 + h.p >= 0}.
    Plain Motzkin double description with the algebraic adjacency test (rank of common tight rows)."""
    P = [tuple(int(v) for v in p) for p in points]
    A = [(1,) + p for p in P]
    m, n = len(A), len(A[0])
    # initial basis: greedy independent rows (exact rank via Fractions elimination)
    def rank(rows):
        R = [list(map(Fraction, r)) for r in rows]
        rk = 0; cols = len(R[0]) if R else 0
        for c in range(cols):
            piv = None
            for i in range(rk, len(R)):
                if R[i][c] != 0:
                    piv = i; break
            if piv is None:
                continue
            R[rk], R[piv] = R[piv], R[rk]
            for i in range(len(R)):
                if i != rk and R[i][c] != 0:
                    f = R[i][c] / R[rk][c]
                    R[i] = [R[i][j] - f * R[rk][j] for j in range(cols)]
            rk += 1
        return rk
    basis = []
    for i in range(m):
        if rank([A[j] for j in basis] + [A[i]]) > len(basis):
            basis.append(i)
        if len(basis) == n:
            break
    assert len(basis) == n
    # rays of the simplicial cone {B h >= 0}: columns of B^{-1}
    B = [list(map(Fraction, A[i])) for i in basis]
    # invert B
    inv = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    Bm = [r[:] for r in B]
    for c in range(n):
        piv = next(i for i in range(c, n) if Bm[i][c] != 0)
        Bm[c], Bm[piv] = Bm[piv], Bm[c]; inv[c], inv[piv] = inv[piv], inv[c]
        pv = Bm[c][c]
        Bm[c] = [v / pv for v in Bm[c]]; inv[c] = [v / pv for v in inv[c]]
        for i in range(n):
            if i != c and Bm[i][c] != 0:
                f = Bm[i][c]
                Bm[i] = [Bm[i][j] - f * Bm[c][j] for j in range(n)]
                inv[i] = [inv[i][j] - f * inv[c][j] for j in range(n)]
    rays = []
    for k in range(n):
        r = [inv[i][k] for i in range(n)]
        den = 1
        for v in r:
            den = den * v.denominator // math.gcd(den, v.denominator)
        r = [int(v * den) for v in r]
        g = 0
        for v in r:
            g = math.gcd(g, abs(v))
        rays.append(tuple(v // g for v in r))
    done = set(basis)
    Aarr = np.array(A, dtype=object)
    for i in range(m):
        if i in done:
            continue
        done_list = sorted(done)
        vals = [sum(a * b for a, b in zip(A[i], r)) for r in rays]
        pos = [k for k, v in enumerate(vals) if v > 0]
        neg = [k for k, v in enumerate(vals) if v < 0]
        zer = [k for k, v in enumerate(vals) if v == 0]
        Z = []
        for r in rays:
            Z.append(frozenset(j for j in done_list if sum(a * b for a, b in zip(A[j], r)) == 0))
        new = []
        for p in pos:
            for q in neg:
                common = Z[p] & Z[q]
                if len(common) < n - 2:
                    continue
                # combinatorial test: no other ray's zero set contains common
                ok = True
                for k in range(len(rays)):
                    if k != p and k != q and common <= Z[k]:
                        ok = False; break
                if not ok:
                    continue
                vp, vq = vals[p], vals[q]
                r = tuple(vp * b - vq * a for a, b in zip(rays[p], rays[q]))
                g = 0
                for v in r:
                    g = math.gcd(g, abs(v))
                new.append(tuple(v // g for v in r))
        rays = [rays[k] for k in pos + zer] + new
        done.add(i)
    # final check: each ray valid and tight on a rank n-1 set
    out = []
    for r in rays:
        vals = [sum(a * b for a, b in zip(A[j], r)) for j in range(m)]
        assert min(vals) >= 0
        T = [A[j] for j in range(m) if vals[j] == 0]
        assert rank(T) == n - 1
        out.append(r)
    assert len(set(out)) == len(out)
    return out


def kd_points(d):
    pts = []
    for n1, n2, n3 in itertools.product(range(d), repeat=3):
        n4 = (-n1 - n2 - n3) % d
        v = [0] * (4 * (d - 1))
        for i, nn in enumerate((n1, n2, n3, n4)):
            if nn:
                v[i * (d - 1) + nn - 1] = 1
        pts.append(v)
    return pts


# ------------------------------------------------------------------ (b) projector-word relaxation
def pred(w):
    """reduce a projector word: letters (g, a); P_a P_a = P_a; P_a P_b = 0 (a != b, same g) -> None"""
    out = []
    for (g, a) in w:
        if out and out[-1][0] == g:
            if out[-1][1] == a:
                continue
            return None
        out.append((g, a))
    return tuple(out)


def pcyc(w):
    w = pred(w)
    if w is None:
        return None
    w = list(w)
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        if w[0][1] != w[-1][1]:
            return None
        w = w[:-1]                      # P_a ... P_a  ~ cyclically  P_a ... (merge)
    return tuple(w)


def pclass(w):
    w = pcyc(w)
    if w is None:
        return None
    if len(w) == 0:
        return ()
    L = len(w)
    c = []
    for s in range(L):
        r = w[s:] + w[:s]
        c.append(r); c.append(tuple(reversed(r)))
    return min(c)


def relax(d, c, eps=1e-10):
    """F(p) = sum_i sum_n c_i(n_i) as a Bell functional; returns (UB on F, float value)."""
    c = np.asarray(c, int)
    # c'_xy(m) on m = b - a
    cpr = {(0, 0): lambda m: c[0, m % d], (0, 1): lambda m: c[1, (-m) % d],
           (1, 0): lambda m: c[2, (-m) % d], (1, 1): lambda m: c[3, m % d]}
    letters = [(g, a) for g in range(4) for a in range(d)]
    W = [()] + [(l,) for l in letters] + [(l1, l2) for l1 in letters for l2 in letters if l1[0] != l2[0]]
    idx = {w: i for i, w in enumerate(W)}
    N = len(W)
    cls = {}
    Mcls = [[None] * N for _ in range(N)]
    for i, u in enumerate(W):
        ur = tuple(reversed(u))
        for j, v in enumerate(W):
            k = pclass(ur + v)
            if k is not None and k not in cls:
                cls[k] = len(cls)
            Mcls[i][j] = None if k is None else cls[k]
    nv = len(cls)
    # equalities E x = e
    rowsE = []
    rhs = []
    rowsE.append({cls[()]: 1}); rhs.append(Fraction(1))
    for (g, a) in letters:
        rowsE.append({cls[pclass(((g, a),))]: 1}); rhs.append(Fraction(1, d))
    # completeness: sum_a M[u, v P^g_a] = M[u, v]
    for i, u in enumerate(W):
        for v in [()] + [(l,) for l in letters]:
            for g in range(4):
                if len(v) == 1 and v[0][0] == g:
                    continue
                kids = [v + ((g, a),) for a in range(d)]
                if not all(k in idx for k in kids):
                    continue
                row = {}
                for k in kids:
                    cc = Mcls[i][idx[k]]
                    if cc is not None:
                        row[cc] = row.get(cc, 0) + 1
                cc = Mcls[i][idx[v]]
                if cc is not None:
                    row[cc] = row.get(cc, 0) - 1
                row = {k_: v_ for k_, v_ in row.items() if v_ != 0}
                if row:
                    rowsE.append(row); rhs.append(Fraction(0))
    # objective
    obj = {}
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    k = cls[pclass(((x, a), (2 + y, b)))]
                    obj[k] = obj.get(k, 0) + int(cpr[(x, y)](b - a))
    # cvxpy
    X = cp.Variable(nv)
    Mexpr_rows = []
    import scipy.sparse as sps
    data = []; ri = []; ci = []
    for i in range(N):
        for j in range(N):
            k = Mcls[i][j]
            if k is not None:
                ri.append(i * N + j); ci.append(k); data.append(1.0)
    Amap = sps.csr_matrix((data, (ri, ci)), shape=(N * N, nv))
    Mv = cp.reshape(Amap @ X, (N, N), order="C")
    Er = sps.lil_matrix((len(rowsE), nv))
    for r, row in enumerate(rowsE):
        for k_, v_ in row.items():
            Er[r, k_] = v_
    Er = Er.tocsr()
    ev = np.array([float(v) for v in rhs])
    oc = np.zeros(nv)
    for k_, v_ in obj.items():
        oc[k_] = v_
    psd = (Mv + Mv.T) / 2 >> 0
    eqc = Er @ X == ev
    prob = cp.Problem(cp.Maximize(oc @ X), [psd, eqc, X <= 1, X >= -1])
    t0 = time.time()
    prob.solve(solver="SCS", eps=eps, max_iters=300000)
    Z = psd.dual_value
    lam = eqc.dual_value
    # ---------------- exact certificate
    sc = 2 ** 80
    Z = (Z + Z.T) / 2
    Zi = np.array([[int(round(Z[i, j] * sc)) for j in range(N)] for i in range(N)], dtype=object)
    lam_q = [Fraction(int(round(l * 2 ** 40)), 2 ** 40) for l in lam]
    evs = np.linalg.eigvalsh(Z)
    s_float = max(0.0, -evs.min()) + 2e-5
    s_int = int(math.ceil(s_float * sc))
    assert psd_llt(Zi, s_int, sc), "PSD certificate failed"
    # coefficients e_r = c_r + <Z', F_r> - (E^T lam)_r ; constant <Z', M0> = 0 (no constant entries)
    ZF = np.zeros(nv, dtype=object)
    for i in range(N):
        for j in range(N):
            k = Mcls[i][j]
            if k is not None:
                ZF[k] += Zi[i, j]
    ETl = [Fraction(0)] * nv
    for r, row in enumerate(rowsE):
        for k_, v_ in row.items():
            ETl[k_] += lam_q[r] * v_
    lam_e = sum((lam_q[r] * rhs[r] for r in range(len(rhs))), Fraction(0))
    base = [Fraction(int(obj.get(k_, 0))) + Fraction(int(ZF[k_]), sc) for k_ in range(nv)]
    sN = Fraction(s_int, sc) * N
    # valid for ANY multiplier vector; try lam and -lam
    ub = lam_e + sum((abs(base[k_] - ETl[k_]) for k_ in range(nv)), Fraction(0)) + sN
    ub2 = -lam_e + sum((abs(base[k_] + ETl[k_]) for k_ in range(nv)), Fraction(0)) + sN
    return prob.value, min(ub, ub2), time.time() - t0, nv, N


def psd_llt(Zi, s_int, sc):
    """exact: Zi + s_int I = L L^T + R with L integer (L L^T ~ Zi + s I at scale sc = K^2) and R diagonally dominant
    with nonnegative diagonal  =>  Zi + s_int I >= 0."""
    N = Zi.shape[0]
    T = Zi.copy()
    for i in range(N):
        T[i, i] += s_int
    Tf = np.array(T, dtype=float) / sc
    Lf = np.linalg.cholesky(Tf - 0.5 * (s_int / sc) * np.eye(N))     # L L^T ~ T - (s/2) I, remainder ~ (s/2) I
    K = int(math.isqrt(sc))
    assert K * K == sc
    L = np.array([[int(round(Lf[i, j] * K)) for j in range(N)] for i in range(N)], dtype=object)
    R = T - L.dot(L.T)
    for i in range(N):
        off = sum(abs(R[i, j]) for j in range(N) if j != i)
        if R[i, i] < off:
            return False
    return True


def ldl_pd(A):
    n = len(A)
    A = [row[:] for row in A]
    for k in range(n):
        if A[k][k] <= 0:
            return False
        piv = A[k][k]
        for i in range(k + 1, n):
            if A[i][k] != 0:
                f = A[i][k] / piv
                Ai = A[i]; Ak = A[k]
                for j in range(k + 1, n):
                    if Ak[j] != 0:
                        Ai[j] -= f * Ak[j]
    return True


def kappa_q(d, prec=60):
    """kappa_d with mpmath intervals"""
    import mpmath as mp
    mp.mp.dps = prec
    iv = mp.iv
    iv.dps = prec
    s = iv.mpf(0)
    for j in range(1, d):
        s += iv.mpf(d - j) / iv.cos(iv.pi * j / (2 * d))
    return s * 4 / (d * (d - 1)) / 2


if __name__ == "__main__":
    d = int(sys.argv[1])
    which = [int(a) for a in sys.argv[2].split(",")] if len(sys.argv) > 2 else None
    EPS = float(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != 'dd' else 1e-10
    t0 = time.time()
    if which is None or "dd" in sys.argv:
        F = naive_facets(kd_points(d))
        print(f"(a) naive exact DD: K_{d} has {len(F)} facets [{time.time()-t0:.0f}s]", flush=True)
    classes = json.load(open(f"kd_facets_d{d}.json"))
    print(f"    listed classes: {len(classes)}, total {sum(c['size'] for c in classes)}")
    kap = kappa_q(d)
    if which:
        for ci in which:
            c = np.array(classes[ci]["c"])
            Fu = Fraction(int(c.sum()), d)
            val, ub, tt, nv, N = relax(d, c, eps=EPS)
            r_ub = (ub - Fu) / (-Fu)
            import mpmath as mp
            r_iv = mp.iv.mpf(r_ub.numerator) / mp.iv.mpf(r_ub.denominator)
            print(f"(b) class {ci}: projector-word relaxation float max F = {val:.9f}, float ratio "
                  f"{(val - float(Fu)) / float(-Fu):.9f}; EXACT rational UB ratio = {float(r_ub):.12f} "
                  f"(kappa_d in {kap}) -> {'CERTIFIED < kappa_d' if r_iv.b < kap.a else 'not certified'} "
                  f"[{nv} moment classes, N = {N}, {tt:.0f}s]", flush=True)
