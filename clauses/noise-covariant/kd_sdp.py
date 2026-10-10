"""
kd_sdp.py -- level-2 tracial moment relaxation for LINK-DIFFERENCE Bell functionals of (2,2,d), balanced max-ent
strategies (rank-D/d PVMs on any Phi_D), with an exact dual certificate.  Written for THEORY_C2C3 (own code; the
model is the one of P3_full_theory/IND_sdp.py, generalised to every d and reduced by the cyclic shift symmetry).

Model.  p(ab|xy) = tau(P^x_a Q^y_b) with projections in ONE algebra (P = A^T), tau = tr/D.  Clock unitaries
U_g = sum_a w^a P^g_a (g = 0,1 Alice, g = 2,3 Bob), U_g^d = 1, balanced: tau(U_g^n) = 0 (n != 0 mod d).
WLOG tau(w) = tau(reverse w) (direct sum with the transposed strategy).  Link laws
   Q_xy(m) = P(b - a = m) = (1/d) sum_n w^{nm} tau(U_x^n U_{2+y}^{-n}).
Functional F = sum_xy sum_m c'_xy(m) Q_xy(m)  =>  F - F(u) = (1/d) sum_xy sum_{n=1}^{d-1} C_xy(n) tau(U_x^n U_{2+y}^{-n}),
C_xy(n) = sum_m c'_xy(m) w^{nm}.
Shift symmetry: a -> a+1 for all outcomes multiplies U_g by w; F is invariant, and averaging the moments over the
shifts keeps every constraint (unitary conjugation of M by diag(w^{s charge(u)})), so WLOG tau(word) = 0 unless
the total exponent ("charge") is 0 mod d; M is then block diagonal by the charge of the basis words.
Level 2: basis words of length <= 2 (adjacent letters from different generators).  M[u,v] = tau(u^* v) = moment of
the dihedral class of the cyclically reduced word u^* v; M >= 0, diag = 1, empty class = 1, single letters = 0.
Certificate (exact up to arb balls for the irrational coefficients): for symmetric Z'_q and s >= 0 with
Z'_q + s I = L L^T + E (L dyadic, E exactly diagonally dominant with nonnegative diagonal):
   F - F(u) = sum_r c_r x_r <= sum_q <Z'_q, Emb M0_q> + sum_r |c_r + sum_q <Z'_q, Emb F_{q,r}>| + s * sum_q 2 N_q
using |x_r| <= 1 (every moment is the trace of a unitary).
"""
import sys
import json
import math
import time
import itertools
import numpy as np
import cvxpy as cp
import flint
from fractions import Fraction


def red(w, d):
    out = []
    for (g, n) in w:
        n %= d
        if n == 0:
            continue
        if out and out[-1][0] == g:
            m = (out[-1][1] + n) % d
            out.pop()
            if m:
                out.append((g, m))
        else:
            out.append((g, n))
    return tuple(out)


def cyc_red(w, d):
    w = list(red(w, d))
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        g = w[0][0]
        m = (w[0][1] + w[-1][1]) % d
        w = w[1:-1]
        if m:
            w = [(g, m)] + w
        w = list(red(w, d))
    return tuple(w)


def dclass(w, d):
    w = cyc_red(w, d)
    if len(w) == 0:
        return ()
    cands = []
    L = len(w)
    for s in range(L):
        r = w[s:] + w[:s]
        cands.append(r)
        cands.append(tuple(reversed(r)))
    return min(cands)


def neg(w, d):
    return tuple((g, (-n) % d) for (g, n) in w)


def charge(w, d):
    return sum(n for (_, n) in w) % d


def build(d):
    letters = [(g, n) for g in range(4) for n in range(1, d)]
    words = [()] + [(l,) for l in letters] + [(a, b) for a in letters for b in letters if a[0] != b[0]]
    blocks = {}
    for w in words:
        blocks.setdefault(charge(w, d), []).append(w)
    cls_index = {}
    entries = {}                       # q -> list of (i, j, class)
    for q, ws in blocks.items():
        ent = []
        for i, u in enumerate(ws):
            us = tuple(reversed(neg(u, d)))
            for j, v in enumerate(ws):
                k = dclass(us + v, d)
                ent.append((i, j, k))
                if k not in cls_index:
                    cls_index[k] = len(cls_index)
        entries[q] = ent
    return letters, blocks, entries, cls_index


def variables(cls_index, d):
    """real variables: for each conjugate pair {k, kbar}: Re, Im of the representative; self-conjugate: Re only.
    fixed: () = 1; single-letter classes and any class whose cyclic reduction has length 1 = 0."""
    rep = {}
    var = []
    for k in cls_index:
        if k in rep:
            continue
        kb = dclass(neg(k, d), d) if len(k) else ()
        if len(k) == 0:
            rep[k] = ("const", 1.0)
            continue
        if len(k) == 1:
            rep[k] = ("const", 0.0); rep[kb] = ("const", 0.0)
            continue
        if kb == k:
            rep[k] = ("real", len(var)); var.append((k, "re"))
        else:
            rep[k] = ("cplx", len(var), +1); rep[kb] = ("cplx", len(var), -1)
            var.append((k, "re")); var.append((k, "im"))
    return rep, var


def moment_expr(k, rep):
    """(const complex, list of (var index, complex coefficient)) for tau(class k)"""
    r = rep[k]
    if r[0] == "const":
        return complex(r[1]), []
    if r[0] == "real":
        return 0j, [(r[1], 1.0 + 0j)]
    _, i, s = r
    return 0j, [(i, 1.0 + 0j), (i + 1, s * 1j)]


def objective(c, d, rep):
    """F - F(u) as a real-linear function sum_r obj[r] x_r ; complex coefficients C_xy(n)/d."""
    c = np.asarray(c, float)
    cp_ = np.zeros((2, 2, d))
    for m in range(d):
        cp_[0, 0, m] = c[0, m]; cp_[0, 1, m] = c[1, (-m) % d]; cp_[1, 0, m] = c[2, (-m) % d]; cp_[1, 1, m] = c[3, m]
    Fu = cp_.sum() / d
    terms = {}
    for x in range(2):
        for y in range(2):
            for n in range(1, d):
                C = sum(cp_[x, y, m] * np.exp(2j * np.pi * n * m / d) for m in range(d)) / d
                k = dclass(((x, n), (2 + y, (-n) % d)), d)
                const, lin = moment_expr(k, rep)
                for (i, a) in lin:
                    terms[i] = terms.get(i, 0j) + C * a
    return Fu, cp_, terms


def solve(d, c, eps=1e-9, verbose=False, solver="SCS"):
    """sparse version: vec(Emb M_q) = M0vec_q + B_q x  (B_q integer, entries 0/+-1)."""
    import scipy.sparse as sps
    letters, blocks, entries, cls_index = build(d)
    rep, var = variables(cls_index, d)
    nv = len(var)
    Fu, cp_, terms = objective(c, d, rep)
    x = cp.Variable(nv)
    cons = [x <= 1, x >= -1]
    mats = {}
    for q, ws in blocks.items():
        N = len(ws)
        n2 = 2 * N
        M0 = np.zeros((n2, n2))
        rows, cols, vals = [], [], []
        for (i, j, k) in entries[q]:
            const, lin = moment_expr(k, rep)
            M0[i, j] += const.real; M0[i + N, j + N] += const.real
            M0[i, j + N] += -const.imag; M0[i + N, j] += const.imag
            for (vi, a) in lin:
                ar, ai = int(round(a.real)), int(round(a.imag))
                assert abs(a.real - ar) < 1e-12 and abs(a.imag - ai) < 1e-12
                for (r_, c_, v_) in ((i, j, ar), (i + N, j + N, ar), (i, j + N, -ai), (i + N, j, ai)):
                    if v_ != 0:
                        rows.append(r_ * n2 + c_); cols.append(vi); vals.append(v_)
        B = sps.csr_matrix((np.array(vals, dtype=np.int64), (rows, cols)), shape=(n2 * n2, nv))
        mats[q] = (M0, B, N)
        X = cp.reshape(M0.flatten() + B.astype(float) @ x, (n2, n2), order="C")
        cons.append((X + X.T) / 2 >> 0)
    obj_c = np.zeros(nv)
    for i, a in terms.items():
        obj_c[i] += a.real
    prob = cp.Problem(cp.Maximize(obj_c @ x), cons)
    t0 = time.time()
    if solver == "SCS":
        prob.solve(solver="SCS", eps=eps, max_iters=200000, verbose=verbose)
    else:
        prob.solve(solver=solver, verbose=verbose)
    psd_duals = [cn.dual_value for cn in cons[2:]]
    return dict(Fu=Fu, val=prob.value, x=x.value, obj_c=obj_c, mats=mats, duals=psd_duals, blocks=blocks,
                time=time.time() - t0, nv=nv, terms=terms)


def certify(sol, d, c, scale_bits=40):
    """exact certificate (sparse): UB on F - F(u) as an arb ball."""
    flint.ctx.prec = 200
    c = np.asarray(c, int)
    cp_ = [[[0] * d for _ in range(2)] for _ in range(2)]
    for m in range(d):
        cp_[0][0][m] = int(c[0, m]); cp_[0][1][m] = int(c[1, (-m) % d])
        cp_[1][0][m] = int(c[2, (-m) % d]); cp_[1][1][m] = int(c[3, m])
    letters, blocks, entries, cls_index = build(d)
    rep, var = variables(cls_index, d)
    nv = len(var)
    obj = {}
    for x_ in range(2):
        for y in range(2):
            for n in range(1, d):
                Cre = flint.arb(0); Cim = flint.arb(0)
                for m in range(d):
                    ang = flint.arb.pi() * 2 * n * m / d
                    Cre += cp_[x_][y][m] * ang.cos(); Cim += cp_[x_][y][m] * ang.sin()
                Cre /= d; Cim /= d
                k = dclass(((x_, n), (2 + y, (-n) % d)), d)
                r = rep[k]
                if r[0] == "const":
                    continue
                if r[0] == "real":
                    obj[r[1]] = obj.get(r[1], flint.arb(0)) + Cre
                else:
                    _, i, s = r
                    obj[i] = obj.get(i, flint.arb(0)) + Cre
                    obj[i + 1] = obj.get(i + 1, flint.arb(0)) - s * Cim
    sc = 2 ** scale_bits
    ZB = np.zeros(nv, dtype=object)
    total_const = 0
    s_total = Fraction(0)
    for qi, (q, (M0, B, N)) in enumerate(sol["mats"].items()):
        Z = sol["duals"][qi]
        Z = (Z + Z.T) / 2
        Zi = np.rint(Z * sc).astype(np.int64)
        ev = np.linalg.eigvalsh(Z)
        s_int = int(math.ceil((max(0.0, -ev.min()) + 1e-9) * sc)) + 1
        n2 = Zi.shape[0]
        A = [[Fraction(int(Zi[i, j])) for j in range(n2)] for i in range(n2)]
        for i in range(n2):
            A[i][i] += s_int
        if not ldl_psd(A):
            raise RuntimeError("PSD certificate failed for block %d" % q)
        s_total += Fraction(s_int, sc) * n2
        total_const += int(np.sum(Zi.astype(object) * np.rint(M0).astype(np.int64).astype(object)))
        zv = Zi.flatten().astype(np.int64)
        BT = B.T.tocsr()
        contrib = BT @ zv                                  # exact int64 (|entries| < 2^63 checked below)
        assert np.abs(zv).max() * max(1, B.getnnz(axis=0).max()) < 2 ** 62
        for vi in range(nv):
            if contrib[vi] != 0:
                ZB[vi] += int(contrib[vi])
    ub = flint.arb(flint.fmpq(total_const, sc))
    for vi in range(nv):
        e = obj.get(vi, flint.arb(0)) + flint.arb(flint.fmpq(int(ZB[vi]), sc))
        ub += abs(e)
    ub += flint.arb(flint.fmpq(s_total.numerator, s_total.denominator))
    return sol["Fu"], ub


def ldl_psd(A):
    """exact test that the symmetric rational matrix A is positive definite (Cholesky-free LDL^T)."""
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


if __name__ == "__main__":
    d = int(sys.argv[1])
    which = sys.argv[2] if len(sys.argv) > 2 else "all"
    kap = (4.0 / (d * (d - 1)) * float(np.sum((d - np.arange(1, d)) / np.cos(np.pi * np.arange(1, d) / (2 * d))))) / 2
    classes = json.load(open(f"kd_facets_d{d}.json"))
    for ci, cl in enumerate(classes):
        if which != "all" and str(ci) not in which.split(","):
            continue
        c = np.array(cl["c"])
        sol = solve(d, c, eps=1e-10)
        Fu = sol["Fu"]
        r = (sol["val"]) / (0 - Fu)
        print(f"d={d} class {ci} (size {cl['size']}, tight {cl['tight']}): SDP value F-F(u) = {sol['val']:.10f}, "
              f"ratio {r:.8f} (kappa_d {kap:.8f}), {sol['nv']} vars, {sol['time']:.1f}s", flush=True)


def kappa_arb(d):
    flint.ctx.prec = 200
    s = flint.arb(0)
    for j in range(1, d):
        s += flint.arb(d - j) / (flint.arb.pi() * j / (2 * d)).cos()
    return s * 4 / (d * (d - 1)) / 2


def certify_class(d, c, eps=1e-10, solver="SCS"):
    sol = solve(d, c, eps=eps, solver=solver)
    Fu, ub = certify(sol, d, c)
    Fu_exact = flint.fmpq(int(np.asarray(c).sum()), d)        # F(u) = (1/d) sum_i sum_n c_i(n)
    ratio_ub = ub / (-flint.arb(Fu_exact))
    return sol, ub, ratio_ub
