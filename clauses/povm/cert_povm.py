"""
cert_povm.py -- build an exact certificate (over Q(zeta_{4d})) for the maximally-entangled CGLMP bound
S >= S_DKZ for GENERAL POVMs from exact_povm_d{d}.pkl (adapted from publish/CGLMP/builders/cert_tracial.py;
same pipeline, POVM relaxation of exact_povm.py: moment blocks + doubly-localizing blocks).

Steps: face restriction X_b = N_b Y_b N_b^dag (N_b = exact kernel of the symmetrised DKZ moment block),
numerical reduced SDP (ipm.py), rounding of Y to Gaussian rationals, exact projection onto the affine
space of the linear SOS identities, exact Hermitian LDL^T positivity check.
Output: cert_tracial_d{d}.pkl
"""
import sys
import time
import pickle
from fractions import Fraction
import numpy as np
import mpmath as mp
from cyclo import Field
import ipm
USE_MODULAR = False


def mat_herm_full(F, n, ent, var):
    """dense n x n list-of-lists of F values: coefficient matrix of variable var in block."""
    M = [[F.zero] * n for _ in range(n)]
    for (i, j), dct in ent.items():
        if var in dct:
            c = dct[var]
            M[i][j] = c
            if i != j:
                M[j][i] = F.conj(c)
    return M


def reduce_mat(F, N, M):
    """N^dag M N ; N as list of column vectors (each list of F of length n)."""
    k = len(N)
    n = len(M)
    # MN
    MN = [[F.zero] * k for _ in range(n)]
    for a in range(n):
        row = M[a]
        nz = [(b, row[b]) for b in range(n) if not F.is_zero(row[b])]
        if not nz:
            continue
        for c in range(k):
            acc = F.zero
            col = N[c]
            for (b, v) in nz:
                if not F.is_zero(col[b]):
                    acc = F.add(acc, F.mul(v, col[b]))
            MN[a][c] = acc
    out = [[F.zero] * k for _ in range(k)]
    active = [a for a in range(n) if any(not F.is_zero(x) for x in MN[a])]
    conjN = {}
    for r in range(k):
        colr = N[r]
        for a in active:
            if not F.is_zero(colr[a]):
                conjN[(r, a)] = F.conj(colr[a])
    for r in range(k):
        for c in range(k):
            acc = F.zero
            for a in active:
                cr = conjN.get((r, a))
                if cr is not None and not F.is_zero(MN[a][c]):
                    acc = F.add(acc, F.mul(cr, MN[a][c]))
            out[r][c] = acc
    return out


def to_np(F, M):
    return np.array([[F.to_cfloat(x) for x in row] for row in M], dtype=complex)


def main(d, denom_bits=40, verbose=True):
    t0 = time.time()
    data = pickle.load(open(f"exact_povm_d{d}.pkl", "rb"))
    N = data["N"]
    F = Field(N)
    nvar = data["st_nvar"]
    obj = data["obj"]
    const = data["const"]
    lam = data["S_dkz"]
    bdata = data["bdata"]
    kernels = data["kernels"]
    # reduced coefficient matrices per block per variable (incl. -1 = constant)
    red = []   # list over blocks of dict var -> k x k F-matrix
    for (lab, els, ent), ker in zip(bdata, kernels):
        n = len(els)
        k = len(ker)
        vars_here = set()
        for dct in ent.values():
            vars_here |= set(dct.keys())
        dct_b = {}
        if k == 0:
            red.append(dct_b)
            continue
        for v in sorted(vars_here):
            M = mat_herm_full(F, n, ent, v)
            R = reduce_mat(F, ker, M)
            if any(not F.is_zero(x) for row in R for x in row):
                dct_b[v] = R
        red.append(dct_b)
    if verbose:
        print(f"d={d}: reduced sizes {[len(k) for k in kernels]} [{time.time()-t0:.1f}s]", flush=True)
    # numeric reduced SDP (moment form): minimise c.y + const s.t. sum_v y_v Mt_v + Mt_c >= 0
    M0, Ms, keep = [], [], []
    for b, dct_b in enumerate(red):
        k = len(kernels[b])
        if k == 0:
            continue
        B0 = to_np(F, dct_b[-1]) if -1 in dct_b else np.zeros((k, k), complex)
        Bj = {v: to_np(F, R) for v, R in dct_b.items() if v >= 0}
        M0.append(B0)
        Ms.append(Bj)
        keep.append(b)
    cvec = np.zeros(nvar)
    for v, c in obj.items():
        cvec[v] = F.to_cfloat(c).real
    constf = F.to_cfloat(const).real
    res = ipm.solve(M0, Ms, cvec, constf, tol=1e-13, maxit=150)
    lamf = F.to_cfloat(lam).real
    if verbose:
        print(f"   reduced SDP: bound={res['pobj_bound']:.14f} moment={res['obj']:.14f} target={lamf:.14f}"
              f" rp={res['rp']:.1e} gap={res['gap']:.1e}", flush=True)
        for bi, Xb in zip(keep, res["X"]):
            ev = np.linalg.eigvalsh(Xb)
            print(f"      block {bi} {bdata[bi][0]} k={Xb.shape[0]} Y eig min {ev.min():.3e} max {ev.max():.3e}")
    # ---------- unknown coordinates: for each kept block, diag y_ii (real), off-diag a_ij, b_ij
    coords = []   # (b, i, j, kind) kind in 'd','a','b'
    for b in keep:
        k = len(kernels[b])
        for i in range(k):
            coords.append((b, i, i, 'd'))
            for j in range(i + 1, k):
                coords.append((b, i, j, 'a'))
                coords.append((b, i, j, 'b'))
    cidx = {c: t for t, c in enumerate(coords)}
    # equations: for v in 0..nvar-1:  sum_b tr(Y_b Mt_b^v) = c_v ; and constant: sum_b tr(Y_b Mt_b^c) = const - lam
    eq_rows = []
    rhs = []
    two = F.from_int(2)
    for v in list(range(nvar)) + [-1]:
        row = {}
        for b in keep:
            if v not in red[b]:
                continue
            R = red[b][v]
            k = len(R)
            for i in range(k):
                if not F.is_zero(R[i][i]):
                    row[cidx[(b, i, i, 'd')]] = F.re(R[i][i])
                for j in range(i + 1, k):
                    m = R[i][j]
                    if F.is_zero(m):
                        continue
                    re_, im_ = F.re(m), F.im(m)
                    if not F.is_zero(re_):
                        row[cidx[(b, i, j, 'a')]] = F.mul(two, re_)
                    if not F.is_zero(im_):
                        row[cidx[(b, i, j, 'b')]] = F.mul(two, im_)
        if v >= 0:
            r = obj.get(v, F.zero)
        else:
            r = F.sub(const, lam)
        if not row:
            assert F.is_zero(r), f"inconsistent equation for var {v}"
            continue
        eq_rows.append(row)
        rhs.append(r)
    if verbose:
        print(f"   {len(eq_rows)} equations, {len(coords)} unknowns [{time.time()-t0:.1f}s]", flush=True)
    # ---------- rounding
    D = 1 << denom_bits
    u = [None] * len(coords)
    Xmap = {b: Xb for b, Xb in zip(keep, res["X"])}
    for t, (b, i, j, kind) in enumerate(coords):
        val = Xmap[b][i, j]
        if kind == 'd':
            u[t] = F.from_frac(Fraction(round(val.real * D), D))
        elif kind == 'a':
            u[t] = F.from_frac(Fraction(round(val.real * D), D))
        else:
            u[t] = F.from_frac(Fraction(round(val.imag * D), D))
    # residual
    resid = []
    for row, r in zip(eq_rows, rhs):
        acc = F.zero
        for t, a in row.items():
            acc = F.add(acc, F.mul(a, u[t]))
        resid.append(F.sub(r, acc))
    maxres = max(abs(F.to_cfloat(x)) for x in resid)
    if verbose:
        print(f"   max residual after rounding: {maxres:.2e}", flush=True)
    m = len(eq_rows)
    if USE_MODULAR:
        # ---------- projection by a well-conditioned pivot subsystem (multi-modular exact solve)
        import scipy.linalg as sla
        import modsolve2
        nun = len(coords)
        Af = np.zeros((m, nun))
        for e, row in enumerate(eq_rows):
            for t, a in row.items():
                Af[e, t] = F.to_cfloat(a).real
        Q, Rr, piv = sla.qr(Af, pivoting=True, mode='economic')
        dg = np.abs(np.diag(Rr))
        rank = int((dg > 1e-9 * dg[0]).sum())
        cols_sel = list(piv[:rank])
        Q2, R2, piv2 = sla.qr(Af[:, cols_sel].T, pivoting=True, mode='economic')
        rows_sel = list(piv2[:rank])
        if verbose:
            print(f"   pivot subsystem {rank}x{rank} (of {m} eqs, {nun} unknowns) [{time.time()-t0:.1f}s]", flush=True)
        Msub = [[eq_rows[r].get(c, F.zero) for c in cols_sel] for r in rows_sel]
        rsub = [resid[r] for r in rows_sel]
        import os as _os2
        if _os2.environ.get("DUMP_SUBSYSTEM"):
            with open(f"subsys_d{d}.pkl", "wb") as _fh:
                pickle.dump(dict(Msub=Msub, rsub=rsub, N=N, deg=F.deg, cols_sel=cols_sel, rows_sel=rows_sel,
                                 u=u, coords=coords, eq_rows=eq_rows, rhs=rhs, keep=keep, kernels=kernels,
                                 lam=lam, bdata=bdata), _fh)
            print("   subsystem dumped", flush=True)
        def check_sol(zz):
            for i in range(rank):
                acc = F.zero
                for j in range(rank):
                    if not F.is_zero(Msub[i][j]) and not F.is_zero(zz[j]):
                        acc = F.add(acc, F.mul(Msub[i][j], zz[j]))
                if not F.is_zero(F.sub(acc, rsub[i])):
                    return False
            return True
        import os as _os
        if _os.environ.get("SOLVER") == "dixon":
            import dixon
            z = dixon.solve(Msub, rsub, N, F.deg, verbose=verbose, check=check_sol)
        elif _os.environ.get("SOLVER") == "dixon2":
            import dixon2
            z = dixon2.solve(Msub, rsub, N, F.deg, verbose=verbose, check=check_sol)
        elif _os.environ.get("MODSOLVE_PAR"):
            import modsolve3
            z = modsolve3.solve(Msub, rsub, N, F.deg, p_ext=None, verbose=verbose, check=check_sol,
                                workers=int(_os.environ.get("MODSOLVE_PAR")))
        else:
            z = modsolve2.solve(Msub, rsub, N, F.deg, p_ext=None, verbose=verbose, check=check_sol)
        du = {c: z[j] for j, c in enumerate(cols_sel)}
    else:
        # ---------- projection: solve (A A^T) z = resid, du = A^T z
        G = [[F.zero] * m for _ in range(m)]
        cols = {}
        for e, row in enumerate(eq_rows):
            for t, a in row.items():
                cols.setdefault(t, []).append((e, a))
        for t, lst in cols.items():
            for (e1, a1) in lst:
                for (e2, a2) in lst:
                    if e2 >= e1:
                        G[e1][e2] = F.add(G[e1][e2], F.mul(a1, a2))
        for e1 in range(m):
            for e2 in range(e1):
                G[e1][e2] = G[e2][e1]
        if verbose:
            print(f"   Gram built [{time.time()-t0:.1f}s]; solving {m}x{m} exactly...", flush=True)
        z = solve_exact(F, G, resid, verbose=verbose)
        du = {}
        for t, lst in cols.items():
            acc = F.zero
            for (e, a) in lst:
                if z[e] is not None:
                    acc = F.add(acc, F.mul(a, z[e]))
            du[t] = acc
    u2 = [F.add(u[t], du.get(t, F.zero)) for t in range(len(coords))]
    # verify equations exactly
    for row, r in zip(eq_rows, rhs):
        acc = F.zero
        for t, a in row.items():
            acc = F.add(acc, F.mul(a, u2[t]))
        assert F.is_zero(F.sub(acc, r)), "projection failed"
    if verbose:
        print(f"   exact equations satisfied [{time.time()-t0:.1f}s]", flush=True)
    # assemble Y blocks
    Y = {}
    iu = F.i_unit()
    for b in keep:
        k = len(kernels[b])
        Yb = [[F.zero] * k for _ in range(k)]
        Y[b] = Yb
    for t, (b, i, j, kind) in enumerate(coords):
        if kind == 'd':
            Y[b][i][i] = u2[t]
        elif kind == 'a':
            Y[b][i][j] = F.add(Y[b][i][j], u2[t])
        else:
            Y[b][i][j] = F.add(Y[b][i][j], F.mul(iu, u2[t]))
    for b in keep:
        k = len(kernels[b])
        for i in range(k):
            for j in range(i + 1, k):
                Y[b][j][i] = F.conj(Y[b][i][j])
    # exact LDL positivity
    minpiv = None
    for b in keep:
        piv = ldl_pivots(F, Y[b])
        vals = [F.to_complex(p, 60).real for p in piv]
        mv = min(vals)
        minpiv = mv if minpiv is None else min(minpiv, mv)
        if verbose:
            print(f"      block {b}: exact LDL pivots min {mp.nstr(mv, 8)}", flush=True)
        assert mv > 0, "not positive definite"
    cert = dict(d=d, N=N, keep=keep, Y=Y, kernels=kernels, lam=lam, bdata=bdata)
    with open(f"cert_povm_d{d}.pkl", "wb") as fh:
        pickle.dump(cert, fh)
    print(f"d={d}: CERTIFICATE OK (min LDL pivot {mp.nstr(minpiv, 6)}), total {time.time()-t0:.1f}s", flush=True)


def solve_exact(F, G, rhs, verbose=False):
    """Gaussian elimination on symmetric (possibly singular) system; returns z (None for dropped)."""
    m = len(G)
    A = [list(G[i]) + [rhs[i]] for i in range(m)]
    piv_of_row = {}
    used = [False] * m
    order = []
    t0 = time.time()
    for c in range(m):
        # choose pivot row among unused rows with nonzero in column c (prefer row c)
        p = None
        if not used[c] and not F.is_zero(A[c][c]):
            p = c
        else:
            for r in range(m):
                if not used[r] and not F.is_zero(A[r][c]):
                    p = r
                    break
        if p is None:
            continue
        used[p] = True
        order.append((p, c))
        inv = F.inv(A[p][c])
        rowp = [F.mul(x, inv) if not F.is_zero(x) else x for x in A[p]]
        A[p] = rowp
        nzp = [j for j in range(c, m + 1) if not F.is_zero(rowp[j])]
        for r in range(m):
            if r == p or F.is_zero(A[r][c]):
                continue
            f = A[r][c]
            rr = A[r]
            for j in nzp:
                rr[j] = F.sub(rr[j], F.mul(f, rowp[j]))
        if verbose and c % 50 == 0:
            print(f"      elim col {c}/{m} [{time.time()-t0:.1f}s]", flush=True)
    # consistency of unused rows
    for r in range(m):
        if not used[r]:
            assert all(F.is_zero(x) for x in A[r][:m]), "rank issue"
            assert F.is_zero(A[r][m]), "inconsistent system"
    z = [None] * m
    for (p, c) in order:
        z[c] = A[p][m]
    # free columns (not pivots) -> 0
    for c in range(m):
        if z[c] is None:
            z[c] = F.zero
    return z


def ldl_pivots(F, Y):
    k = len(Y)
    A = [list(r) for r in Y]
    piv = []
    for c in range(k):
        p = A[c][c]
        assert not F.is_zero(p), "zero pivot"
        piv.append(p)
        inv = F.inv(p)
        for r in range(c + 1, k):
            if F.is_zero(A[r][c]):
                continue
            f = F.mul(A[r][c], inv)
            for j in range(c + 1, k):
                if not F.is_zero(A[c][j]):
                    A[r][j] = F.sub(A[r][j], F.mul(f, A[c][j]))
    return piv


if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "mod":
        USE_MODULAR = True
        args = args[1:]
    for d in [int(t) for t in args]:
        main(d)
