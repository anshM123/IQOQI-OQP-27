"""
ipm.py -- small primal-dual interior-point SDP solver (HKM direction, Mehrotra predictor-corrector)
for block-diagonal complex-Hermitian problems in "moment form":

    minimise  c.y + const   s.t.   M(y) = M0 + sum_j y_j M_j  >= 0     (y real)

Dual ("SOS form"):  maximise const - <M0, X>  s.t.  <M_j, X> = c_j ,  X >= 0.
Works in numpy (double) or with a generic backend for extended precision (mpmath) -- see ipm_mp.py.
Blocks are given as lists of dense complex matrices: M0[b] (n_b x n_b), Mj[b] = list over j (sparse dict).
"""
import numpy as np


def herm(A):
    return (A + A.conj().T) / 2


def from_sdp(sdp):
    """convert an ncwords.SDP (entry lists) into dense block matrices."""
    M0, Ms = [], []
    for (n, ent) in sdp.blocks:
        B0 = np.zeros((n, n), complex)
        Bj = {}
        for (i, j), lst in ent.items():
            for (c, v) in lst:
                if v < 0:
                    B0[i, j] += c
                    if i != j:
                        B0[j, i] += np.conj(c)
                else:
                    if v not in Bj:
                        Bj[v] = np.zeros((n, n), complex)
                    Bj[v][i, j] += c
                    if i != j:
                        Bj[v][j, i] += np.conj(c)
        M0.append(herm(B0))
        Ms.append({v: herm(B) for v, B in Bj.items()})
    return M0, Ms


def solve(M0, Ms, c, const=0.0, tol=1e-12, maxit=100, verbose=False):
    nb = len(M0)
    m = len(c)
    # SDP in standard form: max b.y s.t. C - sum y_j A_j = Z >= 0 ; primal min <C,X> s.t. <A_j,X> = b_j
    C = [M0[b] for b in range(nb)]
    A = [{j: -Ms[b][j] for j in Ms[b]} for b in range(nb)]
    bvec = -np.asarray(c, float)
    # initial point
    X = [np.eye(C[b].shape[0], dtype=complex) for b in range(nb)]
    y = np.zeros(m)
    Z = [np.eye(C[b].shape[0], dtype=complex) * max(1.0, np.abs(C[b]).max() * 10) for b in range(nb)]
    # scale X for feasibility guess
    def Aop(Xs):
        r = np.zeros(m)
        for b in range(nb):
            for j, Aj in A[b].items():
                r[j] += np.real(np.vdot(Aj, Xs[b]))   # <Aj, X> = tr(Aj^H X) = tr(Aj X)
        return r

    def ATop(yv):
        out = []
        for b in range(nb):
            S = np.zeros_like(C[b])
            for j, Aj in A[b].items():
                S = S + yv[j] * Aj
            out.append(S)
        return out
    ntot = sum(C[b].shape[0] for b in range(nb))
    best = None
    worse = 0
    for it in range(maxit):
        ATy = ATop(y)
        Rp = bvec - Aop(X)                                  # primal residual
        Rd = [C[b] - ATy[b] - Z[b] for b in range(nb)]      # dual residual
        mu = sum(np.real(np.vdot(X[b], Z[b])) for b in range(nb)) / ntot
        pobj = sum(np.real(np.vdot(C[b], X[b])) for b in range(nb))
        dobj = bvec @ y
        rp = np.linalg.norm(Rp) / (1 + np.linalg.norm(bvec))
        rd = max(np.abs(R).max() for R in Rd) / (1 + max(np.abs(Cb).max() for Cb in C))
        gap = abs(pobj - dobj) / (1 + abs(pobj) + abs(dobj))
        if verbose:
            print(f"it {it:3d} pobj {pobj:.12e} dobj {dobj:.12e} rp {rp:.1e} rd {rd:.1e} gap {gap:.1e} mu {mu:.1e}")
        err = max(rp, rd, gap)
        if best is None or err < best[0]:
            best = (err, [x.copy() for x in X], y.copy(), [z.copy() for z in Z], it, rp, rd, gap, pobj, dobj)
            worse = 0
        else:
            worse += 1
        if (rp < tol and rd < tol and gap < tol) or worse >= 3:
            break
        Zinv = [np.linalg.inv(Z[b]) for b in range(nb)]
        # Schur complement H_ij = Re tr(A_i X A_j Zinv)
        H = np.zeros((m, m))
        for b in range(nb):
            js = list(A[b].keys())
            if not js:
                continue
            XA = {j: X[b] @ A[b][j] @ Zinv[b] for j in js}
            for i in js:
                Ai = A[b][i]
                for j in js:
                    H[i, j] += np.real(np.sum(Ai.T * XA[j]))   # tr(Ai @ XA_j)
        H = (H + H.T) / 2
        try:
            Lc = np.linalg.cholesky(H + 1e-15 * np.eye(m) * max(1, np.abs(H).max()))
            solveH = lambda r: np.linalg.solve(Lc.T.conj(), np.linalg.solve(Lc, r))
        except np.linalg.LinAlgError:
            Hp = np.linalg.pinv(H)
            solveH = lambda r: Hp @ r

        def direction(sigma_mu, corr=None):
            # solve for (dX, dy, dZ):  A(dX) = Rp ; A^T dy + dZ = Rd ; HKM: dX = sigma mu Zinv - X - X dZ Zinv (sym)
            Rc = []
            for b in range(nb):
                R = sigma_mu * Zinv[b] - X[b]
                if corr is not None:
                    R = R - corr[b] @ Zinv[b]
                Rc.append(R)
            # dX = Rc - X dZ Zinv, dZ = Rd - A^T dy
            # A(dX) = A(Rc) - A(X (Rd - A^T dy) Zinv) = Rp  =>  H dy = Rp - A(Rc) + A(X Rd Zinv)
            XRZ = [X[b] @ Rd[b] @ Zinv[b] for b in range(nb)]
            rhs = Rp - Aop([herm(Rc[b]) for b in range(nb)]) + Aop([herm(XRZ[b]) for b in range(nb)])
            dy = solveH(rhs)
            ATdy = ATop(dy)
            dZ = [Rd[b] - ATdy[b] for b in range(nb)]
            dX = [herm(Rc[b] - X[b] @ dZ[b] @ Zinv[b]) for b in range(nb)]
            return dX, dy, dZ

        def maxstep(M, dM):
            a = 1.0
            for b in range(nb):
                L = np.linalg.cholesky(herm(M[b]))
                Li = np.linalg.inv(L)
                ev = np.linalg.eigvalsh(herm(Li @ dM[b] @ Li.conj().T))
                if ev.min() < 0:
                    a = min(a, -1.0 / ev.min())
            return a
        # predictor
        dX, dy, dZ = direction(0.0)
        try:
            ap = min(1.0, 0.98 * maxstep(X, dX))
            ad = min(1.0, 0.98 * maxstep(Z, dZ))
        except np.linalg.LinAlgError:
            break
        mu_aff = sum(np.real(np.vdot(X[b] + ap * dX[b], Z[b] + ad * dZ[b])) for b in range(nb)) / ntot
        sigma = min(1.0, (mu_aff / mu) ** 3)
        corr = [dX[b] @ dZ[b] for b in range(nb)]
        dX, dy, dZ = direction(sigma * mu, corr)
        try:
            ap = min(1.0, 0.98 * maxstep(X, dX))
            ad = min(1.0, 0.98 * maxstep(Z, dZ))
        except np.linalg.LinAlgError:
            break
        X = [herm(X[b] + ap * dX[b]) for b in range(nb)]
        y = y + ad * dy
        Z = [herm(Z[b] + ad * dZ[b]) for b in range(nb)]
    err, X, y, Z, it, rp, rd, gap, pobj, dobj = best
    # moment problem: min c.y + const = -(b.y) + const
    return {"obj": const - dobj, "pobj_bound": const - pobj, "y": y, "X": X, "Z": Z, "it": it,
            "rp": rp, "rd": rd, "gap": gap}
