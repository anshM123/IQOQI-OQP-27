"""
sdp_tracial.py -- certified upper bounds on the max-ent value of an arbitrary (2,2,d) Bell functional over all
projective strategies with UNIFORM marginals on maximally entangled states (any local dimension D, balanced PVMs;
in particular rank-one PVMs on Phi_d).

Model.  p(a,b|x,y) = tau(P^x_a Q^y_b), tau = normalised trace, P^x_a = (A^x_a)^T, Q^y_b = B^y_b (PVMs in M_D).
Unitaries R_g = sum_a w^a P^g_a (g = 0,1: Alice x; g = 2,3: Bob y), R_g^d = 1, w = exp(2 pi i/d).
   p(a,b|x,y) = d^-2 sum_{n,m} w^{-na-mb} tau(R_x^n R_{2+y}^m);  uniform marginals <=> tau(R_g^n) = 0 (n != 0).
Symmetry used (WLOG for maximising a linear functional): transposition R_g -> R_g^T keeps every P^x_a, Q^y_b
label (P^T = conj(P)) and the behaviour, and maps tau(w) -> tau(reversed w).  NOTE: entrywise conjugation is
NOT a symmetry (it negates outcome labels), so moments are complex.
Relaxation (level k): Hermitian moment matrix M[u,v] = y[cls(u^* v)], cls = class under cyclic rotation and
reversal; y(w^*) = conj(y(w)); M >= 0, y() = 1, y(R_g^n) = 0.

Certificate (dual, real variables t_r = Re/Im parts of the class moments, M = I + sum_r t_r F_r):
  Z >= 0 Hermitian with <Z,F_r> = -c_r  =>  beta <= c_() + tr Z.   Rigorous:
  UB = c_() + tr Z + sum_r |<Z,F_r> + c_r| + N (delta + eta),
where the residuals are exact (Fractions), |t_r| <= 1, and Z + (delta+eta) I >= 0 is certified by a floating
Cholesky L of the real embedding of Z + delta I with a rigorous bound eta >= ||Zr + delta I - L L^T||_F
(standard rounding-error bound gamma_n |L||L|^T plus the exactly-bounded computed residual).
"""
import math
from fractions import Fraction
import numpy as np
import scipy.sparse as sp


# ----------------------------------------------------------------------------- words
def reduce_word(w, d):
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


def dagger(w, d):
    return tuple((g, (-n) % d) for (g, n) in reversed(w))


def cyc_canon(w, d):
    w = list(reduce_word(w, d))
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        g = w[0][0]
        m = (w[0][1] + w[-1][1]) % d
        w = w[1:-1]
        if m:
            w = [(g, m)] + w
        w = list(reduce_word(tuple(w), d))
    w = tuple(w)
    if len(w) <= 1:
        return w
    return min(w[i:] + w[:i] for i in range(len(w)))


def cls(w, d):
    """class under cyclic rotation and reversal."""
    return min(cyc_canon(w, d), cyc_canon(tuple(reversed(w)), d))


def basis_words(d, level=2, extra=()):
    letters = [(g, n) for g in range(4) for n in range(1, d)]
    W = [()]
    W += [(l,) for l in letters]
    if level >= 2:
        for a in letters:
            for b in letters:
                if a[0] != b[0]:
                    W.append((a, b))
    for w in extra:
        if w not in W:
            W.append(w)
    return W


def wpow_exact(k, d):
    """w^k as (re, im) Fractions for d in {1,2,4}; None otherwise."""
    if d not in (1, 2, 4):
        return None
    k %= d
    e = (4 * k // d) % 4
    return [(1, 0), (0, 1), (-1, 0), (0, -1)][e]


# ----------------------------------------------------------------------------- functional -> moment objective
def objective_from_full(C, d):
    """C[x,y,a,b] (real) -> dict class -> complex coefficient h (Fraction pair for d in {2,4}, complex float
    otherwise) with  sum C p = Re sum_k h_k y_k  for every tracial moment functional with uniform marginals."""
    exact = d in (1, 2, 4)
    acc = {}
    for x in range(2):
        for y in range(2):
            for n in range(d):
                for m in range(d):
                    if exact:
                        re, im = Fraction(0), Fraction(0)
                        for a in range(d):
                            for b in range(d):
                                cr, ci = wpow_exact(-n * a - m * b, d)
                                re += Fraction(C[x, y, a, b]) * cr
                                im += Fraction(C[x, y, a, b]) * ci
                        h = (re / (d * d), im / (d * d))
                    else:
                        z = sum(C[x, y, a, b] * np.exp(2j * np.pi * (-n * a - m * b) / d)
                                for a in range(d) for b in range(d)) / d ** 2
                        h = (z.real, z.imag)
                    k = cls(reduce_word(((x, n), (2 + y, m)), d), d)
                    o = acc.get(k, (0, 0))
                    acc[k] = (o[0] + h[0], o[1] + h[1])
    return acc


# ----------------------------------------------------------------------------- SDP
class TracialSDP:
    def __init__(self, d, level=2, extra=(), marginal=True):
        self.d = d
        self.W = basis_words(d, level, extra)
        N = len(self.W)
        self.N = N
        self.keys = {}
        self.kidx = np.zeros((N, N), dtype=np.int64)
        for i, u in enumerate(self.W):
            ud = dagger(u, d)
            for j in range(N):
                k = cls(reduce_word(ud + self.W[j], d), d)
                if k not in self.keys:
                    self.keys[k] = len(self.keys)
                self.kidx[i, j] = self.keys[k]
        self.klist = [None] * len(self.keys)
        for k, v in self.keys.items():
            self.klist[v] = k
        # adjoint pairing of classes
        self.adj = np.zeros(len(self.keys), dtype=np.int64)
        for k, v in self.keys.items():
            ka = cls(dagger(k, d), d)
            if ka not in self.keys:
                self.keys[ka] = len(self.keys)
                self.klist.append(ka)
                self.adj = np.append(self.adj, 0)
            self.adj[v] = self.keys[ka]
        for k, v in list(self.keys.items()):
            self.adj[v] = self.keys[cls(dagger(k, d), d)]
        self.ident = self.keys[()]
        self.marg = {self.keys[k] for k in self.keys if len(k) == 1} if marginal else set()
        # real variables: for each adjoint pair {k, k*} with k <= k*: Re (and Im if k != k*)
        self.rvars = []      # list of (k, 're'|'im')
        self.rindex = {}
        for k in range(len(self.keys)):
            if k == self.ident or k in self.marg:
                continue
            ka = self.adj[k]
            if ka < k:
                continue
            self.rindex[(k, 're')] = len(self.rvars); self.rvars.append((k, 're'))
            if ka != k:
                self.rindex[(k, 'im')] = len(self.rvars); self.rvars.append((k, 'im'))

    def entry_terms(self, i, j):
        """M[i,j] = const + sum_r t_r * coef ; returns (const complex, list of (r, complex coef))."""
        k = self.kidx[i, j]
        if k == self.ident:
            return 1.0, []
        if k in self.marg:
            return 0.0, []
        ka = self.adj[k]
        if ka >= k:            # y_k = re + i im
            terms = [(self.rindex[(k, 're')], 1.0)]
            if ka != k:
                terms.append((self.rindex[(k, 'im')], 1j))
        else:                  # y_k = conj(y_ka) = re - i im
            terms = [(self.rindex[(ka, 're')], 1.0)]
            if ka != k:
                terms.append((self.rindex[(ka, 'im')], -1j))
        return 0.0, terms

    def objective_vector(self, hdict):
        """Re sum_k h_k y_k = c0 + sum_r c_r t_r (floats and exact Fractions when available)."""
        c = [0] * len(self.rvars)
        c0 = 0
        for k, (hr, hi) in hdict.items():
            if k not in self.keys:
                continue
            kk = self.keys[k]
            if kk == self.ident:
                c0 += hr
                continue
            if kk in self.marg:
                continue
            ka = self.adj[kk]
            if ka >= kk:   # y = re + i im ; Re(h y) = hr re - hi im
                c[self.rindex[(kk, 're')]] += hr
                if ka != kk:
                    c[self.rindex[(kk, 'im')]] += -hi
            else:          # y = re - i im (of ka)
                c[self.rindex[(ka, 're')]] += hr
                if ka != kk:
                    c[self.rindex[(ka, 'im')]] += hi
        return c0, c

    def solve(self, hdict, verbose=False, eps=1e-9, max_iters=200000, warm=None):
        """SCS (first-order; memory-light).  Real embedding [[X,-Y],[Y,X]] of M = X + iY, SCS svec format
        (lower triangle, column-major, off-diagonals scaled by sqrt2).  Returns (value, t, Zr, status)."""
        import scs
        N = self.N
        nv = len(self.rvars)
        c0, c = self.objective_vector(hdict)
        cvec = np.array([float(x) for x in c])
        N2 = 2 * N
        rows, cols, vals, b = [], [], [], []
        r = 0
        sq2 = math.sqrt(2.0)

        def emb(I, J):
            bi, i = divmod(I, N)
            bj, j = divmod(J, N)
            cst, terms = self.entry_terms(i, j)
            if bi == bj:
                return np.real(cst), [(t, np.real(cf)) for (t, cf) in terms]
            if bi == 1 and bj == 0:
                return np.imag(cst), [(t, np.imag(cf)) for (t, cf) in terms]
            return -np.imag(cst), [(t, -np.imag(cf)) for (t, cf) in terms]

        order = []
        for J in range(N2):
            for I in range(J, N2):
                sc = 1.0 if I == J else sq2
                cst, terms = emb(I, J)
                b.append(sc * cst)
                for (t, cf) in terms:
                    if cf != 0:
                        rows.append(r); cols.append(t); vals.append(-sc * cf)
                order.append((I, J))
                r += 1
        A = sp.csc_matrix((vals, (rows, cols)), shape=(r, nv))
        data = dict(A=A, b=np.array(b), c=-cvec)
        cone = dict(s=[N2])
        solver = scs.SCS(data, cone, verbose=verbose, eps_abs=eps, eps_rel=eps, max_iters=max_iters,
                         acceleration_lookback=20)
        if warm is not None:
            sol = solver.solve(warm_start=True, x=warm[0], y=warm[1], s=warm[2])
        else:
            sol = solver.solve()
        t = np.array(sol["x"])
        z = np.array(sol["y"])
        Zr = np.zeros((N2, N2))
        for q, (I, J) in enumerate(order):
            Zr[I, J] = Zr[J, I] = z[q] if I == J else z[q] / sq2
        value = float(c0) + float(cvec @ t)
        self.warm = (sol["x"], sol["y"], sol["s"])
        return value, t, Zr, sol["info"]["status"]

    # ------------------------------------------------------------------------- rigorous bound
    def certify(self, hdict, Zr, delta=1e-9):
        """rigorous UB from the real-embedded dual Zr (2N x 2N, symmetric)."""
        N = self.N
        N2 = 2 * N
        c0, c = self.objective_vector(hdict)
        c0 = Fraction(c0)
        c = [Fraction(x) for x in c]
        Zs = (Zr + Zr.T) / 2
        # <Zr, Emb(F_r)> exactly; Emb of entry coefficient cf at (i,j): Re cf at (i,j),(N+i,N+j); Im cf at
        # (N+i, j) and -Im cf at (i, N+j).
        Zf = {}
        acc = [Fraction(0)] * len(self.rvars)
        tr = Fraction(0)
        for i in range(N):
            for j in range(N):
                cst, terms = self.entry_terms(i, j)
                zre = Fraction(float(Zs[i, j])) + Fraction(float(Zs[N + i, N + j]))
                zim = Fraction(float(Zs[N + i, j])) - Fraction(float(Zs[i, N + j]))
                if cst != 0:
                    # constant entries: identity class on the diagonal only (value 1)
                    tr += zre * Fraction(np.real(cst)) + zim * Fraction(np.imag(cst))
                for (t, cf) in terms:
                    acc[t] += zre * Fraction(np.real(cf)) + zim * Fraction(np.imag(cf))
        resid = sum(abs(acc[t] + c[t]) for t in range(len(self.rvars)))
        # PSD certificate of Zs + (delta+eta) I
        A = Zs + delta * np.eye(N2)
        try:
            L = np.linalg.cholesky(A)
        except np.linalg.LinAlgError:
            return False, None, dict(reason="cholesky failed")
        u = 2.0 ** -53
        n = N2
        gam = (n + 2) * u / (1 - (n + 2) * u)
        absL = np.abs(L)
        E = A - L @ L.T
        # rigorous: ||A - L L^T||_F <= ||fl(E)||_F + gam (|A| + |L||L|^T)_F (componentwise bound, generous)
        bound = np.linalg.norm(E, 'fro') * (1 + 4 * u) + gam * (np.linalg.norm(np.abs(A), 'fro') +
                                                               np.linalg.norm(absL @ absL.T, 'fro')) * (1 + 4 * u)
        eta = float(bound) * 1.01 + 1e-300
        shift = Fraction(delta) + Fraction(eta)
        # Z_eff = Zs + shift I (real embedding) <=> complex Z + shift I ; adds shift * N (complex trace) ... the
        # complex trace of Z is (tr Zr)/2 when Zr is the embedding of Z; the pairing used above already used
        # zre = Z11 + Z22 (i.e. 2 Re Z for an exact embedding).  Shifting Zr by s I shifts zre on the diagonal by 2s.
        ub = c0 + tr + resid + 2 * shift * N
        return True, float(ub), dict(trace=float(tr), resid=float(resid), eta=eta, c0=float(c0))
