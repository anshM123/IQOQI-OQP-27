"""Q_RI_check/rc_core.py -- independent numerics for refereeing Q_RI/PROOF.md.

Written from scratch (does not import or copy Q_RI/ri_core.py).  Design choices that differ from the author's code:
  * instances are EXACT Gaussian-rational matrices (sympy), built in the eigenbasis of B (B diagonal); degenerate spectra
    are produced exactly with Cayley unitaries U = (1 - iK)(1 + iK)^{-1} (K Hermitian Gaussian-rational);
  * branch points of tau -> sum |Im y_i(tau)| are the real zeros of the EXACT y-discriminant of the exact polynomial
    p(y, tau) = det(H + c0 - y(B - tau)) in Q[y, tau], isolated exactly (sympy Poly.intervals on the square-free part)
    and then refined by bisection at 120 digits;
  * on each piece [ta, tb] between consecutive branch points tau = ta + (tb - ta) sin^2(theta), and the theta-integral
    is computed by Gauss-Legendre AND by tanh-sinh (mpmath), the difference being reported as an error estimate;
  * the general Hermitian B (b_1 < ... < b_n with multiplicities) is the basic object; a projection P of rank M - r is
    b = (0, 1), m = (r, M - r).

Notation as in Q_RI/PROOF.md: Y(tau, c) = (B - tau)^{-1}(H + c), roots y_i = eigenvalues of Y,
S_+ = sum of C_+ roots, Lam_+ = sum Log over C_+ roots, S0_+ = sum_{b_k > tau} (Tr Pi_k H Pi_k + m_k c)/(b_k - tau),
E(c) = Tr (H_d + c) Log(H_d + c) - Tr (H + c) Log(H + c),  L = (1/2pi) int sum |Im y_i| dtau,  R = Tr H_+ - Tr (H_d)_+.
"""
import random
import sympy as sp
import mpmath as mp
from sympy.polys.matrices import DomainMatrix

Ys, Ts, Cs = sp.symbols('y tau c')


# ============================================================ exact instances
def rat(rng, nr, den):
    return sp.Rational(rng.randint(-nr, nr), den)


def herm(rng, M, nr=9, den=4, offscale=1, diag=None):
    """random Hermitian Gaussian-rational M x M matrix."""
    H = sp.zeros(M, M)
    for i in range(M):
        H[i, i] = rat(rng, nr, den) if diag is None else sp.Rational(diag[i])
        for j in range(i + 1, M):
            z = (rat(rng, nr, den) + sp.I*rat(rng, nr, den))*offscale
            H[i, j] = z
            H[j, i] = sp.conjugate(z)
    return H


def qqi_inv(A):
    return DomainMatrix.from_Matrix(A).convert_to(sp.QQ_I).inv().to_Matrix()


def cayley(rng, M, nr=3, den=2):
    """exact unitary with Gaussian-rational entries: U = (1 - S)(1 + S)^{-1}, S = iK skew-Hermitian."""
    K = herm(rng, M, nr, den)
    S = (sp.I*K).applyfunc(sp.expand)
    U = ((sp.eye(M) - S)*qqi_inv((sp.eye(M) + S).applyfunc(sp.expand))).applyfunc(sp.expand)
    assert (U*U.H).applyfunc(sp.expand) == sp.eye(M)
    return U


def with_spectrum(rng, spec, nr=3, den=2):
    """exact Hermitian matrix U diag(spec) U^* (Gaussian rational) with prescribed (possibly repeated) spectrum."""
    M = len(spec)
    U = cayley(rng, M, nr, den)
    return (U*sp.diag(*[sp.Rational(s) for s in spec])*U.H).applyfunc(sp.expand)


class Inst:
    """H (sympy, exact) written in the eigenbasis of B = diag(b_1 1_{m_1}, ..., b_n 1_{m_n}), b_1 < ... < b_n."""

    def __init__(self, H, b, m, name=''):
        self.Hs = sp.Matrix(H)
        self.b = [sp.Rational(x) for x in b]
        self.m = list(m)
        self.n = len(b)
        self.M = self.Hs.shape[0]
        self.name = name
        assert sum(m) == self.M and all(self.b[i] < self.b[i + 1] for i in range(self.n - 1))
        assert (self.Hs - self.Hs.H).applyfunc(sp.expand) == sp.zeros(self.M, self.M)
        self.blocks = []
        s = 0
        for mk in self.m:
            self.blocks.append(list(range(s, s + mk)))
            s += mk
        self.bdiag = []
        for k, mk in enumerate(self.m):
            self.bdiag += [self.b[k]]*mk
        Hd = sp.zeros(self.M, self.M)
        for blk in self.blocks:
            for i in blk:
                for j in blk:
                    Hd[i, j] = self.Hs[i, j]
        self.Hds = Hd
        self._mp_dps = None

    @staticmethod
    def proj(H, r, name=''):
        """projection case: P of rank M - r, B = 1 - P of rank r  <->  b = (0, 1), m = (r, M - r)."""
        M = sp.Matrix(H).shape[0]
        return Inst(H, [0, 1], [r, M - r], name)

    # ------------------------------------------------ mp copies
    def mpready(self):
        if self._mp_dps == mp.mp.dps:
            return
        M = self.M
        def cv(z):
            re_, im_ = sp.expand(z).as_real_imag()
            re_, im_ = sp.Rational(re_), sp.Rational(im_)      # exact Gaussian rationals only (asserts)
            return mp.mpc(mp.mpf(re_.p)/re_.q, mp.mpf(im_.p)/im_.q)
        self.H = mp.matrix([[cv(self.Hs[i, j]) for j in range(M)] for i in range(M)])
        self.Hd = mp.matrix([[cv(self.Hds[i, j]) for j in range(M)] for i in range(M)])
        self.bmp = [mp.mpf(x.p)/x.q for x in self.b]
        self.lam = sorted(mp.re(e) for e in mp.eigh(self.H, eigvals_only=True))
        self.lam0 = sorted(mp.re(e) for e in mp.eigh(self.Hd, eigvals_only=True))
        self.blockspec = []
        self.blocktr = []
        for blk in self.blocks:
            sub = mp.matrix([[self.H[i, j] for j in blk] for i in blk])
            self.blockspec.append(sorted(mp.re(e) for e in mp.eigh(sub, eigvals_only=True)))
            self.blocktr.append(mp.re(sum((self.H[i, i] for i in blk), mp.mpf(0))))
        self.normH = max(abs(x) for x in self.lam)
        self._mp_dps = mp.mp.dps

    # ------------------------------------------------ exact pencil polynomial
    def pencil_poly(self, c0=0, csym=False):
        """exact p(y, tau) = det(H + c0 - y(B - tau)); a Poly in (y, tau) over QQ (real coefficients asserted).
        With csym=True, c is a symbol and the Poly is in (y, tau, c) over QQ_I."""
        M = self.M
        Bm = sp.diag(*self.bdiag)
        cc = Cs if csym else sp.Rational(c0)
        A = self.Hs + cc*sp.eye(M) - Ys*(Bm - Ts*sp.eye(M))
        gens = (Ys, Ts, Cs) if csym else (Ys, Ts)
        K = sp.QQ_I[gens]
        p = DomainMatrix.from_Matrix(A).convert_to(K).det()
        expr = K.to_sympy(p)
        P = sp.Poly(sp.expand(expr), *gens, domain='QQ_I')
        if csym:
            return P
        d = {}
        for mon, cf in P.terms():
            re_, im_ = sp.expand(cf).as_real_imag()
            assert re_.is_Rational and im_.is_Rational, cf
            assert im_ == 0, ('non-real coefficient', cf)
            d[mon] = re_
        return sp.Poly.from_dict(d, *gens, domain='QQ')

    def branch_points(self, c0=0, lo=None, hi=None, dps_ref=120, near_real=True):
        """real zeros in (lo, hi) of the y-discriminant of p(y, tau; c0) (exact isolation + bisection), and the real
        parts of complex zeros within 0.05 of (lo, hi) (used only as extra split points)."""
        lo = self.b[0] if lo is None else sp.Rational(lo)
        hi = self.b[-1] if hi is None else sp.Rational(hi)
        p = self.pencil_poly(c0)
        py = sp.Poly(p.as_expr(), Ys)
        D = sp.Poly(sp.discriminant(py), Ts, domain='QQ')
        self.disc_identically_zero = D.is_zero
        if D.is_zero:
            # every root is multiple for all tau (e.g. H = H1 (+) H1): use the square-free part of p in (y, tau)
            psq = sp.Poly(sp.sqf_part(p.as_expr()), Ys, Ts, domain='QQ')
            py = sp.Poly(psq.as_expr(), Ys)
            D = sp.Poly(sp.discriminant(py), Ts, domain='QQ')
            assert not D.is_zero
        Dsq = D.sqf_part()
        # remove exact zeros at the b_k (gap ends): those are not interior branch points
        for bk in self.b:
            while Dsq.eval(bk) == 0:
                Dsq = sp.Poly(sp.quo(Dsq.as_expr(), Ts - bk, Ts), Ts, domain='QQ')
        out = []
        if Dsq.degree() >= 1:
            for (a, bb), mult in Dsq.intervals():
                a, bb = sp.Rational(a), sp.Rational(bb)
                if bb < lo or a > hi:
                    continue
                # refine exactly until the interval is inside (lo, hi) or outside it
                while (a <= lo <= bb or a <= hi <= bb) and bb - a > sp.Rational(1, 10**40):
                    a, bb = Dsq.refine_root(a, bb, eps=(bb - a)/1000)
                    a, bb = sp.Rational(a), sp.Rational(bb)
                if bb <= lo or a >= hi:
                    continue
                out.append((a, bb))
        coeffs = [int(x) for x in sp.Poly(Dsq.as_expr()*sp.ilcm(1, 1, *[sp.fraction(c)[1] for c in Dsq.all_coeffs()]),
                                          Ts).all_coeffs()] if Dsq.degree() >= 1 else []
        pts = []
        with mp.workdps(dps_ref):
            f = lambda x: mp.polyval([mp.mpf(c) for c in coeffs], x)
            for (a, bb) in out:
                xa, xb = mp.mpf(a.p)/a.q, mp.mpf(bb.p)/bb.q
                fa = f(xa)
                for _ in range(int(3.4*dps_ref) + 20):
                    xm = (xa + xb)/2
                    fm = f(xm)
                    if fm == 0:
                        xa = xb = xm
                        break
                    if (fm > 0) == (fa > 0):
                        xa, fa = xm, fm
                    else:
                        xb = xm
                pts.append((xa + xb)/2)
        aux = []
        if near_real and Dsq.degree() >= 2:
            try:
                with mp.workdps(60):
                    rts = mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=3000, extraprec=600)
                for z in rts:
                    if 0 < abs(mp.im(z)) < 0.05 and float(lo) < mp.re(z) < float(hi):
                        aux.append(mp.re(z))
            except Exception as e:  # pragma: no cover
                print('   (polyroots for near-real zeros failed: %s)' % e)
        self.last_disc_degree = D.degree()
        return sorted(pts), sorted(aux)

    # ------------------------------------------------ pencil roots at (tau, c)
    def dvec_piece(self, ta, tb, th):
        """b_k - tau for tau = ta + (tb - ta) sin^2 th, computed without cancellation when ta or tb is a b_k."""
        s2, c2 = mp.sin(th)**2, mp.cos(th)**2
        w = tb - ta
        out = []
        for bk in self.bmp:
            if bk == ta:
                out.append(-w*s2)
            elif bk == tb:
                out.append(w*c2)
            else:
                out.append((bk - ta) - w*s2)
        return out, ta + w*s2

    def dvec(self, tau):
        return [bk - tau for bk in self.bmp]

    def Ymat(self, dv, c):
        M = self.M
        inv = []
        for k, mk in enumerate(self.m):
            inv += [1/dv[k]]*mk
        Y = mp.matrix(M, M)
        for i in range(M):
            for j in range(M):
                Y[i, j] = inv[i]*(self.H[i, j] + (c if i == j else 0))
        return Y

    def roots_dv(self, dv, c):
        self.mpready()
        dmin = min(abs(x) for x in dv)
        boost = int(max(0, -mp.log10(dmin))) + 10
        with mp.workdps(mp.mp.dps + boost):
            dv2 = [+x for x in dv]
            Y = self.Ymat(dv2, c)
            ev = mp.eig(Y, left=False, right=False) if self.M > 1 else [Y[0, 0]]
            return [+e for e in ev]

    def roots(self, tau, c):
        return self.roots_dv(self.dvec(tau), c)

    def split(self, dv, c):
        ys = self.roots_dv(dv, c)
        up = [z for z in ys if mp.im(z) > 0]
        dn = [z for z in ys if mp.im(z) < 0]
        return up, dn, ys

    def nplus(self, dv):
        return sum(mk for k, mk in enumerate(self.m) if dv[k] > 0)

    def S_plus(self, dv, c):
        up, dn, ys = self.split(dv, c)
        assert len(up) == self.nplus(dv), ('count', len(up), self.nplus(dv))
        return mp.fsum(up)

    def S_minus(self, dv, c):
        up, dn, ys = self.split(dv, c)
        return mp.fsum(dn)

    def Lam_plus(self, dv, c):
        up, dn, ys = self.split(dv, c)
        assert len(up) == self.nplus(dv)
        return mp.fsum(mp.log(z) for z in up)

    def S0_plus(self, dv, c):
        self.mpready()
        return mp.fsum((self.blocktr[k] + self.m[k]*c)/dv[k] for k in range(self.n) if dv[k] > 0)

    def S0_minus(self, dv, c):
        self.mpready()
        return mp.fsum((self.blocktr[k] + self.m[k]*c)/dv[k] for k in range(self.n) if dv[k] < 0)

    def Lam0_plus(self, dv, c):
        self.mpready()
        return mp.fsum(mp.log((mu + c)/dv[k]) for k in range(self.n) if dv[k] > 0 for mu in self.blockspec[k])

    # ------------------------------------------------ closed forms
    def E(self, c):
        self.mpready()
        zl = lambda z: z*mp.log(z) if z != 0 else mp.mpc(0)
        return mp.fsum(zl(l + c) for l in self.lam0) - mp.fsum(zl(l + c) for l in self.lam)

    def R(self, c0=0):
        self.mpready()
        return mp.fsum(max(l + c0, 0) for l in self.lam) - mp.fsum(max(l + c0, 0) for l in self.lam0)

    def Theta1(self, c):
        self.mpready()
        return mp.fsum(mp.log(l + c) for l in self.lam) - mp.fsum(mp.log(l + c) for l in self.lam0)

    # ------------------------------------------------ L(H + c0) by piecewise quadrature
    def imsum_piece(self, ta, tb, th, c0, k):
        if k == 0:
            return mp.mpf(0)
        dv, tau = self.dvec_piece(ta, tb, th)
        if min(abs(x) for x in dv) == 0:
            return mp.mpf(0)
        ys = self.roots_dv(dv, mp.mpf(c0))
        ims = sorted((abs(mp.im(z)) for z in ys), reverse=True)
        return mp.fsum(ims[:2*k])*(tb - ta)*mp.sin(2*th)

    def npairs_at(self, tau, c0):
        ys = self.roots(tau, mp.mpf(c0))
        scale = max(1, max(abs(z) for z in ys))
        tol = mp.mpf(10)**(-mp.mp.dps//3)*scale
        nc = sum(1 for z in ys if abs(mp.im(z)) > tol)
        assert nc % 2 == 0, ('odd number of non-real roots', nc)
        return nc//2

    def L(self, c0=0, verbose=False, gl_degree=7, ts_degree=7):
        """returns (L, error estimate, #branch points, pieces) for L(H + c0) = (1/2pi) sum_gaps int sum|Im y_i| dtau."""
        self.mpready()
        lo, hi = self.b[0], self.b[-1]
        pts, aux = self.branch_points(c0)
        cuts = sorted(set([mp.mpf(x.p)/x.q for x in self.b] + list(pts) + list(aux)))
        total_gl = mp.mpf(0)
        total_ts = mp.mpf(0)
        pieces = []
        for ta, tb in zip(cuts[:-1], cuts[1:]):
            k = self.npairs_at((ta + tb)/2, c0)
            pieces.append(k)
            if k == 0:
                continue
            f = lambda th: self.imsum_piece(ta, tb, th, c0, k)
            g = mp.quad(f, [0, mp.pi/2], method='gauss-legendre', maxdegree=gl_degree)
            t = mp.quad(f, [0, mp.pi/2], method='tanh-sinh', maxdegree=ts_degree)
            total_gl += g
            total_ts += t
        return total_gl/(2*mp.pi), abs(total_gl - total_ts)/(2*mp.pi), len(pts), pieces


# ============================================================ helpers
def fmt(x, n=22):
    return mp.nstr(x, n)


def logline(fh, s):
    print(s, flush=True)
    fh.write(s + '\n')
    fh.flush()
