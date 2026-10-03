# rf_core.py -- referee's OWN numerics for Q_2bmv/PROOF.md (nothing imported from Q_2bmv/ or Q_fresh/).
# Conventions exactly as in PROOF.md s.0:
#   D(a,t) = Tr e^{ag - tP} - e^{-t} Tr_P e^{aPgP} - Tr_B e^{aBgB}
#   F(s,tau) = (1/2pi) sum_i |Im x_i|,  x_i = roots of det(g - s - x(P - tau))  (= eig((P - tau)^{-1}(g - s)))
#   K_X(u) = sin(pi X)/(2(cosh(pi u) - cos(pi X))),  h_lam(x+iy) = -(1/pi^2) Im Li2(e^{pi(y-lam)} e^{-i pi x})
import numpy as np, mpmath as mp
from scipy.optimize import brentq
from scipy.integrate import quad_vec

PI = np.pi
GLX, GLW = np.polynomial.legendre.leggauss(40)
MAXSEG = 4000


def rand_unitary(M, rng):
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M))
    Q, R = np.linalg.qr(Z)
    return Q*(np.diag(R)/np.abs(np.diag(R)))


def rand_inst(M, r, scale, rng):
    U = rand_unitary(M, rng)
    B = U[:, :r] @ U[:, :r].conj().T
    B = (B + B.conj().T)/2
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M))
    g = (G + G.conj().T)/2*scale
    return B, g


def herm_from_params(p, M):          # decoding of the stored t03 configuration (data format of Q_fresh)
    Hm = np.zeros((M, M), complex)
    iu = np.triu_indices(M, 1); n = len(iu[0])
    Hm[np.diag_indices(M)] = p[:M]
    Hm[iu] = p[M:M+n] + 1j*p[M+n:M+2*n]
    return Hm + np.triu(Hm, 1).conj().T


def decode_t03(d, M=3):
    r = int(d[0]); gmax = d[1]; x = d[2:]
    Hm = herm_from_params(x[:M*M], M); w, V = np.linalg.eigh(Hm)
    U = (V*np.exp(1j*w)) @ V.conj().T
    B = U[:, :r] @ U[:, :r].conj().T
    g = herm_from_params(gmax*np.tanh(x[M*M:]), M)
    return (B + B.conj().T)/2, g, r


def compressions(B, g):
    """spec(BgB|ranB), spec(PgP|ranP)"""
    w, V = np.linalg.eigh(B)
    Qb = V[:, w > .5]; Qp = V[:, w <= .5]
    return np.linalg.eigvalsh(Qb.conj().T @ g @ Qb), np.linalg.eigvalsh(Qp.conj().T @ g @ Qp)


# ------------------------------------------------------------------ D(a,t) in high precision
def D_mp(B, g, a, t, dps=30):
    with mp.workdps(dps):
        M = B.shape[0]
        Bm = mp.matrix(B.tolist()); gm = mp.matrix(g.tolist()); Pm = mp.eye(M) - Bm
        a = mp.mpc(a); t = mp.mpc(t)
        X = a*gm - t*Pm
        tr = sum(mp.expm(X)[i, i] for i in range(M))
        bb, pp = compressions(B, g)
        # compressions in mp: use mp.eigh on exact compressions for accuracy
        w, V = np.linalg.eigh(B)
        Qb = mp.matrix(V[:, w > .5].tolist()); Qp = mp.matrix(V[:, w <= .5].tolist())
        Cb = Qb.H*gm*Qb; Cp = Qp.H*gm*Qp
        eb = mp.eighe(Cb, eigvals_only=True) if Cb.rows > 0 else []
        ep = mp.eighe(Cp, eigvals_only=True) if Cp.rows > 0 else []
        trB = sum(mp.exp(a*e) for e in eb); trP = sum(mp.exp(a*e) for e in ep)
        return tr - mp.exp(-t)*trP - trB


# ------------------------------------------------------------------ F(s,tau), vectorised in s
def F_vals(B, g, s, tau):
    M = B.shape[0]; P = np.eye(M) - B
    S = P/np.sqrt(1 - tau) + B/np.sqrt(tau)          # |P - tau|^{-1/2}
    Jm = P - B                                        # sgn(P - tau)
    SgS = S @ g @ S; S2 = S @ S
    A = Jm[None] @ (SgS[None] - np.asarray(s)[:, None, None]*S2[None])   # similar to (P-tau)^{-1}(g-s)
    ev = np.linalg.eigvals(A)
    im = np.abs(ev.imag)
    im[im < 1e-12*np.abs(ev).max(-1, keepdims=True)] = 0.0     # round-off of REAL roots (measured <= 1.3e-14 rel.)
    return im.sum(-1)/(2*PI)


def crit_values(B, g, tau, N=6000):
    """critical values of the eigenvalue curves x -> lambda_j(g - x(P - tau)) (x real): these are exactly the
    s where two real roots of p_{s,tau} merge (branch points of F).  Critical points obey |x| <= ||g-s||/sqrt(tau(1-tau))."""
    M = B.shape[0]; P = np.eye(M) - B
    ev = np.linalg.eigvalsh(g); lmin, lmax = ev[0], ev[-1]; W = lmax - lmin
    Xmax = 1.05*W/np.sqrt(tau*(1 - tau)) + 1e-12
    Xs = W/40
    U = np.arcsinh(Xmax/Xs)
    x = Xs*np.sinh(np.linspace(-U, U, N))
    Tm = tau*np.eye(M) - P

    def eig_at(xx):
        lam, V = np.linalg.eigh(g + xx*Tm)
        d = tau - np.einsum('ij,ik,kj->j', V.conj(), P, V).real
        return lam, d
    lam, V = np.linalg.eigh(g[None] + x[:, None, None]*Tm[None])
    d = tau - np.einsum('nij,ik,nkj->nj', V.conj(), P, V).real
    out = []
    for j in range(M):
        idx = np.nonzero(d[:-1, j]*d[1:, j] < 0)[0]
        for n in idx:
            try:
                xs = brentq(lambda xx: eig_at(xx)[1][j], x[n], x[n+1], xtol=1e-15*max(1, abs(x[n])), rtol=1e-15)
            except ValueError:
                continue
            out.append(eig_at(xs)[0][j])
    out = np.array(sorted(v for v in out if lmin < v < lmax))
    if len(out):
        keep = np.concatenate([[True], np.diff(out) > 1e-13*max(1, W)])
        out = out[keep]
    return out, lmin, lmax


def cos_nodes(sa, sb, n=None):
    """Gauss-Legendre in theta after s = sa + (sb - sa)(1 - cos th)/2: removes sqrt endpoint singularities"""
    X, Wt = (GLX, GLW) if n is None else np.polynomial.legendre.leggauss(n)
    th = (X + 1)*PI/2; wth = Wt*PI/2
    return sa + (sb - sa)*(1 - np.cos(th))/2, wth*(sb - sa)*np.sin(th)/2


def s_rule(B, g, tau, extra=(), n=None):
    """quadrature nodes/weights in s for the slice tau (all breakpoints of F plus optional extra points)"""
    cv, lmin, lmax = crit_values(B, g, tau)
    pts = np.unique(np.concatenate([[lmin], cv, [lmax], [e for e in extra if lmin < e < lmax]]))
    S = []; Wt = []
    for sa, sb in zip(pts[:-1], pts[1:]):
        s, w = cos_nodes(sa, sb, n)
        S.append(s); Wt.append(w)
    return np.concatenate(S), np.concatenate(Wt)


def J_slice(B, g, tau, avec):
    """J(a, tau) = int_R e^{a s} F(s,tau) ds for a vector of complex a (fixed Gauss; only for smooth cases)"""
    s, w = s_rule(B, g, tau)
    F = F_vals(B, g, s, tau)
    return np.exp(np.outer(avec, s)) @ (w*F)


# ---- vectorised adaptive Gauss-Kronrod (G7/K15) in theta, s = sa + (sb - sa)(1 - cos th)/2 on each breakpoint interval
_XK = np.array([-0.991455371120812639206854697526329, -0.949107912342758524526189684047851, -0.864864423359769072789712788640926,
                -0.741531185599394439863864773280788, -0.586087235467691130294144845693013, -0.405845151377397166906606412076961,
                -0.207784955007898467600689403773245, 0.0, 0.207784955007898467600689403773245, 0.405845151377397166906606412076961,
                0.586087235467691130294144845693013, 0.741531185599394439863864773280788, 0.864864423359769072789712788640926,
                0.949107912342758524526189684047851, 0.991455371120812639206854697526329])
_WK = np.array([0.022935322010529224963732008058970, 0.063092092629978553290700663189204, 0.104790010322250183839876322541518,
                0.140653259715525918745189590510238, 0.169004726639267902826583426598550, 0.190350578064785409913256402421014,
                0.204432940075298892414161999234649, 0.209482141084727828012999174891714, 0.204432940075298892414161999234649,
                0.190350578064785409913256402421014, 0.169004726639267902826583426598550, 0.140653259715525918745189590510238,
                0.104790010322250183839876322541518, 0.063092092629978553290700663189204, 0.022935322010529224963732008058970])
_WG = np.zeros(15)
_WG[1::2] = [0.129484966168869693270611432679082, 0.279705391489276667901467771423780, 0.381830050505118944950369775488975,
             0.417959183673469387755102040816327, 0.381830050505118944950369775488975, 0.279705391489276667901467771423780,
             0.129484966168869693270611432679082]


def adaptive_slice(B, g, tau, weight_fn, nw, extra=(), tol=1e-11, maxit=40, ninit=4, hmin=2e-7, offsets=False):
    """int_R weight_fn(s)[:, k] F(s,tau) ds, k = 0..nw-1, adaptively (absolute tol on the total; segments narrower
    than hmin (in theta) are accepted -- below that the double-precision eigenvalue round-off (~1e-11) dominates).
    offsets=True: weight_fn(s, sa, L, sn2) gets the exact representation s = sa + L*sn2 (for kernels peaked at a breakpoint)."""
    cv, lmin, lmax = crit_values(B, g, tau)
    pts = np.unique(np.concatenate([[lmin], cv, [lmax], [e for e in extra if lmin < e < lmax]]))
    segs = []
    for sa, sb in zip(pts[:-1], pts[1:]):
        th = np.linspace(0, PI, ninit + 1)
        for t0, t1 in zip(th[:-1], th[1:]):
            segs.append((sa, sb, t0, t1))
    segs = np.array(segs)
    total = np.zeros(nw, dtype=complex); nev = 0
    for it in range(maxit):
        if len(segs) == 0:
            break
        sa, sb, t0, t1 = segs.T
        c = (t0 + t1)/2; h = (t1 - t0)/2
        th = c[:, None] + h[:, None]*_XK[None]                              # (nseg, 15)
        sn2 = np.sin(th/2)**2
        Lm = np.broadcast_to((sb - sa)[:, None], th.shape); Sa = np.broadcast_to(sa[:, None], th.shape)
        s = Sa + Lm*sn2
        jac = Lm*np.sin(th)/2*h[:, None]
        F = F_vals(B, g, s.ravel(), tau).reshape(s.shape); nev += s.size
        if offsets:
            Wt = weight_fn(s.ravel(), Sa.ravel(), Lm.ravel(), sn2.ravel()).reshape(s.shape + (nw,))
        else:
            Wt = weight_fn(s.ravel()).reshape(s.shape + (nw,))              # (nseg, 15, nw)
        f = (F*jac)[..., None]*Wt
        IK = np.einsum('k,skw->sw', _WK, f); IG = np.einsum('k,skw->sw', _WG, f)
        err = np.max(np.abs(IK - IG), axis=1)
        L1 = np.max(np.einsum('k,skw->sw', _WK, np.abs(f)), axis=1)      # per-segment L1 size of the integrand
        frac = h/PI                                                           # share of tolerance (per breakpoint interval)
        ok = (err <= tol*frac) | (err <= 1e-11*L1) | (h < hmin)
        total += IK[ok].sum(0)
        bad = segs[~ok]
        if len(bad) == 0:
            segs = bad; break
        if len(bad) > MAXSEG:                     # memory guard (keeps jobs far below 1.2 GB); reported via 3rd output
            total += IK[~ok].sum(0)
            return total, nev, -len(bad)
        mid = (bad[:, 2] + bad[:, 3])/2
        segs = np.concatenate([np.column_stack([bad[:, 0], bad[:, 1], bad[:, 2], mid]),
                               np.column_stack([bad[:, 0], bad[:, 1], mid, bad[:, 3]])])
    return total, nev, len(segs)


# ------------------------------------------------------------------ strip functions
def K_strip(X, u):
    """K_X(u) = sin(pi X)/(2(cosh(pi u) - cos(pi X))) = sin(pi X) q/((1-q)^2 + 4 q sin^2(pi X/2)), q = e^{-pi|u|}
    (overflow-free and free of the 1 - cos cancellation at small X, u)"""
    a = PI*np.abs(u); q = np.exp(-a)
    return np.sin(PI*X)*q/(np.expm1(-a)**2 + 4*q*np.sin(PI*X/2)**2)


TAU_LO, TAU_HI = 1e-13, 1 - 1e-11


def V_lams(B, g, lams, epsrel=1e-11, epsabs=1e-12, stats=None):
    """V(lam) = int_0^1 int_R K_{1-tau}(s - lam) F(s,tau) ds dtau for an array of lam.
    tau = sin^2(phi) (removes the (1-tau)^{-1/2} behaviour of the slices when lam is near spec(PgP));
    tau restricted to [TAU_LO, TAU_HI]: the omitted pieces are <= ||BgP||^2 (pi/8) TAU_LO^2 and
    <= ||BgP||^2 (1-TAU_HI)^2/(2 pi d^2) (d = distance of lam from the s-support of F near tau = 1), negligible here."""
    lams = np.asarray(lams, float); n = len(lams)
    if stats is None: stats = {}
    stats.setdefault('capped', 0)

    def wfun(X):
        def w(s, sa, L, sn2):
            u = (sa[:, None] - lams[None, :]) + (L*sn2)[:, None]
            return K_strip(X, u)
        return w

    def integrand(phi):
        tau = np.sin(phi)**2; X = np.cos(phi)**2
        extra = list(lams)
        for lam in lams:
            for k in range(40):
                d = X*4.0**k
                if d > 400: break
                extra += [lam - d, lam + d]
        tot, _, left = adaptive_slice(B, g, tau, wfun(X), n, extra=extra, tol=1e-12, offsets=True)
        if left < 0: stats['capped'] += 1
        return tot.real*np.sin(2*phi)
    p0, p1 = np.arcsin(np.sqrt(TAU_LO)), np.arccos(np.sqrt(1 - TAU_HI))
    res, err, info = quad_vec(integrand, p0, p1, epsabs=epsabs, epsrel=epsrel, limit=4000, quadrature='gk21',
                              norm='max', full_output=True)
    return res, err, info.neval


def h_mp(nu, lam, dps=30):
    """h_lam(x+iy) = -(1/pi^2) Im Li2(e^{pi(y-lam)} e^{-i pi x}), 0 < x < 1; inversion for |z| > 1:
       Im Li2(z) = -Im Li2(1/z) - pi^2 (y - lam)(1 - x)"""
    with mp.workdps(dps):
        x = mp.mpf(nu.real); y = mp.mpf(nu.imag); lam = mp.mpf(lam)
        if y <= lam:
            z = mp.exp(mp.pi*(y - lam))*mp.expj(-mp.pi*x)
            return -mp.im(mp.polylog(2, z))/mp.pi**2
        zi = mp.exp(-mp.pi*(y - lam))*mp.expj(mp.pi*x)
        return mp.im(mp.polylog(2, zi))/mp.pi**2 + (y - lam)*(1 - x)


def defect_mp(B, g, lam, dps=30):
    """sum_{nu in spec(B+ig)} h_lam(nu) - Tr[(P(g-lam)P)_+]  (eigenvalues of B + ig in mp precision)"""
    with mp.workdps(dps + 10):
        X = mp.matrix((B + 1j*g).tolist())
        nus = mp.eig(X, left=False, right=False)
        tot = mp.mpf(0)
        for nu in nus:
            tot += h_mp_mpc(nu, lam, dps)
        w, V = np.linalg.eigh(B)
        Qp = mp.matrix(V[:, w <= .5].tolist()); gm = mp.matrix(g.tolist())
        ep = mp.eighe(Qp.H*gm*Qp, eigvals_only=True)
        rhs = sum(max(e - lam, 0) for e in ep)
        return tot - rhs, nus


def h_mp_mpc(nu, lam, dps):
    x = mp.re(nu); y = mp.im(nu); lam = mp.mpf(lam)
    if y <= lam:
        z = mp.exp(mp.pi*(y - lam))*mp.expj(-mp.pi*x)
        return -mp.im(mp.polylog(2, z))/mp.pi**2
    zi = mp.exp(-mp.pi*(y - lam))*mp.expj(mp.pi*x)
    return mp.im(mp.polylog(2, zi))/mp.pi**2 + (y - lam)*(1 - x)
