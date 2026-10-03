"""rc06b: end-to-end check of s.4 (Theorem 1 of Q_2bmv) and s.4.1 (Theorem 3 / BMV corollary) by DIRECT 2D integration of
F(s, tau) = (1/2pi) sum |Im x_i(s, tau)| (x_i the eigenvalues of (B - tau)^{-1}(g - s)) -- not via the Radon slices.
Splitting: in s at the real zeros of the exact x-discriminant D(s, tau) (for each tau node), in tau at the b_k and at the real
zeros of disc_s(D) (tau where two s-branch points collide); sin^2 substitution on every piece; Gauss-Legendre; numpy double
precision for the inner eigenvalues.  Reference: D(a,t)/a^2 with mpmath expm (dps 30).  Expected accuracy ~1e-9..1e-12."""
import random, time
import numpy as np
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, logline, Ys, Ts, Cs

out = open('rc06b_thm1_2d.log', 'w')
rng = random.Random(55)


def setup(I):
    I.mpready()
    p = I.pencil_poly(csym=True)                         # det(H + c - y(B - tau)) ; c = -s
    py = sp.Poly(p.as_expr(), Ys)
    D = sp.expand(sp.discriminant(py))
    Dp = sp.Poly(D, Ts, Cs, domain='QQ_I')
    d = {}
    for mon, cf in Dp.terms():
        re_, im_ = sp.expand(cf).as_real_imag()
        assert im_ == 0
        d[mon] = re_
    Dr = sp.Poly.from_dict(d, Ts, Cs, domain='QQ')
    Dc = sp.Poly(Dr.as_expr(), Cs)                       # coefficients in Q[tau]
    coeff_polys = [sp.Poly(cf, Ts) for cf in Dc.all_coeffs()]
    # tau where two s-branch points collide: zeros of disc_c(D) and of the leading coefficient
    DD = sp.Poly(sp.discriminant(sp.Poly(Dr.as_expr(), Cs)), Ts, domain='QQ')
    lead = coeff_polys[0]
    tcuts = set(float(b) for b in I.b)
    for pol in [DD, lead]:
        pol = pol.sqf_part()
        if pol.degree() >= 1:
            for (a_, b_), mult in pol.intervals(eps=sp.Rational(1, 10**14)):
                x = float((a_ + b_)/2)
                if float(I.b[0]) < x < float(I.b[-1]):
                    tcuts.add(x)
    I.coeff_polys = [np.array([float(c) for c in cp.all_coeffs()]) for cp in coeff_polys]
    I.coeff_exact = [[(sp.Rational(c).p, sp.Rational(c).q) for c in cp.all_coeffs()] for cp in coeff_polys]
    I.tcuts = sorted(tcuts)
    I.Hnp = np.array([[complex(I.H[i, j]) for j in range(I.M)] for i in range(I.M)])
    I.bd = np.array([float(x) for x in I.bdiag])
    ev = np.linalg.eigvalsh(I.Hnp)
    I.lmin, I.lmax = ev[0], ev[-1]


def F_vec(I, s, tau):
    """F(s, tau) for an array s."""
    inv = 1.0/(I.bd - tau)
    A = (I.Hnp[None, :, :] - s[:, None, None]*np.eye(I.M)[None, :, :])*inv[None, :, None]
    ev = np.linalg.eigvals(A)
    return np.abs(ev.imag).sum(axis=1)/(2*np.pi)


def s_branch(I, tau):
    # exact rational coefficient polynomials evaluated at tau with 40 digits; roots by mpmath polyroots; s = -c
    with mp.workdps(40):
        t = mp.mpf(tau)
        cf = [mp.polyval([mp.mpf(p)/q for (p, q) in cpe], t) for cpe in I.coeff_exact]
        mx = max(abs(x) for x in cf)
        k = 0
        while k < len(cf) - 1 and abs(cf[k]) < mp.mpf(10)**(-30)*mx:
            k += 1
        if len(cf) - k <= 1:
            return []
        rts = mp.polyroots(cf[k:], maxsteps=400, extraprec=200, error=False)
        ss = sorted(float(-mp.re(z)) for z in rts if abs(mp.im(z)) < mp.mpf(10)**(-15)*(1 + abs(z))
                    and I.lmin < -mp.re(z) < I.lmax)
        # near-real complex branch points (sharp interior features of F(., tau)): extra split points
        for z in rts:
            e = float(abs(mp.im(z)))
            x0 = float(-mp.re(z))
            if 1e-15*(1 + abs(x0)) <= e < 0.3 and I.lmin < x0 < I.lmax:
                for k in (0, -1, 1, -3, 3, -10, 10, -30, 30):
                    if I.lmin < x0 + k*e < I.lmax:
                        ss.append(x0 + k*e)
    return sorted(set(ss))


def inner(I, tau, a, ns):
    """J(a, tau) = int_R e^{a s} F(s, tau) ds, complex a."""
    cuts = [I.lmin] + s_branch(I, tau) + [I.lmax]
    x, w = np.polynomial.legendre.leggauss(ns)
    phi = (x + 1)*np.pi/4                                   # phi in (0, pi/2)
    wphi = w*np.pi/4
    tot = 0j
    for sa, sb in zip(cuts[:-1], cuts[1:]):
        if sb - sa < 1e-15:
            continue
        mid = np.array([(sa + sb)/2])
        if F_vec(I, mid, tau)[0] < 1e-13:
            continue
        s = sa + (sb - sa)*np.sin(phi)**2
        jac = (sb - sa)*np.sin(2*phi)
        tot += np.sum(wphi*jac*np.exp(a*s)*F_vec(I, s, tau))
    return tot


def I2d(I, a, t, nt, ns):
    x, w = np.polynomial.legendre.leggauss(nt)
    th = (x + 1)*np.pi/4
    wth = w*np.pi/4
    tot = 0j
    for ta, tb in zip(I.tcuts[:-1], I.tcuts[1:]):
        tau = ta + (tb - ta)*np.sin(th)**2
        jac = (tb - ta)*np.sin(2*th)
        for k in range(nt):
            tot += wth[k]*jac[k]*np.exp(-t*tau[k])*inner(I, tau[k], a, ns)
    return tot


def Dref(I, a, t):
    mp.mp.dps = 30
    a = mp.mpc(a); t = mp.mpc(t)
    M = I.M
    Bm = mp.diag([mp.mpf(x.p)/x.q for x in I.bdiag])
    val = mp.re(0) + mp.mpc(0)
    val += sum(mp.expm(a*I.H - t*Bm)[i, i] for i in range(M))
    for k, blk in enumerate(I.blocks):
        sub = mp.matrix([[I.H[i, j] for j in blk] for i in blk])
        val -= mp.exp(-t*I.bmp[k])*sum(mp.expm(a*sub)[i, i] for i in range(len(blk)))
    return complex(val/a**2)


cases = [Inst.proj(herm(rng, 3), 1, 'proj_M3_r1'), Inst.proj(herm(rng, 4), 2, 'proj_M4_r2'),
         Inst(herm(rng, 3), [0, sp.Rational(1, 2), 1], [1, 1, 1], 'generalB_b=(0,1/2,1)')]
pts = [(0.8 + 0.6j, 0.3 - 1.1j), (-0.5 + 1.2j, 2.0 + 0.5j), (0.9, 0.9j), (0.9, -0.9j), (1.0, 0.7), (-1.3, -2.0)]
logline(out, 'Theorem 1 (projection) / Theorem 3 (general B): D(a,t)/a^2 vs direct 2D integral of e^{as - t tau} F')
for I in cases:
    t0 = time.time()
    setup(I)
    logline(out, '  %s: tau cut points %s' % (I.name, ['%.6f' % x for x in I.tcuts]))
    for (a, t) in pts:
        ref = Dref(I, a, t)
        v1 = I2d(I, a, t, 50, 40)
        v2 = I2d(I, a, t, 100, 80)
        logline(out, '    (a,t)=(%s, %s): D/a^2 = %.14g%+.14gj  2D = %.14g%+.14gj  |diff| = %.2e  (2D self-consistency %.1e)' % (
            a, t, ref.real, ref.imag, v2.real, v2.imag, abs(v2 - ref), abs(v2 - v1)))
    logline(out, '    (%.0fs)' % (time.time() - t0))
out.close()
