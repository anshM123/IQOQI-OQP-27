"""rc04b: Remark 3.3 (a) complex Jensen formula, (c) Frullani identity, (d) the real 1D formula -- with a robust integrator
(rc04 section (4) used a naive infinite-interval quadrature, which is inaccurate here because the integrands decay only like
log|x|/x^2; its section-(4) numbers are superseded by this file).
Integrator: [-1, 1] split at kinks; |x| > 1 via x = +-e^v, v in [0, 60] split at the images of the kinks; tanh-sinh; the
eigenvalues at large |x| are computed with working precision 30 + 2 log10(1 + |x|) (cancellation in Om(x + ..) differences)."""
import random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline, Ys

mp.mp.dps = 30
out = open('rc04b_remark33.log', 'w')
rng = random.Random(9001)
insts = [Inst.proj(herm(rng, 3), 1, 'rand_M3_r1'), Inst.proj(herm(rng, 4), 2, 'rand_M4_r2'),
         Inst.proj(herm(rng, 5), 2, 'rand_M5_r2')]       # same instances as rc04 (same seed and order)


def eigh_vals(A):
    return [mp.re(e) for e in mp.eigh(A, eigvals_only=True)]


def integrate_R(f, kinks=(), V=60):
    """int_R f(x) dx; f(x) is evaluated with x given as an mpf at the current precision."""
    ks = sorted(set(mp.mpf(k) for k in kinks))
    inner = sorted(set([mp.mpf(-1), mp.mpf(0), mp.mpf(1)] + [k for k in ks if -1 < k < 1]))
    tot = mp.quad(f, inner)
    for sgn in (1, -1):
        vk = sorted(set([mp.mpf(0), mp.mpf(V)] + [mp.log(abs(k)) for k in ks if sgn*k > 1 and mp.log(abs(k)) < V]
                        + [mp.mpf(x) for x in (1, 2, 4, 8, 16, 32) if x < V]))
        g = lambda v: f(sgn*mp.exp(v))*mp.exp(v)
        tot += mp.quad(g, vk)
    return tot


def local_dps(x):
    return mp.mp.dps + int(2*mp.log10(1 + abs(x))) + 5


def Om(z):
    return z*mp.log(z) - z


def Lam(t):
    return t*mp.log(abs(t)) - t if t != 0 else mp.mpf(0)


logline(out, 'Remark 3.3 (dps 30 + adaptive): (a) S_+ - S0_+ = (i/2pi) int_R ell dx ; (c) (i/2pi) int (Phi_B - Phi_P) dx/x = E(c) ; '
             '(d) int_R dx/x [Tr Lam(H+c0+xB) - Tr Lam(H_d+c0+xB) - Tr Lam(H+c0-xP) + Tr Lam(H_d+c0-xP)] = 2 pi^2 R(H + c0)')
for I in insts:
    I.mpready()
    M, r = I.M, I.m[0]
    Hm, Hdm = I.H, I.Hd
    Pm = mp.diag([0]*r + [1]*(M - r))
    Bm = mp.eye(M) - Pm
    c = mp.mpc('0.3', '0.9')
    tau = mp.mpf('0.37')

    def ell(x):
        with mp.workdps(local_dps(x)):
            A = mp.matrix(M, M)
            for i in range(M):
                A[i, i] = -x*((1 if i >= r else 0) - tau)
            nu = eigh_vals(Hm + A)
            nu0 = eigh_vals(Hdm + A)
            v = mp.fsum(mp.log(t + c) for t in nu) - mp.fsum(mp.log(t + c) for t in nu0)
        return +v

    lhs = I.S_plus(I.dvec(tau), c) - I.S0_plus(I.dvec(tau), c)
    rhs = 1j/(2*mp.pi)*integrate_R(ell)
    logline(out, '  %-12s (a) S_+ - S0_+ = %s ; |difference| = %s' % (I.name, mp.nstr(lhs, 15), mp.nstr(abs(lhs - rhs), 3)))

    def dPhi(x):
        with mp.workdps(local_dps(x)):
            pb = mp.fsum(Om(e + c) for e in eigh_vals(Hm + x*Bm)) - mp.fsum(Om(e + c) for e in eigh_vals(Hdm + x*Bm))
            pp = mp.fsum(Om(e + c) for e in eigh_vals(Hm - x*Pm)) - mp.fsum(Om(e + c) for e in eigh_vals(Hdm - x*Pm))
            v = (pb - pp)/x if x != 0 else mp.mpc(0)
        return +v

    val = 1j/(2*mp.pi)*integrate_R(dPhi)
    logline(out, '  %-12s (c) E(c) = %s ; |(i/2pi) int - E| = %s' % (I.name, mp.nstr(I.E(c), 15), mp.nstr(abs(val - I.E(c)), 3)))

    for c0r in [sp.Rational(0), sp.Rational(7, 10)]:
        c0 = mp.mpf(c0r.p)/c0r.q
        kinks = []
        for (A0, sgn, Q) in [(I.Hs, 1, 'B'), (I.Hds, 1, 'B'), (I.Hs, -1, 'P'), (I.Hds, -1, 'P')]:
            Qm = sp.diag(*([1]*r + [0]*(M - r))) if Q == 'B' else sp.diag(*([0]*r + [1]*(M - r)))
            pol = sp.Poly(sp.expand((A0 + c0r*sp.eye(M) + sgn*Ys*Qm).det(method='berkowitz')), Ys)
            if pol.degree() >= 1:
                cfs = [mp.mpf(sp.Rational(sp.re(x)).p)/sp.Rational(sp.re(x)).q for x in pol.all_coeffs()]
                for z in mp.polyroots(cfs, maxsteps=500, extraprec=300):
                    if abs(mp.im(z)) < mp.mpf(10)**(-20):
                        kinks.append(mp.re(z))

        def gd(x):
            with mp.workdps(local_dps(x)):
                a1 = mp.fsum(Lam(e + c0) for e in eigh_vals(Hm + x*Bm)) - mp.fsum(Lam(e + c0) for e in eigh_vals(Hdm + x*Bm))
                a2 = mp.fsum(Lam(e + c0) for e in eigh_vals(Hm - x*Pm)) - mp.fsum(Lam(e + c0) for e in eigh_vals(Hdm - x*Pm))
                v = (a1 - a2)/x if x != 0 else mp.mpf(0)
            return +v

        J = integrate_R(gd, kinks)
        target = 2*mp.pi**2*I.R(c0)
        logline(out, '  %-12s (d) c0=%-4s int = %s  2 pi^2 R(H + c0) = %s  |diff| = %s (#kinks %d)' % (
            I.name, str(c0r), mp.nstr(J, 20), mp.nstr(target, 20), mp.nstr(abs(J - target), 3), len(kinks)))
out.close()
