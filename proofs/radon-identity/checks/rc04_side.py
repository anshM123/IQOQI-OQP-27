"""rc04: Proposition 2.1 (kappa = 0), Corollary 2.2 (E = Stieltjes transform of R(H + t)), Remark 3.2 (M = 2 closed form and
the substitution rho), Remark 3.3 (a) complex Jensen formula, (c) Frullani identity, (d) the real one-dimensional formula.
Section (4) is SUPERSEDED by rc04b_remark33.py (its naive infinite-interval quadrature is inaccurate for log|x|/x^2 tails)."""
import time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline, Ys

mp.mp.dps = 40
out = open('rc04_side.log', 'w')
rng = random.Random(9001)

insts = [Inst.proj(herm(rng, 3), 1, 'rand_M3_r1'), Inst.proj(herm(rng, 4), 2, 'rand_M4_r2'),
         Inst.proj(herm(rng, 5), 2, 'rand_M5_r2'), Inst.proj(herm(rng, 5), 4, 'corank1_M5'),
         Inst.proj(with_spectrum(rng, [2, 2, -1, -1]), 2, 'degenH_M4')]

# ---------------------------------------------------------------- (1) Proposition 2.1
logline(out, '(1) Proposition 2.1: c0 > ||H||, A = H + c0 > 0')
for I in insts:
    I.mpready()
    M, r = I.M, I.m[0]
    BHP2 = mp.fsum(abs(I.H[i, j])**2 for i in range(r) for j in range(r, M))
    trPAP = lambda c0: I.blocktr[1] + (M - r)*c0
    for c0 in [I.normH + mp.mpf('0.5'), I.normH*3 + 1, I.normH*30 + 10]:
        viol = 0
        mxratio = mp.mpf(0)
        for tau in [mp.mpf(k)/41 for k in range(1, 41)]:
            ys = [mp.re(z) for z in I.roots(tau, c0)]
            assert max(abs(mp.im(z)) for z in I.roots(tau, c0)) < mp.mpf(10)**(-25)
            pos = [z for z in ys if z > 0]
            neg = [z for z in ys if z < 0]
            if len(pos) != M - r or len(neg) != r:
                viol += 1
            Spos = mp.fsum(pos)
            up = trPAP(c0)/(1 - tau)
            # Schur lower bound: S_pos >= Tr(PAP)/(1-tau) - Tr(A_PB A_BB^-1 A_BP)/(1-tau)
            ABB = mp.matrix([[I.H[i, j] + (c0 if i == j else 0) for j in range(r)] for i in range(r)])
            APB = mp.matrix([[I.H[i, j] for j in range(r)] for i in range(r, M)])
            sch = mp.re(sum((APB*mp.inverse(ABB)*APB.H)[i, i] for i in range(M - r)))
            if not (Spos <= up + mp.mpf(10)**(-30) and Spos >= up - sch/(1 - tau) - mp.mpf(10)**(-30)):
                viol += 1
            mxratio = max(mxratio, abs(Spos - up)*(c0 - I.normH)/(2*BHP2))
        f = lambda tau: mp.fsum(mp.re(z) for z in I.roots(tau, c0) if mp.re(z) > 0) - trPAP(c0)/(1 - tau)
        val = mp.quad(f, [0, mp.mpf(1)/2, 1], method='gauss-legendre')
        Ev = I.E(c0)
        logline(out, '  %-14s c0=%-10s violations=%d  max |S_pos - S0_+|(c0-||H||)/(2||BHP||_F^2)=%s (<=1)  '
                     '|int(S_pos - S0_+) - E(c0)|=%s  E(c0)=%s  -||BHP||^2/c0=%s' % (
                         I.name, mp.nstr(c0, 6), viol, mp.nstr(mxratio, 4), mp.nstr(abs(val - Ev), 3), mp.nstr(Ev, 10),
                         mp.nstr(-BHP2/c0, 10)))

# ---------------------------------------------------------------- (2) Corollary 2.2
logline(out, '\n(2) Corollary 2.2: E(c) = int_R R(H + t) dt/(t - c), int_R R(H + t) dt = ||BHP||_F^2 (exact piecewise-linear integration)')
for I in insts:
    I.mpready()
    M, r = I.M, I.m[0]
    BHP2 = mp.fsum(abs(I.H[i, j])**2 for i in range(r) for j in range(r, M))
    knots = sorted(set([-l for l in I.lam] + [-l for l in I.lam0]))
    Rf = lambda t: I.R(t)
    tot = mp.mpf(0)
    for a, b in zip(knots[:-1], knots[1:]):
        tot += (Rf(a) + Rf(b))*(b - a)/2
    minR = min(Rf(t) for t in knots + [(a + b)/2 for a, b in zip(knots[:-1], knots[1:])])
    for c in [mp.mpc('0.4', '1.3'), mp.mpc('-2', '0.01'), mp.mpc('5', '7')]:
        st = mp.mpc(0)
        for a, b in zip(knots[:-1], knots[1:]):
            ra, rb = Rf(a), Rf(b)
            al = (rb - ra)/(b - a)
            be = ra - al*a
            st += al*(b - a) + (al*c + be)*(mp.log(b - c) - mp.log(a - c))
        logline(out, '  %-14s c=%-12s |E - Stieltjes| = %s' % (I.name, mp.nstr(c, 4), mp.nstr(abs(I.E(c) - st), 3)))
    logline(out, '  %-14s int R = %s  ||BHP||_F^2 = %s  diff %s ; min_t R(H+t) = %s (>= 0: pinching inequality)' % (
        I.name, mp.nstr(tot, 20), mp.nstr(BHP2, 20), mp.nstr(abs(tot - BHP2), 3), mp.nstr(minR, 5)))

# ---------------------------------------------------------------- (3) Remark 3.2 (M = 2)
logline(out, '\n(3) Remark 3.2, M = 2: H = [[alpha, gamma],[conj gamma, beta]], P = diag(1, 0)')
for trial in range(6):
    I = Inst.proj(herm(rng, 2), 1, 'M2_%d' % trial)
    I.mpready()
    al = mp.re(I.H[1, 1]); be = mp.re(I.H[0, 0]); g2 = abs(I.H[1, 0])**2      # index 1 = ran P, index 0 = ran B
    closed = max(0, (mp.sqrt((al - be)**2 + 4*g2) - abs(al) - abs(be))/2)
    Lv, err, nb, pcs = I.L(0)
    f = lambda tau: mp.sqrt(max(0, 4*tau*(1 - tau)*g2 - (al*tau + be*(1 - tau))**2))/(tau*(1 - tau))
    # direct check of the integrand formula against the pencil roots
    tau = mp.mpf('0.3')
    direct = mp.fsum(abs(mp.im(z)) for z in I.roots(tau, 0))
    # the claimed rho-form: |beta| sqrt((rho - rho1)(rho2 - rho))/(rho(1 + rho)) with rho1 rho2 = alpha^2/beta^2,
    # (1 + rho1)(1 + rho2) = ((alpha - beta)^2 + 4|gamma|^2)/beta^2
    s = ((al - be)**2 + 4*g2)/be**2 - 1 - al**2/be**2      # rho1 + rho2
    pr = al**2/be**2
    disc = s**2 - 4*pr
    res = []
    for name, rho_of_tau, jac in [('rho = tau/(1-tau) [as written]', lambda t: t/(1 - t), lambda t: 1/(1 - t)**2),
                                  ('rho = (1-tau)/tau', lambda t: (1 - t)/t, lambda t: 1/t**2)]:
        errs = []
        for tt in [mp.mpf(k)/20 for k in range(1, 20)]:
            rho = rho_of_tau(tt)
            q = -(rho**2 - s*rho + pr)     # (rho - rho1)(rho2 - rho)
            h = abs(be)*mp.sqrt(max(q, 0))/(rho*(1 + rho))
            errs.append(abs(f(tt) - h*jac(tt)))
        res.append('%s: max |f dtau - h drho| = %s' % (name, mp.nstr(max(errs), 3)))
    logline(out, '  alpha=%-6s beta=%-6s |gamma|^2=%-6s L=%s closed=%s R=%s |L-closed|=%s |f-roots|=%s' % (
        mp.nstr(al, 4), mp.nstr(be, 4), mp.nstr(g2, 4), mp.nstr(Lv, 20), mp.nstr(closed, 20), mp.nstr(I.R(0), 20),
        mp.nstr(abs(Lv - closed), 3), mp.nstr(abs(direct - f(tau)), 3)))
    logline(out, '      ' + ' ; '.join(res))

# ---------------------------------------------------------------- (4) Remark 3.3
logline(out, '\n(4) Remark 3.3 (dps 30): (a) S_+ - S0_+ = (i/2pi) int_R ell dx; (c) (i/2pi) int (Phi_B - Phi_P) dx/x = E(c); '
             '(d) 2 pi^2 R(H + c0) = int_R dx/x [...]')
mp.mp.dps = 30


def eigh_vals(A):
    return [mp.re(e) for e in mp.eigh(A, eigvals_only=True)]


def Om(z):
    return z*mp.log(z) - z


for I in insts[:3]:
    I._mp_dps = None
    I.mpready()
    M, r = I.M, I.m[0]
    Pm = mp.diag([0]*r + [1]*(M - r))
    Bm = mp.eye(M) - Pm
    c = mp.mpc('0.3', '0.9')
    tau = mp.mpf('0.37')
    # (a)
    def ell(x):
        nu = eigh_vals(I.H - x*(Pm - tau*mp.eye(M)))
        nu0 = eigh_vals(I.Hd - x*(Pm - tau*mp.eye(M)))
        return mp.fsum(mp.log(v + c) for v in nu) - mp.fsum(mp.log(v + c) for v in nu0)
    lhs = I.S_plus(I.dvec(tau), c) - I.S0_plus(I.dvec(tau), c)
    X = 20*max(1, float(I.normH))/min(float(tau), 1 - float(tau))
    rhs = 1j/(2*mp.pi)*mp.quad(ell, [-mp.inf, -X, -X/4, -X/16, 0, X/16, X/4, X, mp.inf])
    logline(out, '  %-14s (a) |S_+ - S0_+ - (i/2pi) int ell| = %s   (value %s)' % (I.name, mp.nstr(abs(lhs - rhs), 3), mp.nstr(lhs, 12)))
    # (c)
    def PhiB(x):
        return mp.fsum(Om(v) for v in [e + c for e in eigh_vals(I.H + x*Bm)]) - mp.fsum(Om(v) for v in [e + c for e in eigh_vals(I.Hd + x*Bm)])
    def PhiP(x):
        return mp.fsum(Om(v) for v in [e + c for e in eigh_vals(I.H - x*Pm)]) - mp.fsum(Om(v) for v in [e + c for e in eigh_vals(I.Hd - x*Pm)])
    g = lambda x: (PhiB(x) - PhiP(x))/x if x != 0 else mp.diff(lambda u: PhiB(u) - PhiP(u), 0)
    X = 20*max(1, float(I.normH))
    with mp.workdps(45):
        J = mp.quad(g, [-mp.inf, -X, -X/10, -1, -mp.mpf('0.1'), 0, mp.mpf('0.1'), 1, X/10, X, mp.inf])
    val = 1j/(2*mp.pi)*J
    logline(out, '  %-14s (c) |(i/2pi) int (Phi_B - Phi_P)/x - E(c)| = %s' % (I.name, mp.nstr(abs(val - I.E(c)), 3)))
    # (d) the real 1D formula at c0 real
    for c0 in [mp.mpf(0), mp.mpf('0.7')]:
        Lam = lambda t: t*mp.log(abs(t)) - t if t != 0 else mp.mpf(0)
        def gd(x):
            a1 = mp.fsum(Lam(e + c0) for e in eigh_vals(I.H + x*Bm)) - mp.fsum(Lam(e + c0) for e in eigh_vals(I.Hd + x*Bm))
            a2 = mp.fsum(Lam(e + c0) for e in eigh_vals(I.H - x*Pm)) - mp.fsum(Lam(e + c0) for e in eigh_vals(I.Hd - x*Pm))
            return (a1 - a2)/x
        # kinks: x with an eigenvalue of H + c0 + xB, H_d + c0 + xB (resp. -xP) equal to 0
        kinks = []
        for (A0, sgn, Q) in [(I.Hs, 1, 'B'), (I.Hds, 1, 'B'), (I.Hs, -1, 'P'), (I.Hds, -1, 'P')]:
            Qm = sp.diag(*([1]*r + [0]*(M - r))) if Q == 'B' else sp.diag(*([0]*r + [1]*(M - r)))
            c0r = sp.Rational(str(mp.nstr(c0, 5)))
            pol = sp.Poly(sp.expand((A0 + c0r*sp.eye(M) + sgn*Ys*Qm).det(method='berkowitz')), Ys)
            if pol.degree() >= 1:
                for z in mp.polyroots([mp.mpf(sp.re(x)) for x in pol.all_coeffs()], maxsteps=500, extraprec=200):
                    if abs(mp.im(z)) < mp.mpf(10)**(-15):
                        kinks.append(mp.re(z))
        X = 20*max(1, float(I.normH))
        pts = sorted(set([-mp.inf, -X, -1, 0, 1, X, mp.inf] + kinks))
        with mp.workdps(45):
            J = mp.quad(gd, pts)
        logline(out, '  %-14s (d) c0=%-4s int = %s  2 pi^2 R = %s  diff %s  (#kinks %d)' % (
            I.name, mp.nstr(c0, 2), mp.nstr(J, 18), mp.nstr(2*mp.pi**2*I.R(c0), 18), mp.nstr(abs(J - 2*mp.pi**2*I.R(c0)), 3),
            len(kinks)))
out.close()
