"""rc03: Lemma C (d_tau Lam_+ = d_c S_+) incl. at a GENUINE double root inside C_+ (individual roots not differentiable there),
the contour formula (1.1) on the very disc D constructed in the proof of Lemma C, and Lemma D (tau -> 0, 1 limits; spec T_0 in
C_+ with Im T_0 >= Im c; exp Theta = det(H+c)/det(H_d+c); Theta = Theta_1 exactly, i.e. k = 0 in Step 2), dps 60.
Derivatives are finite-difference derivatives (mp.diff) of eigenvalue-based S_+, Lam_+ -- NOT the contour formula, for which
d_tau Lam_+ and d_c S_+ are literally the same integral -(1/2 pi i) oint Tr[(H + c - y(P - tau))^{-1}] dy."""
import time, random
import sympy as sp
import mpmath as mp
from rc_core import Inst, herm, with_spectrum, logline, Ys, Ts, Cs

mp.mp.dps = 60
out = open('rc03_burgers_ends.log', 'w')
rng = random.Random(4242)


def Splus_tc(I, tau, c):
    return I.S_plus(I.dvec(tau), c)


def Lplus_tc(I, tau, c):
    return I.Lam_plus(I.dvec(tau), c)


def burgers_defect(I, tau, c):
    dLt = mp.diff(lambda t: Lplus_tc(I, t, c), tau)
    dSc = mp.diff(lambda x: Splus_tc(I, tau, c + x), 0)
    return dLt, dSc


# ---------------------------------------------------------------- (1) random points
logline(out, '(1) Lemma C at random points: |d_tau Lam_+ - d_c S_+|')
insts = [Inst.proj(herm(rng, 3), 1, 'rand_M3_r1'), Inst.proj(herm(rng, 4), 2, 'rand_M4_r2'),
         Inst.proj(herm(rng, 5), 1, 'rank1B_M5'), Inst.proj(herm(rng, 5), 4, 'corank1_M5'),
         Inst.proj(with_spectrum(rng, [1, 1, -1, -1, 2]), 2, 'degenH_M5')]
mx = mp.mpf(0)
for I in insts:
    I.mpready()
    for _ in range(6):
        tau = mp.mpf(rng.uniform(0.02, 0.98))
        c = mp.mpc(rng.uniform(-2, 2), 10**rng.uniform(-2, 0.5))
        a, b = burgers_defect(I, tau, c)
        mx = max(mx, abs(a - b)/max(1, abs(a)))
logline(out, '  30 random (instance, tau, c): max relative defect %s' % mp.nstr(mx, 3))

# ---------------------------------------------------------------- (2) a genuine double root in C_+
logline(out, '\n(2) double root inside C_+ (collision of two C_+ roots), M = 4, r = 1 (three C_+ roots)')
found = None
for trial in range(12):
    I = Inst.proj(herm(rng, 4), 1, 'M4_r1_trial%d' % trial)
    I.mpready()
    tau0 = sp.Rational(rng.randint(15, 85), 100)
    p = I.pencil_poly(csym=True)
    pt = sp.Poly(p.as_expr().subs(Ts, tau0), Ys, Cs)
    py = sp.Poly(pt.as_expr(), Ys)
    D = sp.Poly(sp.discriminant(py), Cs)
    cf = [mp.mpc(*[mp.mpf(sp.Rational(x).p)/sp.Rational(x).q for x in sp.nsimplify(z).as_real_imag()]) for z in D.all_coeffs()]
    rts = mp.polyroots(cf, maxsteps=2000, extraprec=400)
    for cs in rts:
        if mp.im(cs) > 0.05:
            ys = I.roots(mp.mpf(tau0.p)/tau0.q, cs)
            up = sorted([z for z in ys if mp.im(z) > 0], key=lambda z: (mp.re(z), mp.im(z)))
            # find the closest pair among the C_+ roots
            best = min(abs(a - b) for i, a in enumerate(up) for b in up[i + 1:]) if len(up) >= 2 else 1
            if best < mp.mpf(10)**(-20):
                found = (I, mp.mpf(tau0.p)/tau0.q, cs, best, up)
                break
    if found:
        break
if not found:
    logline(out, '  no double C_+ root found in 12 trials')
else:
    I, tau0, cs, gap, up = found
    logline(out, '  %s: tau0 = %s, c* = %s ; closest C_+ pair distance %s (double root at %s)' % (
        I.name, mp.nstr(tau0, 4), mp.nstr(cs, 20), mp.nstr(gap, 3), mp.nstr(sorted(up, key=lambda z: 0)[0], 12)))
    logline(out, '  C_+ roots at (tau0, c*): ' + ', '.join(mp.nstr(z, 15) for z in up))
    a, b = burgers_defect(I, tau0, cs)
    logline(out, '  d_tau Lam_+ = %s\n  d_c S_+     = %s\n  |defect| = %s' % (mp.nstr(a, 30), mp.nstr(b, 30), mp.nstr(abs(a - b), 3)))
    # individual roots are NOT differentiable there: show the sqrt behaviour of the colliding pair
    for h in [mp.mpf(10)**(-8), mp.mpf(10)**(-16)]:
        ysh = sorted([z for z in I.roots(tau0, cs + h) if mp.im(z) > 0], key=lambda z: mp.re(z))
        pair = min(abs(x - y) for i, x in enumerate(ysh) for y in ysh[i + 1:])
        logline(out, '  c = c* + %s: closest C_+ pair distance %s (~ sqrt(h): branch point of the individual roots)' % (
            mp.nstr(h, 2), mp.nstr(pair, 4)))
    # (1.1) on the disc D of the proof of Lemma C
    c0 = cs
    K0 = I.normH + abs(c0) + 1
    eta = mp.im(c0)/2
    rho = 2*K0/min(tau0, 1 - tau0)
    T = rho**2/eta + 1
    rad = T - eta/2
    cen = mp.mpc(0, T)
    M = I.M

    def resolvent_terms(yv):
        A = mp.matrix(M, M)
        for i in range(M):
            for j in range(M):
                A[i, j] = I.H[i, j] + (c0 if i == j else 0)
        Pt = mp.matrix(M, M)
        for i in range(M):
            Pt[i, i] = (1 if i >= I.m[0] else 0) - tau0
        Ai = mp.inverse(A - yv*Pt)
        return -sum((Ai*Pt)[i, i] for i in range(M))      # p_y/p

    def contour(phi):
        # the disc is huge (radius ~ rho^2/eta) and passes at distance >= 1.5 eta below the C_+ roots: panels are
        # concentrated geometrically around the bottom point th = 3pi/2
        f = lambda th: phi(cen + rad*mp.expj(th))*resolvent_terms(cen + rad*mp.expj(th))*1j*rad*mp.expj(th)
        s0 = eta/(20*rad)
        offs = [mp.mpf(0)]
        x = s0
        while x < mp.pi:
            offs.append(x)
            x *= 2
        offs.append(mp.pi)
        pts = sorted(set([3*mp.pi/2 + o for o in offs] + [3*mp.pi/2 - o for o in offs]))
        return mp.quad(f, pts)/(2j*mp.pi)

    with mp.workdps(40):
        cS = contour(lambda z: z)
        cL = contour(mp.log)
        cN = contour(lambda z: 1)
    dv = I.dvec(tau0)
    logline(out, '  (1.1) on the proof\'s disc (centre i*%s, radius %s): #roots inside = %s ; |S_+ - contour| = %s ; '
                 '|Lam_+ - contour| = %s' % (mp.nstr(T, 6), mp.nstr(rad, 6), mp.nstr(cN, 12), mp.nstr(abs(I.S_plus(dv, c0) - cS), 3),
                                              mp.nstr(abs(I.Lam_plus(dv, c0) - cL), 3)))

# ---------------------------------------------------------------- (3) Lemma D: both ends
logline(out, '\n(3) Lemma D: limits of Lam_+ - Lam0_+ at tau -> 1 (-> 0) and tau -> 0 (-> Theta); Theta vs Theta_1')
insts3 = insts + [Inst.proj(sp.Matrix([[0, 0, 1, sp.I], [0, 0, 2, 1], [1, 2, 3, 0], [-sp.I, 1, 0, -1]]), 2, 'zero_BHB_M4'),
                  Inst.proj(herm(rng, 6, offscale=sp.Rational(1, 1000)), 3, 'near_comm_1e-3_M6')]
worstk = mp.mpf(0)
for I in insts3:
    I.mpready()
    M = I.M
    r = I.m[0]
    for c in [mp.mpc('0.37', '0.81'), mp.mpc('-1.3', '0.05'), mp.mpc('2.1', '3.0')]:
        # T_0 = PHP + c - PHB (BHB + c)^{-1} BHP on ran P (indices r..M-1)
        Bi = [i for i in range(r)]
        Pi = [i for i in range(r, M)]
        HBB = mp.matrix([[I.H[i, j] + (c if i == j else 0) for j in Bi] for i in Bi])
        HPP = mp.matrix([[I.H[i, j] + (c if i == j else 0) for j in Pi] for i in Pi])
        HPB = mp.matrix([[I.H[i, j] for j in Bi] for i in Pi])
        HBP = mp.matrix([[I.H[i, j] for j in Pi] for i in Bi])
        T0 = HPP - HPB*mp.inverse(HBB)*HBP
        specT = mp.eig(T0, left=False, right=False) if T0.rows > 1 else [T0[0, 0]]
        ImT = (T0 - T0.H)/(2j)
        minImT = min(mp.re(e) for e in mp.eigh(ImT, eigvals_only=True))
        Theta = mp.fsum(mp.log(t) for t in specT) - mp.fsum(mp.log(mu + c) for mu in I.blockspec[1])
        Th1 = I.Theta1(c)
        detratio = mp.det(I.H + c*mp.eye(M))/mp.det(I.Hd + c*mp.eye(M))
        worstk = max(worstk, abs(Theta - Th1))
        r1 = []
        r0 = []
        for k in (4, 8, 16, 30):
            e = mp.mpf(10)**(-k)
            dv1 = [-(1 - e), e]       # tau = 1 - e
            dv0 = [-e, 1 - e]         # tau = e
            r1.append(abs(I.Lam_plus(dv1, c) - I.Lam0_plus(dv1, c)))
            r0.append(abs(I.Lam_plus(dv0, c) - I.Lam0_plus(dv0, c) - Theta))
        logline(out, '  %-20s c=%-14s min Im T_0 - Im c = %s ; |exp Theta - det ratio| = %s ; |Theta - Theta_1| = %s' % (
            I.name, mp.nstr(c, 4), mp.nstr(minImT - mp.im(c), 4), mp.nstr(abs(mp.exp(Theta) - detratio), 3),
            mp.nstr(abs(Theta - Th1), 3)))
        logline(out, '      |Lam_+ - Lam0_+| at 1 - 1e-4,-8,-16,-30: %s ;  |Lam_+ - Lam0_+ - Theta| at 1e-4,-8,-16,-30: %s' % (
            ', '.join(mp.nstr(x, 2) for x in r1), ', '.join(mp.nstr(x, 2) for x in r0)))
logline(out, 'max |Theta - Theta_1| over all (instance, c): %s   (k = 0 in Step 2)' % mp.nstr(worstk, 3))
out.close()
