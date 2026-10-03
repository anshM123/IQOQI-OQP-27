"""ri03: Lemma C (the Burgers identity)  d/dtau Lam_+ = d/dc S_+   (PROOF.md s.1), plus related checks.

 (1) random instances, random (tau, c), Im c > 0: high-precision numerical derivatives (mpmath.diff; d/dc along the real
     direction, legitimate because S_+ is holomorphic in c);
 (2) the pinched pencil (explicit formulas) and the 'total' version d/dtau (Lam_+ - Lam0_+) = d/dc (S_+ - S0_+);
 (3) a configuration with a DOUBLE root in C_+ (H = H_d with a repeated eigenvalue of PHP, and a small perturbation of it):
     the contour-integral form of Lemma C needs no simplicity assumption;
 (4) the contour-integral representations S_+ = (1/2 pi i) oint y p'/p dy, Lam_+ = (1/2 pi i) oint Log(y) p'/p dy on a circle
     in C_+ (direct numerical contour integration);
 (5) for real c the individual roots x(s,tau) of det(g - s - x(P - tau)) satisfy the complex inviscid Burgers (Hopf) equation
     x_tau + x x_s = 0 (s = -c), which is the pointwise form of (1) (not used in the proof).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, rand_herm, standard_instances

mp.mp.dps = 40
rng = np.random.default_rng(7)
insts = standard_instances()
worst1 = mp.mpf(0); worst2 = mp.mpf(0)
for I in insts:
    for k in range(3):
        tau = mp.mpf(rng.uniform(0.05, 0.95)); c = mp.mpc(rng.normal(), rng.uniform(0.05, 2))
        dLt = mp.diff(lambda t: I.Lam_plus(t, c), tau)
        dSc = mp.diff(lambda h: I.S_plus(tau, c + h), 0)
        e1 = abs(dLt - dSc)/(1 + abs(dSc)); worst1 = max(worst1, e1)
        dLt0 = mp.diff(lambda t: I.Lam_plus(t, c) - I.Lam0_plus(t, c), tau)
        dSc0 = mp.diff(lambda h: I.S_plus(tau, c + h) - I.S0_plus(tau, c + h), 0)
        e2 = abs(dLt0 - dSc0)/(1 + abs(dSc0)); worst2 = max(worst2, e2)
print(f'(1) d_tau Lam_+ = d_c S_+ : max rel. defect over {3*len(insts)} random points = {mp.nstr(worst1, 3)}')
print(f'(2) d_tau (Lam_+ - Lam0_+) = d_c (S_+ - S0_+) : max rel. defect = {mp.nstr(worst2, 3)}')
# pinched explicit check
I = insts[4]; tau = mp.mpf('0.3'); c = mp.mpc('0.2', '0.7')
a = mp.diff(lambda t: I.Lam0_plus(t, c), tau); b = mp.diff(lambda h: I.S0_plus(tau, c + h), 0)
print(f'    pinched pencil alone: d_tau Lam0_+ = {mp.nstr(a, 20)},  d_c S0_+ = {mp.nstr(b, 20)}  ((M-r)/(1-tau) = {mp.nstr((I.M - I.r)/(1 - tau), 20)})')

# (3) double root
Hd = np.diag([1.0, 1.0, 0.4, -0.7]).astype(complex); Hd[2, 3] = Hd[3, 2] = 0.5      # P-block diag(1,1): double eigenvalue mu = 1
for eps, lab in [(0.0, 'H = H_d (double C_+ root (1 + c)/(1 - tau))'), (1e-6, 'perturbed off-diagonal 1e-6'), (0.3, 'perturbed off-diagonal 0.3')]:
    H = Hd.copy(); H[0, 2] = H[2, 0] = eps; H[1, 3] = eps*1j; H[3, 1] = -eps*1j
    J = Inst(H, 2, lab)
    tau = mp.mpf('0.37'); c = mp.mpc('-0.4', '0.25')
    up, dn = J.split(tau, c)
    gap = min(abs(up[0] - up[1]), 1) if len(up) == 2 else None
    dLt = mp.diff(lambda t: J.Lam_plus(t, c), tau); dSc = mp.diff(lambda h: J.S_plus(tau, c + h), 0)
    print(f'(3) {lab}: |y1 - y2| (C_+ roots) = {mp.nstr(gap, 3)};  d_tau Lam_+ - d_c S_+ = {mp.nstr(abs(dLt - dSc), 3)}')

# (4) contour-integral representation
I = insts[6]; tau = mp.mpf('0.41'); c = mp.mpc('0.3', '0.9')
up, dn = I.split(tau, c)
R0 = max(abs(y) for y in up); eta = min(mp.im(y) for y in up)
T = (R0**2 + (eta/2)**2)/(eta) + 1; rad = T - eta/4                   # disc centred iT, closure inside C_+, contains all C_+ roots
assert all(abs(y - 1j*T) < rad for y in up) and T - rad > 0
Mx = I.M
def p_and_dp(y):
    A = I.H + c*mp.eye(Mx) - y*(I.P - tau*mp.eye(Mx))
    d = mp.det(A)
    Ainv = mp.inverse(A)
    dA = -(I.P - tau*mp.eye(Mx))
    tr = sum((Ainv*dA)[i, i] for i in range(Mx))   # p'/p = Tr(A^{-1} dA/dy)
    return tr
def contour(phi):
    f = lambda th: phi(1j*T + rad*mp.expj(th))*p_and_dp(1j*T + rad*mp.expj(th))*1j*rad*mp.expj(th)
    return mp.quad(f, mp.linspace(0, 2*mp.pi, 9))/(2j*mp.pi)
S_c = contour(lambda y: y); L_c = contour(lambda y: mp.log(y)); N_c = contour(lambda y: 1)
print(f'(4) circle centre i*{mp.nstr(T, 5)}, radius {mp.nstr(rad, 5)}: (1/2pi i) oint p\'/p = {mp.nstr(N_c, 12)} (M - r = {I.M - I.r})')
print(f'    |contour S_+ - S_+| = {mp.nstr(abs(S_c - I.S_plus(tau, c)), 3)},  |contour Lam_+ - Lam_+| = {mp.nstr(abs(L_c - I.Lam_plus(tau, c)), 3)}')

# (5) Hopf equation for the real-axis pencil roots x(s, tau) (g = H, s real): x_tau + x x_s = 0 for each simple root
I = insts[3]
worst5 = mp.mpf(0); nchk = 0
for k in range(20):
    s = mp.mpf(rng.uniform(float(min(I.lam)), float(max(I.lam)))); tau = mp.mpf(rng.uniform(0.1, 0.9))
    xs = I.roots(tau, -s)      # roots of det(H - s - x(P - tau))
    for x0 in xs:
        if abs(mp.im(x0)) < 1e-10:
            continue
        def track(t, s1):
            ys = I.roots(t, -s1)
            return min(ys, key=lambda z: abs(z - x0))
        xt = mp.diff(lambda t: track(t, s), tau); xsd = mp.diff(lambda s1: track(tau, s1), s)
        worst5 = max(worst5, abs(xt + x0*xsd)/(1 + abs(xt))); nchk += 1
print(f'(5) Hopf equation x_tau + x x_s = 0 at {nchk} non-real roots: max rel. defect = {mp.nstr(worst5, 3)}')
ok = worst1 < 1e-25 and worst2 < 1e-25 and worst5 < 1e-20
print('ALL OK' if ok else 'CHECK')
