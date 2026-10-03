"""ri10: the log-determinant ('Frullani') form of the Radon identity (PROOF.md s.3, Proposition 3.3 and Remark 3.4).

For c in C_+ let nu_j(x,tau) = eigenvalues of the Hermitian matrix H - x(P - tau), nu0_j those of H_d - x(P - tau), and
    ell(x,tau,c) = sum_j Log(nu_j + c) - sum_j Log(nu0_j + c)        (a continuous branch of log p/q on the real x-line).
 (a) complex Jensen:   S_+(tau,c) - S0_+(tau,c) = (i/2pi) int_R ell(x,tau,c) dx;
 (b) exact tau-integration (ell depends on tau only through the scalar shift x tau):
       int_0^1 ell(x,tau,c) dtau = (Phi_B(x) - Phi_P(x))/x,   Phi_B(x) = Tr Om(H + c + xB) - Tr Om(H_d + c + xB),
       Phi_P(x) = Tr Om(H + c - xP) - Tr Om(H_d + c - xP),   Om(z) = z Log z - z;
 (c) Frullani/contour identity:  (i/2pi) int_R (Phi_B(x) - Phi_P(x)) dx/x = E(c)   (PROVED directly: Phi_B extends to
     C_+ and Phi_P to C_- in x);
 (d) the real one-dimensional form (c -> c0 + i0, Lam(t) = t log|t| - t):
       2 pi^2 (Tr (H+c0)_+ - Tr (H_d+c0)_+) = int_R dx/x [Tr Lam(H+c0+xB) - Tr Lam(H_d+c0+xB) - Tr Lam(H+c0-xP) + Tr Lam(H_d+c0-xP)].
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, standard_instances, eigvals

mp.mp.dps = 25
insts = standard_instances()

def heig(A):
    return [mp.re(e) for e in mp.eigh(A, eigvals_only=True)]

def boosted(f):
    """evaluate f(x) at working precision dps + log10(1 + |x|) + 10: the x-integrals run over R and tanh-sinh samples |x| up
    to ~10^30, where the O(1) eigenvalues of H + xB, H - xP are otherwise computed with absolute error ~|x| 10^-dps."""
    def g(x):
        b = int(max(0, mp.log10(1 + abs(x)))) + 10
        with mp.workdps(mp.mp.dps + b):
            v = f(x)
        return +v
    return g

def ell(I, x, tau, c):
    M = I.M
    nu = heig(I.H - x*(I.P - tau*mp.eye(M))); nu0 = heig(I.Hd - x*(I.P - tau*mp.eye(M)))
    return sum((mp.log(v + c) for v in nu), mp.mpc(0)) - sum((mp.log(v + c) for v in nu0), mp.mpc(0))

Om = lambda z: z*mp.log(z) - z if z != 0 else mp.mpc(0)
def TrOm(A, c):
    return sum((Om(v + c) for v in heig(A)), mp.mpc(0))
def PhiB(I, x, c):
    return TrOm(I.H + x*I.B, c) - TrOm(I.Hd + x*I.B, c)
def PhiP(I, x, c):
    return TrOm(I.H - x*I.P, c) - TrOm(I.Hd - x*I.P, c)

# (a)
print('(a) complex Jensen  S_+ - S0_+ = (i/2pi) int ell dx')
worst_a = mp.mpf(0)
for I in insts[:6]:
    tau, c = mp.mpf('0.37'), mp.mpc('0.3', '0.6')
    lhs = I.S_plus(tau, c) - I.S0_plus(tau, c)
    rhs = 1j/(2*mp.pi)*mp.quad(boosted(lambda x: ell(I, x, tau, c)), [-mp.inf, -100, -10, -1, 0, 1, 10, 100, mp.inf])
    worst_a = max(worst_a, abs(lhs - rhs))
    print(f'    {I.name:18s} lhs = {mp.nstr(lhs, 15):>34s}  rhs = {mp.nstr(rhs, 15):>34s}')
print(f'    max |diff| = {mp.nstr(worst_a, 3)}')

# (b)
print('(b) int_0^1 ell dtau = (Phi_B - Phi_P)/x')
worst_b = mp.mpf(0)
I = insts[4]; c = mp.mpc('-0.2', '0.4')
for x in [mp.mpf('-3.1'), mp.mpf('-0.4'), mp.mpf('0.25'), mp.mpf('2.7')]:
    num = mp.quad(lambda t: ell(I, x, t, c), [0, 0.5, 1])
    cl = (PhiB(I, x, c) - PhiP(I, x, c))/x
    worst_b = max(worst_b, abs(num - cl))
print(f'    max |diff| = {mp.nstr(worst_b, 3)}')

# (c)
print('(c) (i/2pi) int (Phi_B - Phi_P) dx/x = E(c)')
worst_c = mp.mpf(0)
for I in insts[:7]:
    for c in [mp.mpc('0.4', '0.8'), mp.mpc('-1.0', '0.15')]:
        f = boosted(lambda x: (PhiB(I, x, c) - PhiP(I, x, c))/x)
        val = 1j/(2*mp.pi)*mp.quad(f, [-mp.inf, -100, -10, -1, 0, 1, 10, 100, mp.inf])
        e = I.E(c)
        worst_c = max(worst_c, abs(val - e))
    print(f'    {I.name:18s} last c: integral = {mp.nstr(val, 15):>34s}  E(c) = {mp.nstr(e, 15):>34s}')
print(f'    max |diff| = {mp.nstr(worst_c, 3)}')

# (d) real form at c0 (kinks: zeros of the four determinants in x)
print('(d) real form: (1/2pi^2) int dx/x [Lam-traces] = R(H + c0)')
Lam = lambda t: t*mp.log(abs(t)) - t if t != 0 else mp.mpf(0)
def TrLam(A):
    return sum((Lam(v) for v in heig(A)), mp.mpf(0))
worst_d = mp.mpf(0)
for I in insts[:7] + [insts[9], insts[10]]:
    for c0 in [mp.mpf(0), mp.mpf('0.31')]:
        M = I.M; A = I.H + c0*mp.eye(M); Ad = I.Hd + c0*mp.eye(M)
        f = boosted(lambda x: (TrLam(A + x*I.B) - TrLam(Ad + x*I.B) - TrLam(A - x*I.P) + TrLam(Ad - x*I.P))/x if x != 0 else mp.mpf(0))
        kinks = []
        Ainv = mp.inverse(A)
        for k_ in eigvals(Ainv*I.B):
            if abs(k_) > 1e-12: kinks.append(-1/mp.re(k_))
        for k_ in eigvals(Ainv*I.P):
            if abs(k_) > 1e-12: kinks.append(1/mp.re(k_))
        kinks += [-(b + c0) for b in I.beta] + [m + c0 for m in I.mu]
        pts = sorted(set([mp.mpf(0), mp.mpf(-100), mp.mpf(100)] + [k_ for k_ in kinks if abs(k_) < 1e6]))
        val = mp.quad(f, [-mp.inf] + pts + [mp.inf])/(2*mp.pi**2)
        Rv = I.R(c0)
        worst_d = max(worst_d, abs(val - Rv))
    print(f'    {I.name:18s} c0 = 0.31: (1/2pi^2) int = {mp.nstr(val, 16):>22s}  R(H + c0) = {mp.nstr(Rv, 16):>22s}')
print(f'    max |diff| = {mp.nstr(worst_d, 3)}')
print('ALL OK' if max(worst_a, worst_b, worst_c, worst_d) < 1e-12 else 'CHECK')
