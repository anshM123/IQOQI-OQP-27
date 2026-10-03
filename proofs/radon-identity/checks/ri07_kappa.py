"""ri07: the constant kappa = 0 (PROOF.md Proposition 2.2) -- ingredients on the real half-line c0 > ||H||.

For real c0 > ||H|| put A = H + c0 > 0.  Then (all roots of det(A - y(P - tau)) are real and nonzero):
 (a) the C_+ roots at c = c0 + i eps converge, as eps -> 0+, to the M - r POSITIVE roots (Re y > 0 for C_+ roots);
 (b) Ky Fan:  S_pos(tau) := sum of positive roots <= Tr(PAP)/(1 - tau) = S0_+(tau, c0);
 (c) Schur lower bounds:  S_pos - S0_+ >= -Tr(A_PB A_BB^{-1} A_BP)/(1 - tau)  and  >= -Tr(A_BP A_PP^{-1} A_PB)/tau,
     hence |S_pos - S0_+| <= 2 ||BHP||_F^2/(c0 - ||H||);
 (d) int_0^1 (S_pos - S0_+) dtau = E(c0)  (real), and both -> 0 as c0 -> oo  =>  kappa = 0.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, standard_instances

mp.mp.dps = 30
insts = standard_instances()

def blocks(I, A):
    M, r = I.M, I.r
    App = mp.matrix(M - r, M - r); Apb = mp.matrix(M - r, r); Abp = mp.matrix(r, M - r); Abb = mp.matrix(r, r)
    for i in range(M):
        for j in range(M):
            if i < M - r and j < M - r: App[i, j] = A[i, j]
            elif i < M - r: Apb[i, j - (M - r)] = A[i, j]
            elif j < M - r: Abp[i - (M - r), j] = A[i, j]
            else: Abb[i - (M - r), j - (M - r)] = A[i, j]
    return App, Apb, Abp, Abb

def tr(X):
    return sum(X[i, i] for i in range(X.rows))

worst_a = mp.mpf(0); viol_b = 0; viol_c = 0; worst_d = mp.mpf(0); worst_bound = mp.mpf(0)
for I in insts:
    M, r = I.M, I.r
    for fac in [mp.mpf('1.05'), mp.mpf(2), mp.mpf(10)]:
        c0 = fac*I.normH + mp.mpf('0.01')
        A = I.H + c0*mp.eye(M)
        App, Apb, Abp, Abb = blocks(I, A)
        lb1 = -mp.re(tr(Apb*mp.inverse(Abb)*Abp)); lb2 = -mp.re(tr(Abp*mp.inverse(App)*Apb))
        for tau in [mp.mpf(x) for x in ['0.001', '0.1', '0.37', '0.5', '0.8', '0.999']]:
            ys = I.roots(tau, c0)
            assert max(abs(mp.im(y)) for y in ys) < mp.mpf(10)**(-20)
            pos = sorted([mp.re(y) for y in ys if mp.re(y) > 0])
            assert len(pos) == M - r
            Spos = sum(pos, mp.mpf(0)); S0 = mp.re(I.S0_plus(tau, c0))
            # (a)
            up, _ = I.split(tau, c0 + 1j*mp.mpf('1e-20'))
            assert all(mp.re(y) > 0 for y in up)
            worst_a = max(worst_a, abs(sum(up, mp.mpc(0)) - Spos))
            # (b), (c)
            if Spos - S0 > mp.mpf(10)**(-25): viol_b += 1
            if Spos - S0 < lb1/(1 - tau) - mp.mpf(10)**(-25) or Spos - S0 < lb2/tau - mp.mpf(10)**(-25): viol_c += 1
            worst_bound = max(worst_bound, abs(Spos - S0)*(c0 - I.normH)/(2*I.frobBHP2))
        # (d)
        f = lambda t: (lambda ys: sum([mp.re(y) for y in ys if mp.re(y) > 0], mp.mpf(0)))(I.roots(t, c0)) - mp.re(I.S0_plus(t, c0))
        val = mp.quad(f, [0, 0.5, 1])
        e = mp.re(I.E(mp.mpc(c0, 0)))
        worst_d = max(worst_d, abs(val - e))
        if fac == 10:
            print(f'  {I.name:18s} c0 = 10||H||: int(S_pos - S0_+) = {mp.nstr(val, 15):>22s}, E(c0) = {mp.nstr(e, 15):>22s}, -||BHP||_F^2/c0 = {mp.nstr(-I.frobBHP2/c0, 8)}')
print(f'(a) |S_+(c0 + 1e-20 i) - S_pos| max = {mp.nstr(worst_a, 3)}   (C_+ roots -> positive roots)')
print(f'(b) Ky Fan violations S_pos > S0_+ : {viol_b}   (expect 0)')
print(f'(c) Schur lower-bound violations : {viol_c}   (expect 0);  max |S_pos - S0_+| (c0 - ||H||)/(2||BHP||_F^2) = {mp.nstr(worst_bound, 6)} (expect <= 1)')
print(f'(d) max |int_0^1 (S_pos - S0_+) dtau - E(c0)| = {mp.nstr(worst_d, 3)}')
print('ALL OK' if viol_b == 0 and viol_c == 0 and worst_bound <= 1 and worst_d < 1e-20 and worst_a < 1e-15 else 'CHECK')
