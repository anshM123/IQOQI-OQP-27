"""ri02: Lemma A (root location/count), Lemma B (bounds), trace identity, domination bound.  PROOF.md s.1.

For Im c > 0, 0 < tau < 1, roots y of det(H + c - y(P - tau)):
  A: none real; exactly M - r in C_+ (and r in C_-).
  B(i):  |y| <= K/min(tau, 1 - tau),                       K = ||H|| + |c|
  B(ii): C_+ roots with tau <= 1/2, and C_- roots with tau >= 1/2:  |y| <= K/sqrt(tau(1 - tau)).
  B(iii) trace identity S_+ + S_- = S0_+ + S0_-;  domination |S_+ - S0_+| <= M K (2 + (tau(1-tau))^{-1/2}).
  Real c (Lemma 1(b) of Q_2bmv): non-real roots satisfy |y| <= ||H + c||/sqrt(tau(1-tau)).
Also shown: B(ii) FAILS for the 'wrong' half plane (C_- roots at small tau grow like 1/tau), so the half-plane split is needed.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, rand_herm, standard_instances

mp.mp.dps = 30
rng = np.random.default_rng(2026)
insts = standard_instances()
for k in range(6):
    M = int(rng.integers(2, 7)); r = int(rng.integers(1, M))
    insts.append(Inst(rand_herm(rng, M, float(rng.choice([0.3, 1, 5]))), r, f'sweep{k}_M{M}_r{r}'))

taus = [mp.mpf(x) for x in ['1e-8', '1e-4', '0.01', '0.2', '0.5', '0.7', '0.99', '0.9999', '0.99999999']]
worst = dict(count=0, Bi=0, Bii=0, tr=0, dom=0, wrong=0, real=0)
for I in insts:
    M, r = I.M, I.r
    for tau in taus:
        for k in range(4):
            c = mp.mpc(rng.normal()*2, float(rng.choice([1e-9, 1e-3, 0.3, 4.0])))
            ys = I.roots(tau, c)
            up = [y for y in ys if mp.im(y) > 0]; dn = [y for y in ys if mp.im(y) < 0]
            if len(up) != M - r or len(dn) != r:
                worst['count'] += 1
            K = I.normH + abs(c)
            worst['Bi'] = max(worst['Bi'], max(abs(y)*min(tau, 1 - tau)/K for y in ys))
            side = up if tau <= mp.mpf(1)/2 else dn
            if side:
                worst['Bii'] = max(worst['Bii'], max(abs(y)*mp.sqrt(tau*(1 - tau))/K for y in side))
            other = dn if tau <= mp.mpf(1)/2 else up
            if other:
                worst['wrong'] = max(worst['wrong'], max(abs(y)*mp.sqrt(tau*(1 - tau))/K for y in other))
            Sp = sum(up, mp.mpc(0)); Sm = sum(dn, mp.mpc(0))
            trd = abs(Sp + Sm - I.S0_plus(tau, c) - I.S0_minus(tau, c))/(1 + abs(Sp) + abs(Sm))
            worst['tr'] = max(worst['tr'], trd)
            dom = abs(Sp - I.S0_plus(tau, c))/(M*K*(2 + 1/mp.sqrt(tau*(1 - tau))))
            worst['dom'] = max(worst['dom'], dom)
        # real c: Lemma 1(b) of Q_2bmv
        c0 = mp.mpf(rng.normal()*2)
        nrm = max(abs(l + c0) for l in I.lam)
        for y in I.roots(tau, c0):
            if abs(mp.im(y)) > mp.mpf(10)**(-15):
                worst['real'] = max(worst['real'], abs(y)*mp.sqrt(tau*(1 - tau))/nrm)

print(f'instances: {len(insts)}, tau values: {len(taus)}, 4 complex c per (instance, tau)')
print(f'Lemma A: number of (instance,tau,c) with wrong C_+/C_- count: {worst["count"]}   (expect 0)')
print(f'Lemma B(i):   max |y| min(tau,1-tau)/K            = {mp.nstr(worst["Bi"], 8)}   (expect <= 1)')
print(f'Lemma B(ii):  max |y| sqrt(tau(1-tau))/K, right side = {mp.nstr(worst["Bii"], 8)}   (expect <= 1)')
print(f'   same ratio for the WRONG half plane (no bound)    = {mp.nstr(worst["wrong"], 8)}   (unbounded as tau -> 0,1)')
print(f'trace identity: max rel. defect                    = {mp.nstr(worst["tr"], 3)}')
print(f'domination: max |S_+ - S0_+| / (M K (2 + (tau(1-tau))^-1/2)) = {mp.nstr(worst["dom"], 8)}   (expect <= 1)')
print(f'real c, Lemma 1(b): max |y| sqrt(tau(1-tau))/||H+c|| over non-real roots = {mp.nstr(worst["real"], 8)}   (expect <= 1)')
ok = worst['count'] == 0 and worst['Bi'] <= 1 and worst['Bii'] <= 1 and worst['dom'] <= 1 and worst['real'] <= 1 and worst['tr'] < 1e-20
print('ALL OK' if ok else 'FAILURE')
