"""ri04: Lemma D (endpoint limits in tau) and the branch constant (PROOF.md s.1-2).

For Im c > 0:
  tau -> 1:  (1 - tau) * (C_+ roots) -> spec(PHP + c | ran P),  hence  Lam_+ - Lam0_+ -> 0;
  tau -> 0:  C_+ roots -> spec T_0,  T_0 = PHP + c - PHB (BHB + c)^{-1} BHP  (Schur complement on ran P),
             hence  Lam_+ - Lam0_+ -> Theta(c) := sum Log(spec T_0) - sum_k Log(mu_k + c),
             exp Theta(c) = det(H + c)/det(H_d + c).
  Branch constant:  Theta(c) = Theta_1(c) := sum_j Log(lam_j + c) - sum_j Log(lam0_j + c)   (k = 0 in PROOF.md, Step 2).
The convergence rates are printed (expected O(1 - tau) and O(tau)).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst, standard_instances, eigvals

mp.mp.dps = 40
rng = np.random.default_rng(99)
insts = standard_instances()

def schur_T0(I, c):
    M, r = I.M, I.r
    A = I.H + c*mp.eye(M)
    App = mp.matrix(M - r, M - r); Apb = mp.matrix(M - r, r); Abp = mp.matrix(r, M - r); Abb = mp.matrix(r, r)
    for i in range(M):
        for j in range(M):
            if i < M - r and j < M - r: App[i, j] = A[i, j]
            elif i < M - r: Apb[i, j - (M - r)] = A[i, j]
            elif j < M - r: Abp[i - (M - r), j] = A[i, j]
            else: Abb[i - (M - r), j - (M - r)] = A[i, j]
    return App - Apb*mp.inverse(Abb)*Abp

def match_dist(a, b):
    """max distance under the best greedy matching of two equal-size multisets."""
    b = list(b); d = mp.mpf(0)
    for x in a:
        j = min(range(len(b)), key=lambda k: abs(b[k] - x)); d = max(d, abs(b[j] - x)); b.pop(j)
    return d

worst_br = mp.mpf(0); worst_exp = mp.mpf(0)
for I in insts:
    c = mp.mpc(rng.normal(), rng.uniform(0.1, 1.5))
    T0 = schur_T0(I, c)
    t0spec = eigvals(T0)
    Theta = sum((mp.log(z) for z in t0spec), mp.mpc(0)) - sum((mp.log(m + c) for m in I.mu), mp.mpc(0))
    lhs = mp.exp(Theta); rhs = mp.det(I.H + c*mp.eye(I.M))/mp.det(I.Hd + c*mp.eye(I.M))
    worst_exp = max(worst_exp, abs(lhs - rhs)/abs(rhs))
    worst_br = max(worst_br, abs(Theta - I.Theta1(c)))
    line1 = []; line0 = []
    for k in [2, 4, 6, 8]:
        e = mp.mpf(10)**(-k)
        up1, _ = I.split(1 - e, c)
        d1 = match_dist([e*y for y in up1], [m + c for m in I.mu])
        D1 = abs(I.Lam_plus(1 - e, c) - I.Lam0_plus(1 - e, c))
        up0, _ = I.split(e, c)
        d0 = match_dist(up0, t0spec)
        D0 = abs(I.Lam_plus(e, c) - I.Lam0_plus(e, c) - Theta)
        line1.append(f'{mp.nstr(D1, 2)}'); line0.append(f'{mp.nstr(D0, 2)}')
    print(f'{I.name:18s} c={mp.nstr(c, 4):>22s}  |Lam_+-Lam0_+| at tau=1-1e-2,-4,-6,-8: {", ".join(line1)}')
    print(f'{"":18s} {"":24s}  |Lam_+-Lam0_+-Theta| at tau=1e-2,-4,-6,-8: {", ".join(line0)}')
print(f'exp(Theta) = det(H+c)/det(H_d+c): max rel. error {mp.nstr(worst_exp, 3)}')
print(f'Theta = Theta_1 (branch constant k = 0): max |Theta - Theta_1| = {mp.nstr(worst_br, 3)}')
print('ALL OK' if worst_exp < 1e-30 and worst_br < 1e-30 else 'CHECK')
