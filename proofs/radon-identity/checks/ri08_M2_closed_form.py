"""ri08: M = 2 by explicit integration (PROOF.md Remark 3.2).

H = [[alpha, gamma], [conj gamma, beta]], P = diag(1, 0) (alpha = PHP entry, beta = BHB entry).
  sum_i |Im y_i(tau)| = sqrt(4 tau(1-tau)|gamma|^2 - m(tau)^2)_+ / (tau(1-tau)),   m(tau) = alpha tau + beta(1 - tau),
and the substitution rho = tau/(1-tau) plus  int_a^b sqrt((x-a)(b-x))/(x + d) dx = (pi/2)(sqrt(b+d) - sqrt(a+d))^2  give
  L(H) = (1/2)( sqrt((alpha - beta)^2 + 4|gamma|^2) - |alpha| - |beta| )_+  =  Tr H_+ - alpha_+ - beta_+ = R(H).
Checked: (i) the integrand formula pointwise, (ii) L by quadrature vs the closed form vs R, random and edge cases.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
from ri_core import Inst

mp.mp.dps = 30
rng = np.random.default_rng(12)
cases = []
for k in range(10):
    a, b = rng.normal(size=2)*2; g = complex(rng.normal(), rng.normal())
    cases.append((a, b, g))
cases += [(0.0, 0.0, 1.0 + 0j), (1.0, 2.0, 0.5 + 0j), (1.0, 2.0, np.sqrt(2.0) + 0j), (1.0, 2.0, 2.0 + 0j), (-1.0, 3.0, 0.1j),
          (0.0, 2.0, 0.3 + 0.4j), (-2.0, -1.0, 1.0 + 0j), (1.0, 1.0, 1e-3 + 0j), (5.0, -0.2, 0.0 + 0j)]
worst_int = mp.mpf(0); worst = mp.mpf(0)
for (a, b, g) in cases:
    H = np.array([[a, g], [np.conj(g), b]], dtype=complex)
    I = Inst(H, 1)
    al, be, ga2 = mp.mpf(a), mp.mpf(b), mp.mpf(complex(g).real)**2 + mp.mpf(complex(g).imag)**2
    for tau in [mp.mpf('0.03'), mp.mpf('0.4'), mp.mpf('0.77')]:
        m = al*tau + be*(1 - tau)
        f = mp.sqrt(max(4*tau*(1 - tau)*ga2 - m**2, 0))/(tau*(1 - tau))
        worst_int = max(worst_int, abs(I.imsum(tau) - f))
    closed = max(mp.sqrt((al - be)**2 + 4*ga2) - abs(al) - abs(be), 0)/2
    Lv = I.L(0) if abs(g) > 0 else mp.mpf(0)
    Rv = I.R(0)
    worst = max(worst, abs(Lv - closed), abs(Rv - closed))
    print(f'  alpha={a:+.4f} beta={b:+.4f} |gamma|^2={abs(g)**2:.4f}:  L={mp.nstr(Lv, 20):>24s}  closed={mp.nstr(closed, 20):>24s}  R={mp.nstr(Rv, 20):>24s}')
print(f'integrand formula: max abs error {mp.nstr(worst_int, 3)};  max |L - closed|, |R - closed| = {mp.nstr(worst, 3)}')
print('ALL OK' if worst < 1e-20 and worst_int < 1e-20 else 'CHECK')
