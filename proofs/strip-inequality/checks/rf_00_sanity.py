# rf_00: sanity of the referee's own machinery on M = 2 (closed form of Remark 4.4) and M = 3 tau-marginals.
import numpy as np, mpmath as mp, time
from rf_core import *

rng = np.random.default_rng(1)
al, be, c = 0.3, -1.1, 0.7*np.exp(0.4j)
B = np.diag([1.0, 0.0]).astype(complex); g = np.array([[al, c], [np.conj(c), be]])
for tau in [0.01, 0.3, 0.77, 0.999]:
    s = np.linspace(-3, 3, 7)
    m = tau*be + (1 - tau)*al
    Fc = np.sqrt(np.maximum(4*tau*(1 - tau)*abs(c)**2 - (s - m)**2, 0))/(2*PI*tau*(1 - tau))
    Fn = F_vals(B, g, s, tau)
    cv, lmin, lmax = crit_values(B, g, tau)
    print(f"M=2 tau={tau}: max|F_num - F_closed| = {np.max(abs(Fn - Fc)):.2e}; branch pts {cv} vs {m - 2*abs(c)*np.sqrt(tau*(1-tau)):.12f},{m + 2*abs(c)*np.sqrt(tau*(1-tau)):.12f}")
    J = J_slice(B, g, tau, np.array([0.0]))
    print(f"      int F ds = {J[0].real:.15f}  vs |c|^2 = {abs(c)**2:.15f}")

for M, r in [(3, 1), (4, 2), (5, 2)]:
    B, g = rand_inst(M, r, 1.0, rng)
    P = np.eye(M) - B
    bgp = np.linalg.norm(B @ g @ P)**2
    t0 = time.time()
    vals = [J_slice(B, g, tau, np.array([0.0]))[0].real for tau in [1e-4, 0.05, 0.3, 0.5, 0.71, 0.95, 1 - 1e-4]]
    print(f"M={M} r={r}: ||BgP||_F^2 = {bgp:.15f}; marginals - that: {[f'{v - bgp:.1e}' for v in vals]}  ({time.time()-t0:.2f}s)")
