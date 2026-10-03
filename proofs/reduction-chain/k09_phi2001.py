"""Item 5, regime boundary 2000/2001: from the decoupled solution Phi_* at d = 2001 (midpoints dumped by the programme's verifier run on a
copy, spot/logs/phi_d2001.json), recompute with independent code (mpmath, 50 digits) the variogram coefficients at_k (all k) and compare
with the regime-3 claim at_k >= 0.1187 w_k eps^2 (CONE_ALLD_PROOF.md s.11) and the regime-2 log; and D_B(1), D_B(2) vs s.7."""
import json, mpmath as mp
mp.mp.dps = 50
r = json.load(open('spot/logs/phi_d2001.json')); d = r['d']
Phi = [mp.mpf(x) for x in r['Phi']]            # m = 0..d-1, symmetric
eps = mp.mpf(1) / d
A0 = mp.pi / 2 - 1
def f(b):
    b = mp.mpf(b)
    if b == 0: return mp.mpf(0)
    B = b * (2 * mp.psi(1, b + 1) + b * mp.psi(2, b + 1))
    return b * b * (1 / B - 1)
fd = f(d)
FA = [A0 * eps * (f(m) + f(d - m) - fd) if m else mp.mpf(0) for m in range(d)]
X = [Phi[m] - FA[m] for m in range(d)]
D4 = lambda Y, m: Y[(m - 2) % d] - 4 * Y[(m - 1) % d] + 6 * Y[m % d] - 4 * Y[(m + 1) % d] + Y[(m + 2) % d]
print(f"d = {d}: D_B[Phi_*](1)/eps^2 = {mp.nstr(D4(X, 1) / eps**2, 8)} (s.7 model bound >= -2.7652);  D_B(2)/eps^3 = {mp.nstr(D4(X, 2) / eps**3, 8)} (model >= 206.88)")
print("   D_B(m)/eps^3 for m = 3,4,5,10,50,200,1000:", [mp.nstr(D4(X, m) / eps**3, 6) for m in (3, 4, 5, 10, 50, 200, 1000)])
cs = [mp.cos(2 * mp.pi * j / d) for j in range(d)]
mn = None
for k in range(1, d // 2 + 1):
    s = mp.fsum(Phi[m] * cs[(k * m) % d] for m in range(1, d))
    a = -(mp.mpf(2) / d) * s
    if mn is None or a < mn[0]: mn = (a, k)
print(f"   min_k at_k(Phi_*) d^2 = {mp.nstr(mn[0] * d * d, 8)} at k = {mn[1]}  (regime-3 claim >= 0.1187; regime-2 log 0.1264)")
