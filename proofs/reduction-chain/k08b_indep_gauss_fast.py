"""Item 5 (faster variant k08b: F interpolated on 64 Chebyshev nodes per window [b - L, b + L], nodes from direct quadrature): independent re-implementation of the regime-2 (Gaussian-modulation) construction at a small d, to cross-check the
programme's verifier (QD2/verify_gauss.py, run on a copy in spot/) by a DIFFERENT method:
  F(b) = E Ghat(d X_b) by direct quadrature over the Beta(b, d-b) density (no series, no polygamma formulas);
  P_v  = discrete Dirichlet potential of v_m = 2 csc(pi m/2d) with P_v(0) = Ghat(0), P_v(d) = Ghat(d) (no singular/regular split);
  H(m,t) = E[F(m+Z); |Z| < L] + F(m) P(|Z| >= L), Z ~ N(0,t), by Gauss-Legendre in z (no Taylor expansion of F);
  Phi_*(m): secant root of Hc_m(t) = tau_m;  at_k(Phi_*), slack w = Delta^2 W, W = (P_v - H(., Phi_*))_S.
Usage: python k08_indep_gauss.py d
"""
import sys, numpy as np, mpmath as mp
mp.mp.dps = 25
d = int(sys.argv[1]) if len(sys.argv) > 1 else 50
N = 4 * d
pref = -(mp.mpf(N) ** 2) / (2 * mp.pi ** 2)
Gh = lambda u: pref * (mp.clsin(2, 2 * mp.pi * u / N) + mp.clsin(2, 2 * mp.pi * (2 * d - u) / N))
Fc = {}


def F(b):
    b = mp.mpf(b)
    key = mp.nstr(b, 22)
    if key in Fc:
        return Fc[key]
    if b <= 0:
        val = Gh(0)
    elif b >= d:
        val = Gh(d)
    else:
        lb = mp.log(mp.beta(b, d - b))
        dens = lambda x: mp.exp((b - 1) * mp.log(x) + (d - b - 1) * mp.log(1 - x) - lb)
        mode = min(max((b - 1) / (d - 2), mp.mpf(0.02)), mp.mpf(0.98)) if d > 2 else mp.mpf(0.5)
        sd = mp.sqrt(b * (d - b) / (d * d * (d + 1)))
        pts = sorted(set([mp.mpf(0)] + [p for p in [mode - 8 * sd, mode, mode + 8 * sd] if 0 < p < 1] + [mp.mpf(1)]))
        val = mp.quad(lambda x: Gh(d * x) * dens(x), pts)
    Fc[key] = val
    return val


Fm0 = {}
XG, WG = np.polynomial.legendre.leggauss(64)
XG = [mp.mpf(x) for x in XG]; WG = [mp.mpf(w) for w in WG]


NCH = 64
CHEB = {}


def cheb_window(b):
    """Chebyshev interpolant of F on [b - L, b + L], L = 3 min(b, d-b)/4 (F analytic there; nearest singularity at 0 or d)."""
    if b not in CHEB:
        L = mp.mpf(3) * min(b, d - b) / 4
        th = [mp.pi * (j + mp.mpf(1) / 2) / NCH for j in range(NCH)]
        xs = [mp.cos(t) for t in th]
        fs = [F(b + L * x) for x in xs]
        ws = [(-1) ** j * mp.sin(t) for j, t in enumerate(th)]
        CHEB[b] = (L, xs, fs, ws)
    return CHEB[b]


def Fint(b, z):
    L, xs, fs, ws = cheb_window(b)
    x = z / L
    num = mp.mpf(0); den = mp.mpf(0)
    for xj, fj, wj in zip(xs, fs, ws):
        if x == xj:
            return fj
        c = wj / (x - xj); num += c * fj; den += c
    return num / den


def HmF(m, t):
    """H(m,t) - F(m)  with truncation |Z| < L = 3 min(m, d-m)/4 (exactly as Lemma R4)."""
    L = mp.mpf(3) * min(m, d - m) / 4
    s = mp.sqrt(t)
    Lz = min(L, 14 * s)                                   # beyond 14 sd the Gaussian mass is < 1e-44
    acc = mp.mpf(0)
    for x, w in zip(XG, WG):
        z = Lz * x
        acc += w * Lz * (Fint(m, z) - Fm0[m]) * mp.exp(-z * z / (2 * t)) / mp.sqrt(2 * mp.pi * t)
    return acc


# discrete potential of v with boundary values Ghat(0), Ghat(d)
v = [None] + [2 / mp.sin(mp.pi * m / (2 * d)) for m in range(1, d)]
P0, Pd = Gh(0), Gh(d)
Pv = [mp.mpf(0)] * (d + 1)
for m in range(d + 1):
    s = (d - mp.mpf(m)) / d * P0 + mp.mpf(m) / d * Pd
    for j in range(1, d):
        Gmj = mp.mpf(min(m, j)) * (d - max(m, j)) / d
        s -= Gmj * v[j]
    Pv[m] = s
for m in range(1, d):
    Fm0[m] = Fint(m, mp.mpf(0))
Dlt = [Pv[m] - F(m) for m in range(d + 1)]
print('max |Chebyshev(F)(m) - F(m)| =', mp.nstr(max(abs(Fm0[m] - F(m)) for m in range(1, d)), 3), flush=True)
Phi = {0: mp.mpf(0)}
half = (d - 1) // 2
for m in range(1, half + 1):
    tau = Dlt[m] - Dlt[d - m]
    Hc = lambda t: HmF(m, t) - HmF(d - m, t) - tau
    t0 = mp.mpf(0.64) * m * m / d * (1 - mp.mpf(m) / d)       # rough start
    t1 = t0 * mp.mpf(1.05)
    f0, f1 = Hc(t0), Hc(t1)
    for it in range(30):
        t2 = t1 - f1 * (t1 - t0) / (f1 - f0)
        if t2 <= 0:
            t2 = t1 / 2
        t0, f0, t1, f1 = t1, f1, t2, Hc(t2)
        if abs(t1 - t0) < mp.mpf(10) ** -18 * t1:
            break
    Phi[m] = t1
    Phi[d - m] = t1
if d % 2 == 0:
    h2 = d // 2
    Phi[h2] = (15 * Phi[h2 - 1] - 6 * Phi[h2 - 2] + Phi[h2 - 3]) / 10
at = []
for k in range(1, d // 2 + 1):
    s = sum(Phi[m] * mp.cos(2 * mp.pi * k * m / d) for m in range(d))
    wk = mp.mpf(2) / d if 2 * k != d else mp.mpf(1) / d
    at.append(-wk * s)
W = [mp.mpf(0)] * (d + 1)
for m in range(1, d):
    W[m] = ((Pv[m] - F(m) - HmF(m, Phi[m])) + (Pv[d - m] - F(d - m) - HmF(d - m, Phi[d - m]))) / 2
w = [W[m + 1] - 2 * W[m] + W[m - 1] for m in range(1, d)]
print(f"d={d}: Phi(1) d = {mp.nstr(Phi[1] * d, 8)};  min at_k = {mp.nstr(min(at), 8)} (d^2 min = {mp.nstr(min(at) * d * d, 6)}, k = {1 + at.index(min(at))});"
      f"  min w = {mp.nstr(min(w), 8)} (d min = {mp.nstr(min(w) * d, 6)})")
print("Phi(1..5) =", [mp.nstr(Phi[m], 15) for m in range(1, 6)])
