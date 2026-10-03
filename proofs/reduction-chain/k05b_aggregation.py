"""Item 5, Lemma R3 (corrected test; the first test in k05 compared two Monte-Carlo estimates and was noise-limited at ~1e-2):
for FIXED eta (in E), the Dirichlet aggregation gives  E[u^ell | eta] = Delta^2_m (1/d) sum_r F(B_r(m)),  B_r(m) = beta_r + .. + beta_{r+m-1},
beta = 1 + eta.  Monte Carlo over 300000 Dirichlet draws vs quadrature of F.  Plus: convexity of a(m) = 1/6 - f(m) (QD2-L12) for
0 <= m <= 400 in 40-digit arithmetic (the double-precision test in k05 is meaningless beyond m ~ 100)."""
import numpy as np, mpmath as mp
from scipy import integrate, stats
from k05_cone_lemmas_core import cl2
PI = np.pi
rng = np.random.default_rng(99)
d = 10; N = 4 * d
Ghat = lambda u: -(N ** 2 / (2 * PI ** 2)) * (cl2(2 * PI * np.asarray(u, float) / N) + cl2(PI - 2 * PI * np.asarray(u, float) / N))
def u_window(ell):
    e2 = np.concatenate([ell, ell]); cs = np.concatenate([[0.0], np.cumsum(e2)])
    r = np.arange(d)[:, None]; m = np.arange(d + 1)[None, :]
    P = Ghat(cs[r + m] - cs[r]).mean(axis=0)
    return P[2:] - 2 * P[1:-1] + P[:-2]
def F(b):
    if b <= 0: return float(Ghat(0.0))
    if b >= d: return float(Ghat(float(d)))
    f = lambda x: Ghat(d * x) * stats.beta.pdf(x, b, d - b)
    pts = [p for p in [(b - 1) / (d - 2)] if 0.01 < p < 0.99]
    return integrate.quad(f, 0, 1, points=pts or None, limit=400, epsabs=1e-12, epsrel=1e-12)[0]
for trial in range(3):
    eta = rng.uniform(-0.5, 0.5, d); eta -= eta.mean()           # any eta in E with sum 0 (law of eta irrelevant here)
    beta = 1 + eta
    ns = 300000
    U = np.array([u_window(rng.dirichlet(beta) * d) for _ in range(ns)])
    mean = U.mean(0); se = U.std(0) / np.sqrt(ns)
    b2 = np.concatenate([beta, beta])
    P = [F(0)] + [np.mean([F(b2[r:r + m].sum()) for r in range(d)]) for m in range(1, d)] + [F(d)]
    P = np.array(P); pred = P[2:] - 2 * P[1:-1] + P[:-2]
    z = (mean - pred) / se
    print(f"trial {trial}: max |MC - Delta^2 (1/d) sum_r F(B_r(m))| / SE = {np.abs(z).max():.2f}  (z-scores {np.round(z, 2)})", flush=True)
mp.mp.dps = 40
def f(b):
    b = mp.mpf(b)
    if b == 0: return mp.mpf(0)
    B = b * (2 * mp.psi(1, b + 1) + b * mp.psi(2, b + 1))
    return b * b * (1 / B - 1)
a = [mp.mpf(1) / 6 - f(m) for m in range(0, 402)]
d2 = [a[m - 1] - 2 * a[m] + a[m + 1] for m in range(1, 401)]
print(f"QD2-L12: a(0)-2a(1)+a(2) = 2f(1)-f(2) = {mp.nstr(2 * f(1) - f(2), 10)};  min_(1<=m<=400) Delta^2 a(m) = {mp.nstr(min(d2), 6)} (all > 0: {all(x > 0 for x in d2)});"
      f"  a(m) > 0 for m <= 401: {all(x > 0 for x in a[1:])};  max m^2 a(m) = {mp.nstr(max(m * m * a[m] for m in range(1, 402)), 8)} (13/180 = {13/180:.8f})")
