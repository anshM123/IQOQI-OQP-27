"""Referee check, item 5 (independent numerics for the lemmas behind the d >= 201 certificates; float64, own code):
 (i)   Lemma R3 (direction of the Gaussian-modulated Dirichlet process Pi_Phi), Monte Carlo at d = 10:
         E_mu[u^ell] = Delta^2 P,  P(m) = E[F(m + Z(m)); E] + P(E^c) F(m),  F(b) = E Ghat(d X_b), X_b ~ Beta(b, d-b);
 (ii)  QD2-L11 identity  8 d s^4 at_k(X) = sum_{m=1}^{d-1} Delta^4 X(m) (1 - cos m th)  (symmetric X, X(0) = 0, periodic);
 (iii) boundary layer: at_k(F_A) >= w_k * 2 A0 (A_min - 0.1446/(d-1)) eps^2 with A_min >= 0.105487 (QD2-L12), d = 2001..;
       and A(th) = a(0) + 2 sum a(m) cos(m th) >= 0.105487 (a = 1/6 - f, f(b) = b^2 (1/B - 1), B = b[2 psi'(b+1) + b psi''(b+1)]).
"""
import numpy as np
from scipy import integrate, stats, special
rng = np.random.default_rng(777)
PI = np.pi


def bern_c(n0=30):
    out = []
    for n in range(1, n0 + 1):
        B = abs(special.bernoulli(2 * n)[-1])
        out.append(B / (2 * n * special.factorial(2 * n + 1)))
    return np.array(out)


CN = bern_c()


def cl2(t):
    """Clausen Cl2 on [0, pi] (vectorised series)."""
    t = np.asarray(t, float)
    out = np.where(t > 0, t - t * np.log(np.where(t > 0, t, 1.0)), 0.0)
    pw = t ** 3
    t2 = t * t
    for c in CN:
        out = out + c * pw
        pw = pw * t2
    return out


def Ghat(u, d):
    N = 4 * d
    x = 2 * PI * np.asarray(u, float) / N            # in [0, pi/2] for u in [0, d]
    return -(N ** 2 / (2 * PI ** 2)) * (cl2(x) + cl2(PI - x))


def u_window(ell, d):
    e2 = np.concatenate([ell, ell])
    cs = np.concatenate([[0.0], np.cumsum(e2)])
    r = np.arange(d)[:, None]; m = np.arange(d + 1)[None, :]
    S = cs[r + m] - cs[r]
    P = Ghat(S, d).mean(axis=0)
    return P[2:] - 2 * P[1:-1] + P[:-2]


# (i) ------------------------------------------------------------------------------------------------------------
d = 10
# a valid variogram: Phi(m) = sum_k a_k (1 - cos(2 pi k m/d)), a_k >= 0  (k = 1, 2, 3)
amp = {1: 0.05, 2: 0.02, 3: 0.01}
mm = np.arange(d + 1)
Phi = sum(a * (1 - np.cos(2 * PI * k * mm / d)) for k, a in amp.items())
# covariance c(j) = Delta^2 Phi(j)/2 (periodic)
Php = np.concatenate([Phi[:d], Phi[:d]])
c = np.array([(Phi[(j + 1) % d] - 2 * Phi[j % d] + Phi[(j - 1) % d]) / 2 for j in range(d)])
C = np.array([[c[(i - j) % d] for j in range(d)] for i in range(d)])
w_, V_ = np.linalg.eigh(C)
assert w_.min() > -1e-12, w_.min()
Lc = V_ @ np.diag(np.sqrt(np.maximum(w_, 0)))
ns = 400000
eta = rng.standard_normal((ns, d)) @ Lc.T
inE = np.abs(eta).max(axis=1) < 0.75
print(f"(i) d = {d}: Var eta_0 = {eta[:, 0].var():.5f} (Phi(1) = {Phi[1]:.5f}); sum eta = {np.abs(eta.sum(1)).max():.1e}; P(E^c) ~ {1 - inE.mean():.4f}")
# Monte Carlo of E u^ell
acc = np.zeros(d - 1)
for i in range(ns):
    beta = 1 + eta[i] if inE[i] else np.ones(d)
    ell = rng.dirichlet(beta) * d
    acc += u_window(ell, d)
uMC = acc / ns
# formula: F(b) by quadrature
Fcache = {}


def F(b):
    if b <= 0:
        return float(Ghat(0.0, d))
    if b >= d:
        return float(Ghat(float(d), d))
    f = lambda x: Ghat(d * x, d) * stats.beta.pdf(x, b, d - b)
    return integrate.quad(f, 0, 1, limit=200, epsabs=1e-11, epsrel=1e-11)[0]


Z = np.cumsum(eta, axis=1)                            # Z(m) = eta_0 + .. + eta_{m-1}, m = 1..d
P = np.zeros(d + 1)
P[0], P[d] = F(0), F(d)
nsub = 4000                                           # subsample for the E-part (F is smooth; error ~ 1e-3 relative)
idx = rng.choice(ns, nsub, replace=False)
for m in range(1, d):
    vals = np.array([F(m + Z[i, m - 1]) if inE[i] else F(m) for i in idx])
    P[m] = vals.mean()
uF = P[2:] - 2 * P[1:-1] + P[:-2]
v = 2 / np.sin(PI * np.arange(1, d) / (2 * d))
# Monte-Carlo standard error of uMC (batch estimate)
print("    m:        " + " ".join(f"{m:8d}" for m in range(1, d)))
print("    E u (MC): " + " ".join(f"{x:8.4f}" for x in uMC))
print("    Delta^2P: " + " ".join(f"{x:8.4f}" for x in uF))
print("    v:        " + " ".join(f"{x:8.4f}" for x in v))
print(f"    max |E u - Delta^2 P| / max|v| = {np.abs(uMC - uF).max() / v.max():.2e}  (MC + subsample noise ~ 1e-3 expected)")

# (ii) -----------------------------------------------------------------------------------------------------------
err = 0
for d in [7, 10, 33, 64]:
    X = np.zeros(d)
    half = rng.standard_normal(d // 2 + 1)
    for m in range(1, d):
        X[m] = half[min(m, d - m)]
    D4 = np.array([X[(m - 2) % d] - 4 * X[(m - 1) % d] + 6 * X[m] - 4 * X[(m + 1) % d] + X[(m + 2) % d] for m in range(d)])
    for k in range(1, d // 2 + 1):
        th = 2 * PI * k / d; s = np.sin(th / 2)
        wk = 1.0 if 2 * k != d else 0.5
        at = -wk * (2 / d) * np.sum(X * np.cos(th * np.arange(d)))
        rhs = np.sum(D4[1:] * (1 - np.cos(np.arange(1, d) * th)))
        err = max(err, abs(8 * d * s ** 4 * at / wk - rhs) / max(1, abs(rhs)))
print(f"(ii) QD2-L11 identity: max relative error {err:.1e}")

# (iii) ----------------------------------------------------------------------------------------------------------
A0 = PI / 2 - 1


def fB(b):
    b = np.asarray(b, float)
    B = b * (2 * special.polygamma(1, b + 1) + b * special.polygamma(2, b + 1))
    return b ** 2 * (1 / B - 1)


mbig = np.arange(1, 200001)
a = 1 / 6 - fB(mbig)
th = np.linspace(1e-4, PI, 4001)
A = 1 / 6 + 2 * np.array([np.sum(a[:20000] * np.cos(mbig[:20000] * t)) + 0 for t in th[::40]])
print(f"(iii) a(m) = 1/6 - f(m): a(1..4) = {a[:4]}, convex on 1..2000: {bool(np.all(np.diff(a[:2000], 2) >= -1e-15))}; "
      f"min_th A(th) (truncated at m = 2e4, coarse grid) = {A.min():.6f}; 2 f(1) - f(2) = {2 * fB(1) - fB(2):.6f}")
for d in [2001, 2002, 3001, 5000]:
    eps = 1 / d
    m = np.arange(d)
    fm = np.where(m > 0, fB(np.maximum(m, 1)), 0.0)
    fdm = fB(d - m)
    FA = A0 * eps * (fm + fdm - fB(d))
    FA[0] = 0.0                                       # F_A(0) = A0 eps [f(0) + f(d) - f(d)] = 0
    at = -(2 / d) * np.real(np.fft.fft(FA))[1:d // 2 + 1]
    if d % 2 == 0:
        at[-1] /= 2
    wk = np.ones(len(at)); wk[-1] = 0.5 if d % 2 == 0 else 1.0
    bound = 2 * A0 * (0.105487 - 0.1446 / (d - 1)) * eps ** 2
    print(f"    d = {d}: min_k at_k(F_A)/(w_k eps^2) = {np.min(at / wk) / eps ** 2:.5f}  vs claimed lower bound {bound / eps ** 2:.5f}")
