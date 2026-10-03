"""q04: broad float stress sweep of Theorem 1 (closed form nu_2 = (1/2pi) sum |Im x_i|) at large / clustered / near-commuting
configurations, M = 3..6, scales up to 300.  For each configuration:
  (i)  tau-marginal  int nu_2(s,tau) ds = ||BgP||_F^2   at 2 random tau,
  (ii) Radon slice   int_0^1 nu_2(w + xi tau, tau) dtau = U_xi(w)   at 2 random (xi, w),
  (iii) the Laplace identity D(a,t)/a^2 = int int e^{as - t tau} nu_2 at one (a,t) (a scaled to the spectrum width).
Adaptive quadrature (scipy quad) with breakpoints at root collisions (grid + bisection); tau = sin^2(theta) at the edges.
usage: python q04_stress_sweep.py seed n"""
import numpy as np, sys, time
from scipy.integrate import quad
from q_core import U_float, D_float

def roots(g, B, s, tau, eps):
    M = g.shape[0]; P = np.eye(M) - B
    return np.linalg.eigvals((P/eps - B/tau) @ (g - s*np.eye(M)))

def Fv(g, B, s, tau, eps):
    return np.sum(np.abs(roots(g, B, s, tau, eps).imag))/(2*np.pi)

def cnt(g, B, s, tau, eps):
    x = roots(g, B, s, tau, eps); sc = max(1.0, np.max(np.abs(x)))
    return int(np.sum(np.abs(x.imag) > 1e-8*sc))

def breaks(fc, u0, u1, n):
    us = np.linspace(u0, u1, n); cs = [fc(u) for u in us]; out = []
    for k in range(n - 1):
        if cs[k] != cs[k + 1]:
            a, b = us[k], us[k + 1]; ca = cs[k]
            for _ in range(55):
                m = (a + b)/2
                if fc(m) == ca: a = m
                else: b = m
            out.append((a + b)/2)
    return out

def integrate(f, edges):
    tot = 0.0
    for a, b in zip(edges[:-1], edges[1:]):
        if b - a > 1e-15:
            tot += quad(f, a, b, limit=500, epsabs=1e-13, epsrel=1e-11)[0]
    return tot

def tau_marginal(g, B, tau):
    eps = 1 - tau; lo, hi = np.linalg.eigvalsh(g)[[0, -1]]
    bp = breaks(lambda s: cnt(g, B, s, tau, eps), lo, hi, 4000)
    return integrate(lambda s: Fv(g, B, s, tau, eps), [lo] + bp + [hi])

def radon(g, B, xi, w):
    # theta-parametrisation: tau = sin^2 th, eps = cos^2 th, dtau = sin(2th) dth
    f = lambda th: Fv(g, B, w + xi*np.sin(th)**2, np.sin(th)**2, np.cos(th)**2)*np.sin(2*th) if 0 < th < np.pi/2 else 0.0
    c = lambda th: cnt(g, B, w + xi*np.sin(th)**2, np.sin(th)**2, np.cos(th)**2) if 0 < th < np.pi/2 else -1
    bp = breaks(c, 1e-9, np.pi/2 - 1e-9, 4000)
    return integrate(f, [0.0] + bp + [np.pi/2])

def laplace(g, B, a, t, ntau=160):
    """int int e^{as - t tau} nu_2 : Gauss-Legendre in theta (tau = sin^2 theta), adaptive in s."""
    lo, hi = np.linalg.eigvalsh(g)[[0, -1]]
    xt, wt = np.polynomial.legendre.leggauss(ntau); th = (np.pi/4)*(xt + 1); wt = wt*np.pi/4
    tot = 0.0
    for thk, wk in zip(th, wt):
        tau, eps = np.sin(thk)**2, np.cos(thk)**2
        bp = breaks(lambda s: cnt(g, B, s, tau, eps), lo, hi, 1500)
        tot += wk*np.sin(2*thk)*np.exp(-t*tau)*integrate(lambda s: np.exp(a*s)*Fv(g, B, s, tau, eps), [lo] + bp + [hi])
    return tot

def make(rng, k):
    M = int(rng.integers(3, 7)); r = int(rng.integers(1, M))
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); Q, _ = np.linalg.qr(Z); B = Q[:, :r] @ Q[:, :r].conj().T
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); W, _ = np.linalg.qr(Z)
    kind = ['big', 'cluster', 'nearcomm', 'wide', 'twoscale'][k % 5]
    if kind == 'big':          # one huge eigenvalue (the t03 mechanism)
        ev = rng.normal(size=M)*3; ev[-1] = rng.choice([-1, 1])*rng.uniform(50, 300)
        g = (W*ev) @ W.conj().T
    elif kind == 'cluster':    # all eigenvalues of g within 1e-3 of a large centre, one far
        ev = rng.uniform(20, 200) + 1e-3*rng.normal(size=M); ev[0] = rng.normal()*5
        g = (W*ev) @ W.conj().T
    elif kind == 'nearcomm':   # nearly commuting: tiny off-diagonal block, large diagonal blocks
        G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); G = 50*(G + G.conj().T)/2
        P = np.eye(M) - B; gd = B @ G @ B + P @ G @ P; go = G - gd; g = gd + 1e-3*go
    elif kind == 'wide':       # all eigenvalues of size up to 300
        ev = rng.uniform(-300, 300, size=M); g = (W*ev) @ W.conj().T
    else:                      # two scales: O(1) block coupling, O(100) diagonal
        G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); G = (G + G.conj().T)/2
        P = np.eye(M) - B; g = 100*(B @ G @ B + P @ G @ P) + (G - B @ G @ B - P @ G @ P)
    g = (g + g.conj().T)/2
    return g, B, kind

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0; n = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    rng = np.random.default_rng(seed); worst = {'marg': 0, 'radon': 0, 'lap': 0}
    for k in range(n):
        g, B, kind = make(rng, k); M = g.shape[0]; P = np.eye(M) - B; t0 = time.time()
        fro = np.linalg.norm(B @ g @ P)**2
        ev = np.linalg.eigvalsh(g); width = ev[-1] - ev[0]
        devs = []
        for tau in rng.uniform(0.02, 0.98, size=2):
            v = tau_marginal(g, B, tau); devs.append(abs(v - fro)/fro)
        worst['marg'] = max(worst['marg'], max(devs))
        rdev = []
        for _ in range(2):
            xi = rng.normal()*width/2
            lam = np.linalg.eigvalsh(g - xi*P); w = lam[0] + (lam[-1] - lam[0])*rng.uniform(0.2, 0.8)
            U = U_float(g, B, xi, w)
            if U > 1e-9*max(1, width):
                v = radon(g, B, xi, w); rdev.append(abs(v - U)/U)
        worst['radon'] = max([worst['radon']] + rdev)
        a = rng.choice([-1, 1])*rng.uniform(0.3, 2.0)/max(1.0, width/4); t = rng.uniform(-2, 3)
        lhs = D_float(g, B, a, t)/a**2; rhs = laplace(g, B, a, t); ldev = abs(lhs - rhs)/abs(lhs)
        worst['lap'] = max(worst['lap'], ldev)
        print(f"[{k:2d}] {kind:8s} M={M} r={int(round(np.trace(B).real))} |g|={np.abs(ev).max():7.1f} ||BgP||^2={fro:10.4g}: "
              f"marg dev {max(devs):.1e}  radon dev {max(rdev) if rdev else float('nan'):.1e}  laplace dev {ldev:.1e}  [{time.time()-t0:.0f}s]", flush=True)
    print("WORST relative deviations:", {k: f"{v:.2e}" for k, v in worst.items()})
