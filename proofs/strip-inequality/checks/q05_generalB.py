"""q05 (side experiment): does the closed form extend to a general Hermitian B = sum_k b_k Pi_k (distinct b_k)?
Test   Tr e^{aA - tB} - sum_k e^{-t b_k} Tr e^{a Pi_k A Pi_k}  =?=  a^2 int int e^{as - t tau} F(s,tau) ds dtau,
F = (1/2pi) sum |Im roots of det(A - s - x(B - tau))|, tau in (b_min, b_max) minus the interior eigenvalues.
(For projections this is Theorem 1.)  Interior lines tau = b_k are NOT covered by the proof of Theorem 1 (no asymptotics there)."""
import numpy as np, sys
from scipy.linalg import expm
from scipy.integrate import quad

def F(A, B, s, tau):
    M = A.shape[0]
    x = np.linalg.eigvals(np.linalg.solve(B - tau*np.eye(M), A - s*np.eye(M)))
    return np.sum(np.abs(x.imag))/(2*np.pi)

def cntf(A, B, s, tau):
    M = A.shape[0]; x = np.linalg.eigvals(np.linalg.solve(B - tau*np.eye(M), A - s*np.eye(M)))
    return int(np.sum(np.abs(x.imag) > 1e-8*max(1, np.abs(x).max())))

def sint(A, B, tau, a, lo, hi, n=1500):
    ss = np.linspace(lo, hi, n); cs = [cntf(A, B, s, tau) for s in ss]; bp = []
    for k in range(n - 1):
        if cs[k] != cs[k + 1]:
            u, v = ss[k], ss[k + 1]; cu = cs[k]
            for _ in range(55):
                m = (u + v)/2
                if cntf(A, B, m, tau) == cu: u = m
                else: v = m
            bp.append((u + v)/2)
    e = [lo] + bp + [hi]; tot = 0.0
    for u, v in zip(e[:-1], e[1:]):
        if v - u > 1e-15:
            tot += quad(lambda s: np.exp(a*s)*F(A, B, s, tau), u, v, limit=300, epsabs=1e-13, epsrel=1e-11)[0]
    return tot

def rhs(A, B, bs, a, t, ng=120):
    lo, hi = np.linalg.eigvalsh(A)[[0, -1]]; tot = 0.0
    xt, wt = np.polynomial.legendre.leggauss(ng)
    for b0, b1 in zip(bs[:-1], bs[1:]):           # each gap between consecutive eigenvalues of B, tau = b0 + (b1-b0) sin^2
        th = (np.pi/4)*(xt + 1); w = wt*np.pi/4
        for thk, wk in zip(th, w):
            tau = b0 + (b1 - b0)*np.sin(thk)**2
            tot += wk*(b1 - b0)*np.sin(2*thk)*np.exp(-t*tau)*sint(A, B, tau, a, lo, hi)
    return a*a*tot

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    M = 3; bs = [0.0, 0.37, 1.0]
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); U, _ = np.linalg.qr(Z)
    B = (U*np.array(bs)) @ U.conj().T; B = (B + B.conj().T)/2
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); A = (G + G.conj().T)/2
    for (a, t) in [(1.0, 0.0), (0.7, 2.0), (-1.2, -1.5), (1.0, 6.0)]:
        lhs = np.trace(expm(a*A - t*B)).real
        for k, b in enumerate(bs):
            u = U[:, k:k+1]; lhs -= np.exp(-t*b)*np.exp(a*(u.conj().T @ A @ u)[0, 0].real)
        r = rhs(A, B, bs, a, t)
        print(f"a={a:5.2f} t={t:5.2f}:  LHS = {lhs:.10f}   RHS = {r:.10f}   diff = {lhs - r:.3e}   diff*e^(t b_2) = {(lhs - r)*np.exp(t*bs[1]):.3e}", flush=True)
