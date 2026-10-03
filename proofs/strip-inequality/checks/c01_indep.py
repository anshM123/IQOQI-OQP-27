# Independent re-implementation check of Theorem 2 (strip inequality, exact defect):  defect(lam) = int_0^1 int_R K_{1-tau}(s-lam) F(s,tau) ds dtau,
# F = (1/2pi) sum |Im eig((P - tau)^{-1}(g - s))|.  Own implementation (no reuse of q_core).
import sys; sys.path.insert(0, '../../common')
import numpy as np
from fcore import hstrip
rng = np.random.default_rng(2024)
def defect(B, g, lam):
    M = B.shape[0]; P = np.eye(M) - B
    nu = np.linalg.eigvals(B + 1j*(g - lam*np.eye(M)))
    w, V = np.linalg.eigh(P); Q = V[:, w > .5]
    mu = np.linalg.eigvalsh(Q.conj().T@g@Q)
    return np.sum(hstrip(nu)) - np.sum(np.maximum(mu - lam, 0))
def Fgrid(B, g, s, tau):
    M = B.shape[0]; P = np.eye(M) - B
    S, T = np.meshgrid(s, tau, indexing='ij')
    Pinv = P[None,None]/(1 - T[...,None,None]) - B[None,None]/T[...,None,None]
    A = Pinv @ (g[None,None] - S[...,None,None]*np.eye(M)[None,None])
    ev = np.linalg.eigvals(A)
    return np.sum(np.abs(ev.imag), axis=-1)/(2*np.pi)
def K(X, u):
    return np.sin(np.pi*X)/(2*(np.cosh(np.pi*u) - np.cos(np.pi*X)))
def V(B, g, lam, ns=1500, nt=1200):
    lmin, lmax = np.linalg.eigvalsh(g)[[0, -1]]
    s = np.linspace(lmin, lmax, ns)
    th = (np.arange(nt) + 0.5)/nt*(np.pi/2)          # tau = sin^2(theta), midpoint rule in theta
    tau = np.sin(th)**2; jac = 2*np.sin(th)*np.cos(th)*(np.pi/2)/nt
    F = Fgrid(B, g, s, tau)
    Kmat = K(1 - tau[None, :], s[:, None] - lam)
    ds = s[1] - s[0]
    integrand = Kmat*F
    # trapezoid in s
    Is = (integrand.sum(axis=0) - 0.5*(integrand[0] + integrand[-1]))*ds
    return np.sum(Is*jac)
for trial in range(8):
    M = int(rng.integers(3, 5)); r = int(rng.integers(1, M))
    U = np.linalg.qr(rng.normal(size=(M,M)) + 1j*rng.normal(size=(M,M)))[0]
    B = U[:, :r]@U[:, :r].conj().T
    sc = [1.0, 3.0][trial % 2]
    g = rng.normal(size=(M,M)) + 1j*rng.normal(size=(M,M)); g = (g + g.conj().T)/2*sc
    lam = rng.normal()*sc
    d = defect(B, g, lam); v = V(B, g, lam)
    print(f'M={M} r={r} sc={sc}: defect={d:.8f}  V={v:.8f}  diff={d-v:.2e}')
