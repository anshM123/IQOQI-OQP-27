"""q01: float check of the closed form  nu_2(s,tau) = (1/2pi) sum_i |Im x_i(s,tau)|,  x_i = eig((P - tau)^{-1}(g - s)).
Checks (a) D(a,t)/a^2 = int int e^{as - t tau} nu_2 ds dtau  for several real (a,t);
       (b) tau-marginal  int nu_2(s,tau) ds = ||B g P||_F^2  for every tau in (0,1).
Quadrature: tau = sin^2(theta) (kills the 1/sqrt(tau(1-tau)) edge), Gauss-Legendre in theta and in s on [lmin(g), lmax(g)]."""
import numpy as np, sys
from scipy.linalg import expm

def F(g, B, s, tau):
    M = g.shape[0]; P = np.eye(M) - B
    Jinv = P/(1 - tau) - B/tau
    x = np.linalg.eigvals(Jinv @ (g - s*np.eye(M)))
    return np.sum(np.abs(x.imag))/(2*np.pi)

def D(g, B, a, t):
    M = g.shape[0]; P = np.eye(M) - B
    w, V = np.linalg.eigh(B); VB = V[:, w > 0.5]; VP = V[:, w < 0.5]
    gB = VB.conj().T @ g @ VB; gP = VP.conj().T @ g @ VP
    return (np.trace(expm(a*g - t*P)) - np.exp(-t)*np.trace(expm(a*gP)) - np.trace(expm(a*gB))).real

def grid(g, B, ns=400, nt=200):
    lo, hi = np.linalg.eigvalsh(g)[[0, -1]]
    xs, ws = np.polynomial.legendre.leggauss(ns); s = lo + (hi - lo)*(xs + 1)/2; ws = ws*(hi - lo)/2
    xt, wt = np.polynomial.legendre.leggauss(nt); th = (np.pi/4)*(xt + 1); wt = wt*np.pi/4
    tau = np.sin(th)**2; wtau = wt*np.sin(2*th)
    Fv = np.array([[F(g, B, si, ti) for si in s] for ti in tau])   # shape (nt, ns)
    return s, ws, tau, wtau, Fv

def rand_case(M, r, scale, rng):
    Z = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); Q, _ = np.linalg.qr(Z)
    B = Q[:, :r] @ Q[:, :r].conj().T
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); g = scale*(G + G.conj().T)/2
    return g, B

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    for (M, r, sc) in [(2, 1, 1.0), (3, 1, 1.0), (3, 2, 1.0), (4, 2, 1.0), (5, 2, 0.7), (4, 1, 2.0)]:
        g, B = rand_case(M, r, sc, rng)
        s, ws, tau, wtau, Fv = grid(g, B)
        P = np.eye(M) - B
        fro = np.linalg.norm(B @ g @ P)**2
        marg = Fv @ ws
        print(f"M={M} r={r} scale={sc}: ||BgP||^2 = {fro:.6f}; tau-marginal range [{marg.min():.6f}, {marg.max():.6f}]")
        for (a, t) in [(0.7, 0.0), (-1.3, 0.5), (0.4, -2.0), (1.1, 3.0)]:
            lhs = D(g, B, a, t)/a**2
            rhs = np.sum(wtau[:, None]*ws[None, :]*np.exp(a*s[None, :] - t*tau[:, None])*Fv)
            print(f"   a={a:5.2f} t={t:5.2f}:  D/a^2 = {lhs:.8f}   int e^(as-t tau) nu2 = {rhs:.8f}   rel.err = {abs(lhs-rhs)/abs(lhs):.2e}")
