"""Core numerics for Q_2bmv.

Closed form (PROOF.md, Theorem 1):  nu_2(s,tau) = (1/2pi) sum_i |Im x_i(s,tau)|,  x_i = roots of det(g - s - x(P - tau)),
i.e. eigenvalues of (P - tau)^{-1}(g - s) = (P/(1-tau) - B/tau)(g - s),  0 < tau < 1.

Float and mpmath versions; breakpoints of nu_2 along a line = real roots of the x-discriminant (polynomial of degree <= M(M-1)
in the line parameter, PROOF.md Remark), found by Chebyshev interpolation at high precision + polyroots.
"""
import numpy as np, mpmath as mp
from scipy.linalg import expm

PI = np.pi

# ------------------------------------------------------------------ float
def F_float(g, B, s, tau):
    M = g.shape[0]; P = np.eye(M) - B
    x = np.linalg.eigvals((P/(1 - tau) - B/tau) @ (g - s*np.eye(M)))
    return np.sum(np.abs(x.imag))/(2*PI)

def blocks_eig(g, B):
    w, V = np.linalg.eigh(B); VB = V[:, w > 0.5]; VP = V[:, w < 0.5]
    return np.linalg.eigvalsh(VB.conj().T @ g @ VB), np.linalg.eigvalsh(VP.conj().T @ g @ VP)

def D_float(g, B, a, t):
    M = g.shape[0]; P = np.eye(M) - B
    eB, eP = blocks_eig(g, B)
    return (np.trace(expm(a*g - t*P)) - np.exp(-t)*np.sum(np.exp(a*eP)) - np.sum(np.exp(a*eB))).real

def U_float(g, B, xi, w):
    M = g.shape[0]; P = np.eye(M) - B
    lam = np.linalg.eigvalsh(g - xi*P); eB, eP = blocks_eig(g, B)
    lam0 = np.r_[eB, eP - xi]
    return np.sum(np.maximum(w - lam, 0)) - np.sum(np.maximum(w - lam0, 0))

# ------------------------------------------------------------------ mpmath
def to_mp(A):
    return mp.matrix([[mp.mpc(complex(A[i, j])) for j in range(A.shape[1])] for i in range(A.shape[0])])

class MPConf:
    """holds B, g as mp matrices (exactly the float64 values of the input), plus block data."""
    def __init__(self, g, B, dps=60):
        self.M = g.shape[0]; self.gf = g; self.Bf = B
        mp.mp.dps = dps
        self.g = to_mp(g)
        # B: re-orthogonalise at high precision from its float eigenvectors so that B^2 = B to working precision
        w, V = np.linalg.eigh(B); self.r = int(np.sum(w > 0.5))
        Vm = to_mp(V)
        Q, _ = mp.qr(Vm)
        self.VB = Q[:, self.M - self.r:]; self.VP = Q[:, :self.M - self.r]   # eigh sorts ascending: last r = B
        self.B = self.VB*self.VB.H; self.P = mp.eye(self.M) - self.B
        self.gB = self.VB.H*self.g*self.VB; self.gP = self.VP.H*self.g*self.VP
        self.eB = sorted([mp.re(e) for e in mp.eigh(self.gB, eigvals_only=True)]) if self.r > 0 else []
        self.eP = sorted([mp.re(e) for e in mp.eigh(self.gP, eigvals_only=True)]) if self.r < self.M else []
        self.eg = sorted([mp.re(e) for e in mp.eigh(self.g, eigvals_only=True)])

    def roots(self, s, tau):
        M = self.M
        Jinv = self.P/(1 - tau) - self.B/tau
        A = Jinv*(self.g - s*mp.eye(M))
        ev = mp.eig(A, left=False, right=False)
        return ev

    def F(self, s, tau, thr=None):
        if not (0 < tau < 1):
            return mp.mpf(0)
        ev = self.roots(s, tau)
        if thr is None:
            thr = mp.mpf(10)**(-(mp.mp.dps*2)//3)
        return sum((abs(mp.im(e)) for e in ev if abs(mp.im(e)) > thr), mp.mpf(0))/(2*mp.pi)

    def disc(self, s, tau):
        """x-discriminant of p(x) = det(g - s - x(P - tau)) = lead * prod (x - x_i):  lead^{2M-2} prod_{i<j}(x_i - x_j)^2."""
        M = self.M
        lead = (-1)**M * (1 - tau)**(M - self.r) * (-tau)**self.r
        ev = self.roots(s, tau)
        pr = mp.mpf(1)
        for i in range(M):
            for j in range(i + 1, M):
                pr *= (ev[i] - ev[j])**2
        return mp.re(lead**(2*M - 2)*pr)

    def U(self, xi, w):
        lam = [mp.re(e) for e in mp.eigh(self.g - xi*self.P, eigvals_only=True)]
        lam0 = list(self.eB) + [e - xi for e in self.eP]
        return sum((max(w - l, 0) for l in lam), mp.mpf(0)) - sum((max(w - l, 0) for l in lam0), mp.mpf(0))

    def frob_BgP(self):
        X = self.B*self.g*self.P
        return mp.re(sum(abs(X[i, j])**2 for i in range(self.M) for j in range(self.M)))


def breakpoints(fun_disc, u0, u1, deg, dps_work=None):
    """real roots in (u0,u1) of a polynomial of degree <= deg given by values fun_disc(u): Chebyshev interpolation + polyroots."""
    n = deg + 1
    nodes = [ (u0 + u1)/2 + (u1 - u0)/2*mp.cos(mp.pi*(k + mp.mpf(1)/2)/n) for k in range(n) ]
    vals = [fun_disc(u) for u in nodes]
    # monomial coefficients in the variable z = (2u - u0 - u1)/(u1 - u0) via a Vandermonde solve (fine at high precision)
    zs = [(2*u - u0 - u1)/(u1 - u0) for u in nodes]
    V = mp.matrix([[z**k for k in range(n)] for z in zs])
    c = mp.lu_solve(V, mp.matrix(vals))
    coeffs = [c[k] for k in range(n)][::-1]       # highest first
    # strip negligible leading coefficients
    scale = max(abs(x) for x in coeffs)
    while len(coeffs) > 1 and abs(coeffs[0]) < scale*mp.mpf(10)**(-mp.mp.dps//2):
        coeffs = coeffs[1:]
    if len(coeffs) <= 1:
        return []
    try:
        rts = mp.polyroots(coeffs, maxsteps=400, extraprec=4*mp.mp.dps)
    except mp.libmp.libhyper.NoConvergence:
        rts = mp.polyroots(coeffs, maxsteps=2000, extraprec=8*mp.mp.dps, error=False)
    out = []
    for z in rts:
        if abs(mp.im(z)) < mp.mpf(10)**(-mp.mp.dps//4) and -1 < mp.re(z) < 1:
            out.append((u0 + u1)/2 + (u1 - u0)/2*mp.re(z))
    return sorted(out)
