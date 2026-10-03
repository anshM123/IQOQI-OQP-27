"""q03: end-to-end check of the exact (*) defect formula with the closed-form density (PROOF.md, Theorem 2):
    Psi_lam - Tr[(PgP - lam)_+]  =  V(lam) := int_0^1 dtau int ds K_{1-tau}(s - lam) nu_2(s,tau),
    K_{1-tau}(u) = sin(pi tau) / (2 (cosh(pi u) + cos(pi tau))),   nu_2 = (1/2pi) sum |Im x_i|.
LHS in mpmath (30 digits, Li2 via mp.polylog); RHS by nested adaptive float quadrature (s-breakpoints at root collisions and at lam;
tau = sin^2(theta) substitution).  usage: python q03_defect_check.py [names]"""
import numpy as np, mpmath as mp, sys, time
from scipy.integrate import quad
from q_core import F_float
from q02_hp_checks import CONFS

mp.mp.dps = 30

def h_mp(nu, lam):
    x = mp.mpf(nu.real); y = mp.mpf(nu.imag) - lam
    x = min(max(x, mp.mpf(10)**-25), 1 - mp.mpf(10)**-25)
    return -mp.im(mp.polylog(2, mp.exp(mp.pi*y)*mp.exp(-1j*mp.pi*x)))/mp.pi**2

def lhs(g, B, lam):
    M = g.shape[0]; P = np.eye(M) - B
    gm = mp.matrix([[mp.mpc(complex(g[i, j])) for j in range(M)] for i in range(M)])
    w, V = np.linalg.eigh(B); r = int(np.sum(w > 0.5))
    Vm = mp.matrix([[mp.mpc(complex(V[i, j])) for j in range(M)] for i in range(M)]); Q, _ = mp.qr(Vm)
    VB = Q[:, M - r:]; VP = Q[:, :M - r]; Bm = VB*VB.H
    nus = mp.eig(Bm + 1j*gm, left=False, right=False)
    psi = sum(h_mp(complex(e), mp.mpf(lam)) if False else
              -mp.im(mp.polylog(2, mp.exp(mp.pi*(mp.im(e) - lam))*mp.exp(-1j*mp.pi*min(max(mp.re(e), mp.mpf(10)**-25), 1 - mp.mpf(10)**-25))))/mp.pi**2
              for e in nus)
    eP = mp.eigh(VP.H*gm*VP, eigvals_only=True)
    rhs = sum(max(mp.re(e) - lam, 0) for e in eP)
    return psi - rhs, psi, rhs

def F_te(g, B, s, tau, eps):
    """nu_2 with tau and eps = 1 - tau passed separately (no cancellation near tau = 1)."""
    M = g.shape[0]; P = np.eye(M) - B
    x = np.linalg.eigvals((P/eps - B/tau) @ (g - s*np.eye(M)))
    return np.sum(np.abs(x.imag))/(2*np.pi)

def Kker(u, eps):
    """K_{1-tau}(u) = sin(pi eps)/(2(cosh pi u - cos pi eps)), eps = 1 - tau, overflow/cancellation-free form."""
    q = np.exp(-np.pi*abs(u))
    return np.sin(np.pi*eps)*q/((1 - q)**2 + 4*np.sin(np.pi*eps/2)**2*q)

def transitions_s(g, B, tau, eps, lo, hi, n=1500):
    M = g.shape[0]; P = np.eye(M) - B; Jinv = P/eps - B/tau
    def cnt(s):
        x = np.linalg.eigvals(Jinv @ (g - s*np.eye(M))); sc = max(1.0, np.max(np.abs(x)))
        return int(np.sum(np.abs(x.imag) > 1e-7*sc))
    ss = np.linspace(lo, hi, n); cs = [cnt(s) for s in ss]; out = []
    for k in range(n - 1):
        if cs[k] != cs[k + 1]:
            a, b = ss[k], ss[k + 1]; ca = cs[k]
            for _ in range(60):
                m = (a + b)/2
                if cnt(m) == ca: a = m
                else: b = m
            out.append((a + b)/2)
    return out

def V_of_lam(g, B, lam):
    ev = np.linalg.eigvalsh(g); lo, hi = ev[0], ev[-1]
    def inner(th):
        tau = np.sin(th)**2; eps = np.cos(th)**2
        if tau <= 0 or eps <= 0:
            return 0.0
        pts = transitions_s(g, B, tau, eps, lo, hi)
        if lo < lam < hi: pts = pts + [lam]
        pts = sorted(pts); edges = [lo] + pts + [hi]; tot = 0.0
        for a, b in zip(edges[:-1], edges[1:]):
            if b - a < 1e-14: continue
            v, e = quad(lambda s: Kker(s - lam, eps)*F_te(g, B, s, tau, eps), a, b, limit=400, epsabs=1e-14, epsrel=1e-12)
            tot += v
        return tot*np.sin(2*th)
    v, e = quad(inner, 0, np.pi/2, limit=400, epsabs=1e-12, epsrel=1e-10)
    return v, e

if __name__ == "__main__":
    names = sys.argv[1].split(',') if len(sys.argv) > 1 else ['r3_1', 't03', 't59', 'r4_1']
    for name in names:
        g, B = CONFS[name](); M = g.shape[0]; P = np.eye(M) - B
        eP = np.linalg.eigvalsh(P @ g @ P)
        lams = [float(np.median(np.linalg.eigvalsh(g))), float(eP.max()) - 0.3]
        print(f"=== {name}: M={M} spec g = {np.round(np.linalg.eigvalsh(g), 4)}", flush=True)
        for lam in lams:
            t0 = time.time()
            d, psi, rhs = lhs(g, B, lam)
            v, e = V_of_lam(g, B, lam)
            print(f"  lam={lam:.5f}: Psi - Tr(PgP-lam)_+ = {mp.nstr(d, 16)}   V(lam) = {v:.14f} (+-{e:.1e})   diff = {float(d) - v:.2e}   [{time.time()-t0:.0f}s]", flush=True)
