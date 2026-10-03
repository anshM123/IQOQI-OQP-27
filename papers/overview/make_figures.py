"""Figures for the article "Fourier measurements are optimal for CGLMP Bell tests on maximally entangled states in
every dimension" (A. Mishra and A. Senthilkumar).

All plotted data are computed here (double precision; numpy/scipy) or read from the certificate files of the
verification programme (the folder cone-certificates/ of this repository: certs/cert_d*.json for
2 <= d <= 200, the single-run certificates logs/cert_g_d*.json of verify_cert.py for 201 <= d <= 2000, and
logs/alld/*.json for d >= 2001).  Nothing is drawn by hand except the schematic and the flow diagram.

Run:  python make_figures.py            (writes figures/fig1.pdf ... fig5.pdf, PNG previews, and prints the numbers
                                         quoted in the captions)
      python make_figures.py --recompute (ignore the cache of the expensive computations in figures/cache/)
"""
import glob
import json
import os
import re
import sys
from decimal import Decimal
from fractions import Fraction

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle, Ellipse, Rectangle, Wedge, Polygon
from matplotlib.colors import LinearSegmentedColormap, PowerNorm, Normalize
from matplotlib.lines import Line2D
from scipy.linalg import expm
from scipy.optimize import brentq, linear_sum_assignment
from scipy.special import spence

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'figures')
CACHE = os.path.join(OUT, 'cache')
QD2 = os.path.normpath(os.path.join(HERE, '..', '..', 'cone-certificates'))   # certificate data of this repository
os.makedirs(OUT, exist_ok=True)
os.makedirs(CACHE, exist_ok=True)
RECOMPUTE = '--recompute' in sys.argv

# ------------------------------------------------------------------------------------------------ style
plt.rcParams.update({
    'font.family': 'sans-serif', 'font.sans-serif': ['Arial', 'Helvetica', 'DejaVu Sans'],
    'mathtext.fontset': 'custom', 'mathtext.rm': 'Arial', 'mathtext.it': 'Arial:italic',
    'mathtext.bf': 'Arial:bold', 'mathtext.sf': 'Arial', 'mathtext.fallback': 'stixsans',
    'font.size': 7, 'axes.labelsize': 7, 'axes.titlesize': 7, 'xtick.labelsize': 6, 'ytick.labelsize': 6,
    'legend.fontsize': 6, 'axes.linewidth': 0.6, 'xtick.major.width': 0.6, 'ytick.major.width': 0.6,
    'xtick.minor.width': 0.4, 'ytick.minor.width': 0.4, 'xtick.major.size': 2.5, 'ytick.major.size': 2.5,
    'xtick.minor.size': 1.5, 'ytick.minor.size': 1.5, 'axes.spines.top': False, 'axes.spines.right': False,
    'axes.edgecolor': '#333333', 'xtick.color': '#333333', 'ytick.color': '#333333', 'axes.labelcolor': '#1a1a1a',
    'text.color': '#1a1a1a', 'pdf.fonttype': 42, 'savefig.dpi': 600, 'axes.titlepad': 4,
    'legend.frameon': False, 'legend.handlelength': 1.4, 'legend.borderaxespad': 0.2,
})
# categorical slots (validated: blue/vermillion/green pass all-pairs CVD and contrast checks on white)
C_BLUE, C_VERM, C_GREEN, C_ORANGE = '#0072B2', '#D55E00', '#009E73', '#E69F00'
INK, INK2, MUTED, HAIR = '#1a1a1a', '#4d4d4d', '#8c8c8c', '#d9d9d9'
MM = 1/25.4
SEQ_BLUE = LinearSegmentedColormap.from_list('seqblue', ['#ffffff', '#d4e6f4', '#8fbfe0', '#3a8fc8', C_BLUE, '#023d63'])
SEQ_VERM = LinearSegmentedColormap.from_list('seqverm', ['#ffffff', '#fbe3d4', '#f4b48c', '#e8804a', C_VERM, '#6e2a00'])


def panel_label(ax, s, x=-0.02, y=1.02, fig=None):
    ax.text(x, y, s, transform=ax.transAxes, fontsize=8, fontweight='bold', va='bottom', ha='right', color='k')


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + '.pdf'))
    fig.savefig(os.path.join(OUT, name + '.png'), dpi=300)
    plt.close(fig)
    print(f'[{name}] written')


def cached(name, fn):
    path = os.path.join(CACHE, name + '.npz')
    if os.path.exists(path) and not RECOMPUTE:
        return dict(np.load(path, allow_pickle=True))
    out = fn()
    np.savez(path, **out)
    return out


# ------------------------------------------------------------------------------------------------ CGLMP basics
def I_ME(d):
    j = np.arange(1, d)
    return 4.0/(d*(d - 1))*np.sum((d - j)/np.cos(np.pi*j/(2*d)))


CATALAN = 0.915965594177219015054603514932
I_INF = 32*CATALAN/np.pi**2          # = lim I_ME(d) = 2.96981...


def cglmp_coeffs(d):
    """c[x, y, t]: I_d = sum_{x,y,a,b} c[x, y, (a - b) mod d] P(a, b | x, y)  (CGLMP, Phys. Rev. Lett. 88, 040404)."""
    c = np.zeros((2, 2, d))
    for k in range(d//2):
        w = 1 - 2*k/(d - 1)
        c[0, 0, k % d] += w; c[0, 0, (-k - 1) % d] -= w          # P(A1 = B1 + k) - P(A1 = B1 - k - 1)
        c[1, 0, (-k - 1) % d] += w; c[1, 0, k % d] -= w          # P(B1 = A2 + k + 1) - P(B1 = A2 - k)
        c[1, 1, k % d] += w; c[1, 1, (-k - 1) % d] -= w          # P(A2 = B2 + k) - P(A2 = B2 - k - 1)
        c[0, 1, (-k) % d] += w; c[0, 1, (k + 1) % d] -= w        # P(B2 = A1 + k) - P(B2 = A1 - k - 1)
    return c


def haar(D, rng):
    Z = rng.normal(size=(D, D)) + 1j*rng.normal(size=(D, D))
    Q, R = np.linalg.qr(Z)
    return Q*(np.diag(R)/np.abs(np.diag(R)))


class Strategy:
    """Projective strategy on the maximally entangled state of C^D (x) C^D, D = d k, with rank-k projectors
    P^x_a = U_x Pi_a U_x^*, Q^y_b = V_y Pi_b V_y^*;  p(a,b|x,y) = Tr(P^x_a (Q^y_b)^T)/D."""

    def __init__(self, d, k):
        self.d, self.k, self.D = d, k, d*k
        self.c = cglmp_coeffs(d)
        a = np.arange(d)
        self.T = (a[:, None] - a[None, :]) % d

    def probs(self, U, V):
        d, k, D = self.d, self.k, self.D
        p = np.zeros((2, 2, d, d))
        for x in range(2):
            for y in range(2):
                Mxy = U[x].conj().T @ V[y].conj()
                p[x, y] = (np.abs(Mxy)**2).reshape(d, k, d, k).sum(axis=(1, 3))/D
        return p

    def value(self, U, V):
        p = self.probs(U, V)
        return float(sum((self.c[x, y][self.T]*p[x, y]).sum() for x in range(2) for y in range(2)))

    def value_and_directions(self, U, V):
        """value and the Riemannian ascent directions (skew-Hermitian generators) for U_x and V_y"""
        d, k, D, c = self.d, self.k, self.D, self.c
        f = self.value(U, V)
        PA = [[U[x][:, a*k:(a + 1)*k] @ U[x][:, a*k:(a + 1)*k].conj().T for a in range(d)] for x in range(2)]
        PB = [[V[y][:, b*k:(b + 1)*k] @ V[y][:, b*k:(b + 1)*k].conj().T for b in range(d)] for y in range(2)]
        dirs = []
        for side in range(2):
            for s in range(2):
                W = U[s] if side == 0 else V[s]
                Om = np.zeros((D, D), complex)
                for a in range(d):
                    if side == 0:
                        G = sum(c[s, y][(a - b) % d]*PB[y][b].conj() for y in range(2) for b in range(d))/D
                    else:
                        G = sum(c[x, s][(b - a) % d]*PA[x][b].conj() for x in range(2) for b in range(d))/D
                    X = W.conj().T @ G @ W
                    Pi = np.zeros(D); Pi[a*k:(a + 1)*k] = 1
                    Om += X*Pi[None, :] - Pi[:, None]*X          # increases f (d f = Tr(Om^* Om) >= 0)
                dirs.append(Om)
        return f, dirs


def ascent(d, k, rng, iters=2500):
    S = Strategy(d, k)
    U = [haar(d*k, rng) for _ in range(2)]
    V = [haar(d*k, rng) for _ in range(2)]
    eta = 0.5
    f, dirs = S.value_and_directions(U, V)
    traj = [f]
    for it in range(iters):
        if sum(np.linalg.norm(o)**2 for o in dirs) < 1e-24:
            break
        while True:
            U2 = [U[x] @ expm(eta*dirs[x]) for x in range(2)]
            V2 = [V[y] @ expm(eta*dirs[2 + y]) for y in range(2)]
            f2, dirs2 = S.value_and_directions(U2, V2)
            if f2 >= f - 1e-15:
                U, V, f, dirs = U2, V2, f2, dirs2
                eta = min(eta*1.3, 50.0)
                break
            eta *= 0.5
            if eta < 1e-14:
                break
        traj.append(f)
    return np.array(traj)


def dkz_value(d):
    al, be = [0.0, 0.5], [0.25, -0.25]
    j = np.arange(d)
    U = [np.array([np.exp(-2j*np.pi*j*(a + al[x])/d)/np.sqrt(d) for a in range(d)]).T for x in range(2)]
    V = [np.array([np.exp(2j*np.pi*j*(b - be[y])/d)/np.sqrt(d) for b in range(d)]).T for y in range(2)]
    return Strategy(d, 1).value(U, V)


# ------------------------------------------------------------------------------------------------ strip numerics
PI = np.pi


def h_lam(nu, lam):
    """h_lam(x+iy) = -(1/pi^2) Im Li2(e^{pi(y - lam)} e^{-i pi x}), harmonic on 0 < x < 1, boundary values (y - lam)_+
    on x = 0 and 0 on x = 1 (Li2(z) = spence(1 - z), principal branch)."""
    nu = np.asarray(nu, dtype=complex)
    x, y = nu.real, nu.imag
    z = np.exp(PI*(y - lam))*np.exp(-1j*PI*np.clip(x, 0, 1))
    val = -np.imag(spence(1 - z))/PI**2
    val = np.where(x <= 1e-15, np.maximum(y - lam, 0.0), val)
    val = np.where(x >= 1 - 1e-15, 0.0, val)
    return val


def K_strip(X, u):
    """Poisson kernel of the strip 0 < X < 1 for its left edge."""
    return np.sin(PI*X)/(2*(np.cosh(PI*u) - np.cos(PI*X)))


def rand_unitary(M, rng):
    return haar(M, rng)


def instance(M, r, rng):
    U = rand_unitary(M, rng)
    B = U[:, :r] @ U[:, :r].conj().T
    B = (B + B.conj().T)/2
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M))
    return B, (G + G.conj().T)/2


def compressions(B, g):
    w, V = np.linalg.eigh(B)
    Qb, Qp = V[:, w > .5], V[:, w <= .5]
    return np.linalg.eigvalsh(Qb.conj().T @ g @ Qb), np.linalg.eigvalsh(Qp.conj().T @ g @ Qp)


def lhs_star(B, g, lams):
    nu = np.linalg.eigvals(B + 1j*g)
    return np.array([h_lam(nu, l).sum() for l in np.atleast_1d(lams)])


def rhs_star(B, g, lams):
    _, pp = compressions(B, g)
    return np.array([np.maximum(pp - l, 0).sum() for l in np.atleast_1d(lams)])


def F_vals(B, g, s, tau):
    """F(s,tau) = (1/2pi) sum_i |Im x_i|, x_i the roots of det(g - s - x(P - tau)) = eig((P - tau)^{-1}(g - s))."""
    M = B.shape[0]; P = np.eye(M) - B
    S = P/np.sqrt(1 - tau) + B/np.sqrt(tau)          # |P - tau|^{-1/2}; the pencil is similar to J S (g - s) S
    J = P - B
    SgS, S2 = S @ g @ S, S @ S
    s = np.atleast_1d(s)
    ev = np.linalg.eigvals(J[None] @ (SgS[None] - s[:, None, None]*S2[None]))
    im = np.abs(ev.imag)
    im[im < 1e-12*(np.abs(ev).max(-1, keepdims=True) + 1e-300)] = 0.0
    return im.sum(-1)/(2*PI)


def crit_values(B, g, tau, N=4000):
    """Breakpoints of F(., tau): critical values of the eigenvalue curves x -> lambda_j(g - x(P - tau))."""
    M = B.shape[0]; P = np.eye(M) - B
    ev = np.linalg.eigvalsh(g); lmin, lmax = ev[0], ev[-1]; W = lmax - lmin
    Xmax = 1.05*W/np.sqrt(tau*(1 - tau)) + 1e-12
    Xs = W/40
    Uu = np.arcsinh(Xmax/Xs)
    x = Xs*np.sinh(np.linspace(-Uu, Uu, N))
    Tm = tau*np.eye(M) - P

    def eig_at(xx):
        lam, V = np.linalg.eigh(g + xx*Tm)
        return lam, tau - np.einsum('ij,ik,kj->j', V.conj(), P, V).real
    lam, V = np.linalg.eigh(g[None] + x[:, None, None]*Tm[None])
    dd = tau - np.einsum('nij,ik,nkj->nj', V.conj(), P, V).real
    out = []
    for j in range(M):
        for n in np.nonzero(dd[:-1, j]*dd[1:, j] < 0)[0]:
            try:
                xs = brentq(lambda xx: eig_at(xx)[1][j], x[n], x[n + 1], xtol=1e-15*max(1, abs(x[n])), rtol=1e-15)
            except ValueError:
                continue
            out.append(eig_at(xs)[0][j])
    out = np.array(sorted(v for v in out if lmin < v < lmax))
    if len(out):
        out = out[np.concatenate([[True], np.diff(out) > 1e-13*max(1, W)])]
    return out, lmin, lmax


_XK = np.array([-0.991455371120812639206854697526329, -0.949107912342758524526189684047851, -0.864864423359769072789712788640926,
                -0.741531185599394439863864773280788, -0.586087235467691130294144845693013, -0.405845151377397166906606412076961,
                -0.207784955007898467600689403773245, 0.0, 0.207784955007898467600689403773245, 0.405845151377397166906606412076961,
                0.586087235467691130294144845693013, 0.741531185599394439863864773280788, 0.864864423359769072789712788640926,
                0.949107912342758524526189684047851, 0.991455371120812639206854697526329])
_WK = np.array([0.022935322010529224963732008058970, 0.063092092629978553290700663189204, 0.104790010322250183839876322541518,
                0.140653259715525918745189590510238, 0.169004726639267902826583426598550, 0.190350578064785409913256402421014,
                0.204432940075298892414161999234649, 0.209482141084727828012999174891714, 0.204432940075298892414161999234649,
                0.190350578064785409913256402421014, 0.169004726639267902826583426598550, 0.140653259715525918745189590510238,
                0.104790010322250183839876322541518, 0.063092092629978553290700663189204, 0.022935322010529224963732008058970])
_WG = np.zeros(15)
_WG[1::2] = [0.129484966168869693270611432679082, 0.279705391489276667901467771423780, 0.381830050505118944950369775488975,
             0.417959183673469387755102040816327, 0.381830050505118944950369775488975, 0.279705391489276667901467771423780,
             0.129484966168869693270611432679082]


def slice_integral(B, g, tau, weight_fn, nw, extra=(), tol=1e-12, maxit=60, ninit=4, hmin=1e-9):
    """int_R weight_fn(s)[:, k] F(s,tau) ds; adaptive Gauss-Kronrod in theta, s = sa + (sb - sa) sin^2(theta/2) on each
    interval between breakpoints of F(., tau) (this removes the square-root singularities at the edges)."""
    cv, lmin, lmax = crit_values(B, g, tau)
    pts = np.unique(np.concatenate([[lmin], cv, [lmax], [e for e in extra if lmin < e < lmax]]))
    segs = np.array([(sa, sb, t0, t1) for sa, sb in zip(pts[:-1], pts[1:])
                     for t0, t1 in zip(np.linspace(0, PI, ninit + 1)[:-1], np.linspace(0, PI, ninit + 1)[1:])])
    total = np.zeros(nw)
    for it in range(maxit):
        if len(segs) == 0:
            break
        sa, sb, t0, t1 = segs.T
        c, hh = (t0 + t1)/2, (t1 - t0)/2
        th = c[:, None] + hh[:, None]*_XK[None]
        L = (sb - sa)[:, None]
        s = sa[:, None] + L*np.sin(th/2)**2
        jac = L*np.sin(th)/2*hh[:, None]
        F = F_vals(B, g, s.ravel(), tau).reshape(s.shape)
        f = (F*jac)[..., None]*weight_fn(s.ravel()).reshape(s.shape + (nw,))
        IK, IG = np.einsum('k,skw->sw', _WK, f), np.einsum('k,skw->sw', _WG, f)
        ok = (np.max(np.abs(IK - IG), axis=1) <= tol*hh/PI) | (hh < hmin)
        total += IK[ok].sum(0)
        bad = segs[~ok]
        if len(bad) == 0:
            break
        a0, b0, u0, u1 = bad.T
        mid = (u0 + u1)/2
        segs = np.concatenate([np.stack([a0, b0, u0, mid], 1), np.stack([a0, b0, mid, u1], 1)])
    return total


def tau_integral(fun, nw, tol=1e-9, maxit=40, ninit=16):
    """int_0^1 fun(tau) dtau (vector valued), adaptive Gauss-Kronrod in theta with tau = sin^2(theta/2)."""
    grid = np.linspace(0, PI, ninit + 1)
    segs = list(zip(grid[:-1], grid[1:]))
    total = np.zeros(nw)
    for it in range(maxit):
        if not segs:
            break
        new = []
        for (t0, t1) in segs:
            c, hh = (t0 + t1)/2, (t1 - t0)/2
            th = c + hh*_XK
            vals = np.array([fun(t) for t in np.sin(th/2)**2])*(np.sin(th)/2*hh)[:, None]
            IK, IG = _WK @ vals, _WG @ vals
            if np.max(np.abs(IK - IG)) <= tol*hh/PI or hh < 1e-8:
                total += IK
            else:
                new += [(t0, c), (c, t1)]
        segs = new
    return total


# ================================================================================================ Figure 1
def figure1():
    d0 = 5

    def compute():
        rng = np.random.default_rng(20261002)
        trajs, ranks = [], []
        for k in (1, 2):
            for r in range(20):
                trajs.append(ascent(d0, k, rng, iters=2500))
                ranks.append(k)
        L = max(len(t) for t in trajs)
        T = np.full((len(trajs), L), np.nan)
        for i, t in enumerate(trajs):
            T[i, :len(t)] = t
            T[i, len(t):] = t[-1]
        # random strategies (no optimisation): spread of I_d
        S1 = Strategy(d0, 1)
        rand_vals = np.array([S1.value([haar(d0, rng) for _ in range(2)], [haar(d0, rng) for _ in range(2)])
                              for _ in range(4000)])
        return {'T': T, 'ranks': np.array(ranks), 'rand': rand_vals}
    data = cached('fig1_ascent', compute)
    T, ranks, rand_vals = data['T'], data['ranks'], data['rand']
    excess = np.nanmax(T[:, -1]) - I_ME(d0)
    print(f'[fig1] d = {d0}: DKZ value {dkz_value(d0):.15f}, I_ME = {I_ME(d0):.15f}')
    print(f'[fig1] {len(T)} ascents (D = {d0}, {2*d0}): final values in [{T[:, -1].min():.13f}, {T[:, -1].max():.13f}], '
          f'max excess over I_ME = {excess:.1e}; random strategies: mean {rand_vals.mean():.3f}, max {rand_vals.max():.3f}')

    fig = plt.figure(figsize=(183*MM, 66*MM))
    axA = fig.add_axes([0.0, 0.0, 0.43, 1.0])
    axB = fig.add_axes([0.505, 0.165, 0.215, 0.75])
    axC = fig.add_axes([0.80, 0.165, 0.19, 0.75])

    # ---------------- (a) schematic
    ax = axA
    ax.set_xlim(0, 100); ax.set_ylim(0, 66); ax.axis('off')
    asp = (0.43*183/100)/(1.0*66/66)                          # mm per x-unit / mm per y-unit

    def disc(xy, r, **kw):                                    # a round disc in this anisotropic frame
        return Ellipse(xy, 2*r, 2*r*asp, **kw)
    src = (50, 47)
    for xe in (27.5, 72.5):                                     # entangled pair travelling to the two labs
        xs = np.linspace(src[0] + np.sign(xe - src[0])*5.2, xe, 200)
        ax.plot(xs, src[1] + 0.85*np.sin((xs - src[0])*1.25), color=C_BLUE, lw=0.8, zorder=1)
    for rr, al in [(7.6, 0.10), (6.0, 0.18)]:
        ax.add_patch(disc(src, rr, fc=C_BLUE, ec='none', alpha=al, zorder=2))
    ax.add_patch(disc(src, 4.6, fc='white', ec=C_BLUE, lw=0.9, zorder=2))
    ax.text(src[0], src[1] - 0.2, r'$\Phi_d$', ha='center', va='center', fontsize=8.5, color=C_BLUE, zorder=3)
    ax.text(src[0], src[1] + 9.0, 'maximally entangled source', ha='center', va='bottom', fontsize=6.3, color=INK2)
    ax.text(src[0], src[1] - 8.6, r'$|\Phi_d\rangle=\frac{1}{\sqrt{d}}\sum_j|j\rangle|j\rangle$', ha='center',
            va='top', fontsize=6.3, color=INK2)

    def party(xc, name, setting, outcome):
        bx, by, bw, bh = xc - 12.5, 35.5, 25, 23
        ax.add_patch(FancyBboxPatch((bx, by), bw, bh, boxstyle='round,pad=0.5,rounding_size=2.2', fc='#f3f6f9',
                                    ec=INK, lw=0.8, zorder=2))
        ax.text(xc, by + bh - 3.2, name, ha='center', va='center', fontsize=7.5, fontweight='bold', zorder=3)
        dc = (xc, by + 10.0)
        for i in range(8):                                    # outcome dial: d = 8 outcomes on a clock
            ang = np.pi/2 - 2*np.pi*i/8
            ax.add_patch(disc((dc[0] + 5.0*np.cos(ang), dc[1] + 5.0*np.sin(ang)*asp), 1.05,
                              fc=C_VERM if i == 2 else 'white', ec=INK2, lw=0.5, zorder=3))
        ax.text(dc[0], dc[1], outcome, ha='center', va='center', fontsize=6.0, zorder=3)
        ax.text(xc, by + 2.3, setting, ha='center', va='center', fontsize=6.0, color=INK, zorder=3)
    party(14.5, 'Alice', r'setting $x\in\{1,2\}$', r'$a$')
    party(85.5, 'Bob', r'setting $y\in\{1,2\}$', r'$b$')

    # DKZ recipe (shared)
    y0 = 22.0
    ax.text(50, y0 + 6.6, r'DKZ measurements (Alice $\theta=0,\frac{1}{2}$; Bob $\theta=\frac{1}{4},-\frac{1}{4}$)',
            ha='center', va='center', fontsize=6.2, color=C_BLUE, fontweight='bold')
    chips = [(r'phases $e^{2\pi i j\theta/d}$', 25.0), ('discrete Fourier\ntransform', 22.0),
             (r'detect $|k\rangle$, $k\in\mathbb{Z}_d$', 22.0)]
    xc_ = [17.0, 50.0, 83.0]
    for i, ((lab, w), xx) in enumerate(zip(chips, xc_)):
        ax.add_patch(FancyBboxPatch((xx - w/2, y0 - 3.4), w, 6.8, boxstyle='round,pad=0.3,rounding_size=1.2',
                                    fc='white', ec=C_BLUE, lw=0.6, zorder=2))
        ax.text(xx, y0, lab, ha='center', va='center', fontsize=5.8, color=INK, zorder=3, linespacing=0.95)
        if i < 2:
            ax.add_patch(FancyArrowPatch((xx + w/2 + 0.6, y0), (xc_[i + 1] - chips[i + 1][1]/2 - 0.6, y0),
                                         arrowstyle='-|>', mutation_scale=5, lw=0.6, color=INK2, zorder=3))

    # the bounds
    ax.add_patch(FancyBboxPatch((3.5, 1.8), 93, 10.6, boxstyle='round,pad=0.4,rounding_size=2', fc='#fafafa',
                                ec=HAIR, lw=0.6))
    ax.plot([37.5, 37.5], [3.3, 11.0], color=HAIR, lw=0.6)
    ax.text(20.5, 7.1, 'local models\n' + r'$I_d\leq2$', ha='center', va='center', fontsize=6.3, color=INK2,
            linespacing=1.15)
    ax.text(67, 7.1, r'projective measurements on $\Phi_D$, any $D$' + '\n' + r'$I_d\leq I_{\rm ME}(d)$ (Theorem 1)',
            ha='center', va='center', fontsize=6.3, color=C_BLUE, linespacing=1.15)
    panel_label(ax, 'a', x=0.035, y=0.955)

    # ---------------- (b) ascent landscape
    ax = axB
    it = np.arange(T.shape[1]) + 1
    ax.axhspan(I_ME(d0), 3.25, color='#f6e1d6', lw=0, zorder=0)
    ax.text(T.shape[1]*0.85, 3.08, 'excluded by Theorem 1', color=C_VERM, fontsize=5.9, ha='right', va='center')
    ax.axhline(2.0, color=MUTED, lw=0.7, ls=(0, (3, 2)), zorder=1)
    ax.text(T.shape[1]*0.85, 2.06, 'local bound', color=INK2, fontsize=5.8, va='bottom', ha='right')
    for i in range(len(T)):
        ax.plot(it, T[i], color=C_BLUE if ranks[i] == 1 else C_GREEN, lw=0.55, alpha=0.55, zorder=2)
    ax.axhline(I_ME(d0), color=INK, lw=0.9, zorder=3)
    ax.text(T.shape[1]*0.85, I_ME(d0) - 0.06, r'$I_{\rm ME}(5)$ (DKZ)', fontsize=5.9, va='top', ha='right')
    ax.set_xscale('log')
    ax.set_xlim(1, T.shape[1])
    ax.set_ylim(-0.7, 3.25)
    ax.set_xlabel('ascent step')
    ax.set_ylabel(r'CGLMP value $I_5$')
    handles = [Line2D([], [], color=C_BLUE, lw=1.0, label=r'$D=5$, rank-1'),
               Line2D([], [], color=C_GREEN, lw=1.0, label=r'$D=10$, rank-2')]
    ax.legend(handles=handles, loc='lower right', handlelength=1.2)
    panel_label(ax, 'b', x=-0.2)

    # ---------------- (c) I_ME(d)
    ax = axC
    dd = np.unique(np.round(np.logspace(np.log10(2), 5, 600)).astype(int))
    vals = np.array([I_ME(int(x)) for x in dd])
    ax.axvspan(3, 20, color='#ececec', lw=0, zorder=0)
    ax.text(23, 2.996, 'earlier exact certificates\n' + r'($3\leq d\leq20$)', fontsize=5.4, color=INK2, ha='left',
            va='top', linespacing=1.05)
    ax.axhline(I_INF, color=C_VERM, lw=0.8, ls=(0, (3, 2)), zorder=1)
    ax.text(9e4, I_INF - 0.004, r'$32G/\pi^2=2.9698\ldots$', color=C_VERM, fontsize=5.8, ha='right', va='top')
    ax.plot(dd, vals, color=C_BLUE, lw=1.1, zorder=3)
    small = np.arange(2, 21)
    ax.plot(small, [I_ME(int(x)) for x in small], 'o', ms=2.0, mfc=C_BLUE, mec='white', mew=0.3, zorder=4)
    ax.annotate(r'$d=2$: $2\sqrt{2}$', xy=(2, I_ME(2)), xytext=(24, 2.826), fontsize=5.6, color=INK2, va='center',
                arrowprops=dict(arrowstyle='-', lw=0.4, color=MUTED))
    ax.set_xscale('log')
    ax.set_xlim(1.8, 1e5)
    ax.set_ylim(2.80, 3.0)
    ax.set_xlabel(r'number of outcomes $d$')
    ax.set_ylabel(r'$I_{\rm ME}(d)$')
    ax.text(0.97, 0.03, 'local bound 2: off scale', transform=ax.transAxes, ha='right', va='bottom', fontsize=5.4,
            color=MUTED)
    panel_label(ax, 'c', x=-0.3)
    save(fig, 'fig1')
    return {'excess': excess, 'n_runs': len(T)}


# ================================================================================================ Figure 2
def figure2():
    W, H = 183, 104
    fig = plt.figure(figsize=(W*MM, H*MM))
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, W); ax.set_ylim(0, H); ax.axis('off')

    styles = {
        'red': dict(fc='#f2f2f2', ec='#8c8c8c'),      # exact reductions (earlier work)
        'new': dict(fc='#e4eff8', ec=C_BLUE),         # new analytic theorems
        'cap': dict(fc='#fcebe0', ec=C_VERM),         # computer-assisted
        'res': dict(fc=C_BLUE, ec=C_BLUE),            # main results
        'eq': dict(fc='white', ec='#8c8c8c'),         # steps of the equality analysis
    }

    def box(x, y, w, h, title, body, kind, tsize=6.6, bsize=6.0, gap=2.7, lw=0.8):
        st = styles[kind]
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle='round,pad=0.35,rounding_size=1.6', fc=st['fc'],
                                    ec=st['ec'], lw=lw, zorder=2))
        col = 'white' if kind == 'res' else INK
        if title and body:
            ax.text(x + w/2, y + h - gap, title, ha='center', va='center', fontsize=tsize, fontweight='bold', color=col,
                    zorder=3)
            ax.text(x + w/2, y + (h - gap - 1.2)/2, body, ha='center', va='center', fontsize=bsize, color=col, zorder=3,
                    linespacing=1.3)
        elif title:
            ax.text(x + w/2, y + h/2, title, ha='center', va='center', fontsize=tsize, fontweight='bold', color=col,
                    zorder=3)
        else:
            ax.text(x + w/2, y + h/2, body, ha='center', va='center', fontsize=bsize, color=col, zorder=3,
                    linespacing=1.25)

    def arrow(p, q, color=INK2, lw=0.8, rad=0.0):
        ax.add_patch(FancyArrowPatch(p, q, arrowstyle='-|>', mutation_scale=7, lw=lw, color=color, zorder=1,
                                     connectionstyle=f'arc3,rad={rad}', shrinkA=0, shrinkB=0))

    def note(x, y, s, ha='center', va='center'):
        ax.text(x, y, s, ha=ha, va=va, fontsize=5.4, color=INK2, style='italic', zorder=3, linespacing=1.05)

    # legend (top)
    items = [('red', 'exact reduction (earlier work)'), ('new', 'new analytic proof'),
             ('cap', 'computer-assisted proof (interval arithmetic)'), ('res', 'main results')]
    xs = [4, 49, 87, 152]
    for xx, (k, lab) in zip(xs, items):
        ax.add_patch(FancyBboxPatch((xx, H - 4.6), 4.0, 2.3, boxstyle='round,pad=0.15,rounding_size=0.6',
                                    fc=styles[k]['fc'], ec=styles[k]['ec'], lw=0.6))
        ax.text(xx + 5.5, H - 3.45, lab, fontsize=5.9, va='center', color=INK2)

    # row 1: exact reduction
    y1, h1 = 77, 16
    box(4, y1, 42, h1, 'Bell strategy', r'projective measurements' + '\n' + r'on $\Phi_D$, any dimension $D$', 'red')
    box(68, y1, 48, h1, 'Clock model', r'$d$ unitaries $V_k$, $V_k^4=1$' + '\n' + r'$I_d=4F(V)/(d(d-1))$', 'red')
    box(138, y1, 41, h1, 'Circle configuration', r'$4d$ projections $Q_x$' + '\n' +
        r'$F-F_{\rm DKZ}=\frac{1}{2}\langle v,\delta\rangle$', 'red')
    arrow((46.6, y1 + h1/2 - 1.5), (67.4, y1 + h1/2 - 1.5)); note(57, y1 + h1/2 + 2.3, 'twirl +\nStone-von Neumann')
    arrow((116.6, y1 + h1/2 - 1.5), (137.4, y1 + h1/2 - 1.5)); note(127, y1 + h1/2 + 2.3, 'spectral\nprojections')

    # row 2: analytic chain
    y2, h2 = 46, 21
    bw, gp, x0 = 33, 14, 4
    bx = [x0 + i*(bw + gp) for i in range(4)]
    box(bx[0], y2, bw, h2, 'Theorem 4', 'two-variable BMV\nwith explicit density\n'
        + r'$F=\frac{1}{2\pi}\sum_i|{\rm Im}\,x_i|\geq0$', 'new')
    box(bx[1], y2, bw, h2, 'Theorem 3', 'strip inequality for\nevery matrix size\n'
        + r'$\sum h_\lambda(\nu)\geq{\rm Tr}[(P(g-\lambda)P)_+]$', 'new', bsize=5.6)
    box(bx[2], y2, bw, h2, 'Continuum theorem', 'operator fields on\na circle reach only\nthe classical value '
        + r'$\Phi_c$', 'new')
    box(bx[3], y2, bw, h2, 'Cell inequalities', r'$\langle u^{\ell},\delta\rangle\leq0$' + '\nfor every\n'
        + r'cell vector $\ell$', 'new')
    labels = ['strip Poisson\nkernel', 'harmonic\nextension,\nbathtub', 'embed in\ncells, rotate']
    for i in range(3):
        xa, xb = bx[i] + bw + 0.6, bx[i + 1] - 0.6
        arrow((xa, y2 + h2/2 - 3.0), (xb, y2 + h2/2 - 3.0))
        note((xa + xb)/2, y2 + h2/2 + 2.6, labels[i])
    # circle configuration feeds the cell inequalities
    arrow((158.5, y1 - 0.6), (bx[3] + bw/2 + 1.0, y2 + h2 + 0.6))

    # row 3: CONE_d and Theorem 1
    y3, h3 = 19.5, 20.5
    box(4, y3, 92, h3, None, '', 'cap')
    ax.text(50, y3 + h3 - 3.0, r'CONE$_d$:  $v$ is a positive combination of the cell vectors $u^{\ell}$',
            ha='center', va='center', fontsize=6.6, fontweight='bold', zorder=3)
    chips = [(r'$2\leq d\leq200$', 'exact rational cells,\ninterval arithmetic'),
             (r'$201\leq d\leq2000$', 'Gaussian-modulated\nDirichlet cells'),
             (r'every $d\geq2001$', 'analytic proof with\ninterval Taylor models')]
    for i, (t1, t2) in enumerate(chips):
        cx = 7.5 + i*29.0
        ax.add_patch(FancyBboxPatch((cx, y3 + 1.6), 27.0, 11.6, boxstyle='round,pad=0.3,rounding_size=1.2',
                                    fc='white', ec=C_VERM, lw=0.6, zorder=3))
        ax.text(cx + 13.5, y3 + 10.0, t1, ha='center', va='center', fontsize=6.2, fontweight='bold', color=C_VERM,
                zorder=4)
        ax.text(cx + 13.5, y3 + 4.9, t2, ha='center', va='center', fontsize=5.5, color=INK, zorder=4,
                linespacing=1.1)
    box(108, y3, 71, h3, 'Theorem 1 (optimality)', r'$I_d\leq I_{\rm ME}(d)$ for every $d\geq2$ and every'
        + '\nprojective strategy on ' + r'$\Phi_D$:  $\langle v,\delta\rangle=$' + '\n' +
        r'$\int\langle u^{\ell},\delta\rangle\,d\mu(\ell)+\sum_s w_s\langle t_s,\delta\rangle\leq0$', 'res',
        tsize=7.0, bsize=6.0)
    arrow((96.6, y3 + h3/2), (107.4, y3 + h3/2))
    arrow((bx[3] + bw/2 + 1.0, y2 - 0.6), (bx[3] + bw/2 - 4.0, y3 + h3 + 0.6))

    # row 4: rigidity
    y4, h4 = 2, 12
    box(108, y4, 71, h4, 'Theorem 2 (rigidity)', r'equality $\Rightarrow$ DKZ$\,\otimes\,\mathbf{1}$ up to $u\otimes\bar u$',
        'res', tsize=6.8, bsize=6.1)
    arrow((171, y3 - 0.6), (171, y4 + h4 + 0.6))
    note(169.5, (y3 + y4 + h4)/2, 'equality\ncase', ha='right')
    steps = [(r'$[B(\theta),g(\theta)]=0$' + '\nequality in Theorem 3'),
             ('all ' + r'$Q_x$' + ' commute\nresidue lemma'),
             ('commuting clock model\nclassical theorem (earlier work)')]
    sx = [4, 33, 62]
    sw = [25, 25, 34]
    for i, (x_, w_, s_) in enumerate(zip(sx, sw, steps)):
        box(x_, y4 + 0.8, w_, h4 - 1.6, None, s_, 'eq', bsize=5.4, lw=0.6)
        nxt = sx[i + 1] if i < 2 else 108
        arrow((x_ + w_ + 0.5, y4 + h4/2), (nxt - 0.5, y4 + h4/2), lw=0.6)
    save(fig, 'fig2')


# ================================================================================================ Figures 3 and 4
SEED_EX = 2
M_EX, R_EX = 5, 2


def example():
    rng = np.random.default_rng(SEED_EX)
    return instance(M_EX, R_EX, rng)


def eigen_paths(B, g, nt=400):
    """eigenvalues of B + i(g_d + t g_o), 0 <= t <= 1, tracked by optimal assignment."""
    M = B.shape[0]; P = np.eye(M) - B
    gd = B @ g @ B + P @ g @ P
    go = g - gd
    ts = np.linspace(0, 1, nt)
    paths = np.zeros((nt, M), complex)
    prev = None
    for i, t in enumerate(ts):
        ev = np.linalg.eigvals(B + 1j*(gd + t*go))
        if prev is not None:
            r, c = linear_sum_assignment(np.abs(prev[:, None] - ev[None, :]))
            ev = ev[c[np.argsort(r)]]
        else:
            ev = ev[np.argsort(ev.imag)]
        paths[i] = ev
        prev = ev
    return ts, paths


def figure3():
    B, g = example()
    M = B.shape[0]; P = np.eye(M) - B
    nu = np.linalg.eigvals(B + 1j*g)
    bb, pp = compressions(B, g)
    ev = np.linalg.eigvalsh(g)
    lam0 = 0.5
    ts, paths = eigen_paths(B, g)
    y_lo, y_hi = -3.0, 3.6

    lams = np.linspace(-3.2, 3.8, 701)
    L, R = lhs_star(B, g, lams), rhs_star(B, g, lams)
    defect = L - R
    print(f'[fig3] example: M = {M}, rank B = {R_EX}, spec(B+ig) = {np.round(np.sort_complex(nu), 3)}')
    print(f'[fig3] spec(PgP) = {np.round(pp, 4)}, spec(BgB) = {np.round(bb, 4)}, ||BgP||_F^2 = '
          f'{np.linalg.norm(B @ g @ P)**2:.6f}')
    print(f'[fig3] min defect over lambda grid = {defect.min():.3e} (at the edges of the grid), max = {defect.max():.4f}')

    yy = np.linspace(y_lo, y_hi, 4000)
    dens = sum(K_strip(n.real, n.imag - yy) for n in nu)
    print(f'[fig3] swept measure: mass {np.trapezoid(dens, yy):.4f} (rank P = {M - R_EX}; tails beyond the plotted '
          f'range excluded), max density {dens.max():.3f}')

    fig = plt.figure(figsize=(183*MM, 68*MM))
    axL = fig.add_axes([0.065, 0.15, 0.135, 0.76])
    axS = fig.add_axes([0.212, 0.15, 0.30, 0.76], sharey=axL)
    axR = fig.add_axes([0.655, 0.15, 0.33, 0.76])

    # (b) strip
    X, Y = np.meshgrid(np.linspace(0, 1, 401), np.linspace(y_lo, y_hi, 661))
    H = h_lam(X + 1j*Y, lam0)
    im = axS.imshow(H, origin='lower', aspect='auto', extent=[0, 1, y_lo, y_hi], cmap=SEQ_BLUE,
                    norm=PowerNorm(0.6, vmin=0, vmax=H.max()), interpolation='bilinear', zorder=0)
    axS.contour(X, Y, H, levels=[0.05, 0.25, 0.5, 1.0, 1.5, 2.0, 2.5], colors='white', linewidths=0.45,
                alpha=0.9, zorder=1)
    for j in range(M):
        axS.plot(paths[:, j].real, paths[:, j].imag, color='#2b2b2b', lw=0.5, alpha=0.75, zorder=2)
    p0 = paths[0]
    axS.plot(p0.real, p0.imag, 'o', ms=3.6, mfc='white', mec=INK, mew=0.7, zorder=4, clip_on=False)
    axS.plot(nu.real, nu.imag, 'o', ms=4.4, mfc=C_VERM, mec='white', mew=0.6, zorder=5)
    axS.set_xlim(0, 1); axS.set_ylim(y_lo, y_hi)
    axS.set_xlabel(r'${\rm Re}\,\nu$')
    axS.set_xticks([0, 0.5, 1])
    axS.set_xticklabels(['0', '0.5', '1'])
    axS.tick_params(axis='y', labelleft=False, left=False)
    axS.set_title(r'eigenvalues of $B+ig$ in the strip; colour: $h_\lambda$', fontsize=6.4)
    axS.text(0.975, y_hi - 0.15, r'$h_\lambda=0$', ha='right', va='top', fontsize=5.8, color=INK, rotation=90)
    axS.plot([0, 0], [lam0, y_hi], color=C_BLUE, lw=2.6, solid_capstyle='butt', zorder=3, clip_on=False)
    axS.plot([0], [lam0], marker='_', ms=6, mew=1.0, color=INK, zorder=4, clip_on=False)
    axS.text(0.035, lam0 - 0.06, r'$\lambda$', ha='left', va='top', fontsize=6.2, color=INK)
    axS.text(0.04, 3.32, r'$h_\lambda=(y-\lambda)_+$', ha='left', va='center', fontsize=5.8, color='white')
    for s_ in ['top', 'right']:
        axS.spines[s_].set_visible(True)
    cax = fig.add_axes([0.522, 0.53, 0.008, 0.38])
    cb = fig.colorbar(im, cax=cax)
    cb.ax.tick_params(labelsize=5, length=1.5)
    cb.outline.set_linewidth(0.4)
    cb.set_label(r'$h_\lambda(\nu)$', fontsize=6, labelpad=1)
    handles = [Line2D([], [], marker='o', ls='', ms=4.4, mfc=C_VERM, mec='white', mew=0.6, label=r'spec$(B+ig)$'),
               Line2D([], [], marker='o', ls='', ms=3.6, mfc='white', mec=INK, mew=0.7,
                      label=r'spec$(B+ig_{\rm d})$, commuting'),
               Line2D([], [], color='#2b2b2b', lw=0.6, label=r'$g_{\rm d}\to g$')]
    axS.legend(handles=handles, loc='lower right', bbox_to_anchor=(1.0, 0.0), fontsize=5.2, handletextpad=0.3,
               borderpad=0.35, frameon=True, framealpha=0.9, edgecolor='none', facecolor='white')
    panel_label(axS, 'b', x=0.0, y=1.02)

    # (a) swept measure on the left edge vs spec(PgP)
    axL.fill_betweenx(yy, 0, dens, color=C_BLUE, alpha=0.20, lw=0)
    axL.plot(dens, yy, color=C_BLUE, lw=0.9)
    for v in pp:
        axL.annotate('', xy=(1.0, v), xytext=(0.0, v), arrowprops=dict(arrowstyle='-|>', lw=0.9, color=INK,
                                                                      mutation_scale=6, shrinkA=0, shrinkB=0))
    xmax = 1.08*dens.max()
    axL.set_xlim(xmax, 0)
    axL.set_ylim(y_lo, y_hi)
    axL.set_ylabel(r'${\rm Im}\,\nu$')
    axL.set_xlabel('mass density')
    axL.spines['left'].set_visible(True)
    axL.spines['right'].set_visible(True)
    axL.text(0.62*xmax, -2.45, 'swept\neigenvalues', color=C_BLUE, fontsize=5.6, ha='center', va='center',
             linespacing=1.0)
    axL.text(0.93*xmax, pp[0] - 0.42, r'spec$(PgP)$' + '\n(unit masses)', color=INK, fontsize=5.4, ha='left',
             va='top', linespacing=1.0)
    axL.set_title('swept to the left edge', fontsize=6.4)
    panel_label(axL, 'a', x=-0.2, y=1.02)

    # (c) both sides vs lambda
    ax = axR
    ax.fill_between(lams, R, L, color=C_VERM, alpha=0.22, lw=0, zorder=1)
    ax.plot(lams, L, color=C_BLUE, lw=1.1, zorder=3)
    ax.plot(lams, R, color=INK, lw=1.0, zorder=2)
    ax.axvline(lam0, color=MUTED, lw=0.5, ls=(0, (2, 2)), zorder=0)
    ax.text(lam0 + 0.08, 6.9, r'$\lambda$ of panel b', fontsize=5.6, color=INK2, va='center')
    xl = -0.85
    ax.annotate(r'left side: $\sum_k h_\lambda(\nu_k)$', xy=(xl, lhs_star(B, g, xl)[0]), xytext=(-0.35, 5.75),
                fontsize=6.1, color=C_BLUE, va='center', arrowprops=dict(arrowstyle='-', lw=0.5, color=C_BLUE))
    xr = 0.3
    ax.annotate(r'right side: ${\rm Tr}[(P(g-\lambda)P)_+]$', xy=(xr, rhs_star(B, g, xr)[0]), xytext=(-3.1, 1.15),
                fontsize=6.1, color=INK, va='center', arrowprops=dict(arrowstyle='-', lw=0.5, color=INK))
    xm = 1.15
    ym = 0.5*(lhs_star(B, g, xm)[0] + rhs_star(B, g, xm)[0])
    ax.annotate('defect, positive for every ' + r'$\lambda$', xy=(xm, ym), xytext=(1.0, 4.3), fontsize=6.0,
                color=C_VERM, va='center', arrowprops=dict(arrowstyle='-', lw=0.5, color=C_VERM))
    for v in pp:
        ax.plot([v], [0], marker='|', ms=5, mew=0.8, color=INK, clip_on=False, zorder=4)
    ax.set_xlim(lams[0], lams[-1])
    ax.set_ylim(-0.15, 7.3)
    ax.set_xlabel(r'threshold $\lambda$')
    ax.set_ylabel('value')
    ax.set_title('both sides of the strip inequality', fontsize=6.4)
    panel_label(ax, 'c', x=-0.1, y=1.02)
    save(fig, 'fig3')
    return {'lam0': lam0}


def figure4():
    B, g = example()
    M = B.shape[0]; P = np.eye(M) - B
    bb, pp = compressions(B, g)
    ev = np.linalg.eigvalsh(g)
    bgp = np.linalg.norm(B @ g @ P)**2

    def compute():
        s = np.linspace(ev[0], ev[-1], 900)
        tau = np.linspace(0.0015, 0.9985, 600)
        Fg = np.array([F_vals(B, g, s, t) for t in tau])
        lam_mark = np.linspace(-2.6, 3.0, 15)
        def fun(t):
            return slice_integral(B, g, t, lambda x: K_strip(1 - t, x[:, None] - lam_mark[None, :]), len(lam_mark),
                                  extra=tuple(lam_mark), tol=1e-11)
        V = tau_integral(fun, len(lam_mark), tol=1e-9)
        tau_m = np.array([0.003, 0.02, 0.08, 0.2, 0.35, 0.5, 0.65, 0.8, 0.92, 0.98, 0.997])
        marg = np.array([slice_integral(B, g, t, lambda x: np.ones((len(x), 1)), 1)[0] for t in tau_m])
        return {'s': s, 'tau': tau, 'F': Fg, 'lam_mark': lam_mark, 'V': V, 'tau_m': tau_m, 'marg': marg}
    data = cached('fig4_density', compute)
    s, tau, Fg = data['s'], data['tau'], data['F']
    lam_mark, V, tau_m, marg = data['lam_mark'], data['V'], data['tau_m'], data['marg']
    direct = lhs_star(B, g, lam_mark) - rhs_star(B, g, lam_mark)
    err_bal = np.max(np.abs(direct - V))
    err_marg = np.max(np.abs(marg - bgp))
    print(f'[fig4] F >= 0 on the grid (min {Fg.min():.1e}); defect vs balayage max |diff| = {err_bal:.1e} '
          f'(defects {direct.min():.4f} .. {direct.max():.4f}); tau-marginals vs ||BgP||^2 = {bgp:.12f}: '
          f'max |diff| = {err_marg:.1e}')

    # M = 2 example
    al, be, cc = -1.0, 1.25, 0.65
    B2 = np.diag([1.0, 0.0]); g2 = np.array([[al, cc], [cc, be]])

    def F2(sv, t):
        R2 = 4*t*(1 - t)*cc**2 - (sv - (t*be + (1 - t)*al))**2
        return np.sqrt(np.maximum(R2, 0))/(2*PI*t*(1 - t))
    chk = max(np.max(np.abs(F_vals(B2, g2, np.linspace(-1.6, 1.8, 300), t) - F2(np.linspace(-1.6, 1.8, 300), t)))
              for t in (0.1, 0.3, 0.5, 0.7, 0.9))
    print(f'[fig4] M = 2: semicircle formula vs eigenvalue computation, max |diff| = {chk:.1e}')

    fig = plt.figure(figsize=(183*MM, 112*MM))
    axF = fig.add_axes([0.065, 0.56, 0.47, 0.39])
    caxF = fig.add_axes([0.545, 0.56, 0.009, 0.39])
    axM = fig.add_axes([0.66, 0.56, 0.32, 0.39])
    axD = fig.add_axes([0.065, 0.08, 0.47, 0.36])
    axT = fig.add_axes([0.66, 0.08, 0.32, 0.36])

    # (a) density
    vmax = np.percentile(Fg, 99.7)
    im = axF.imshow(Fg, origin='lower', aspect='auto', extent=[s[0], s[-1], tau[0], tau[-1]], cmap=SEQ_VERM,
                    norm=PowerNorm(0.5, vmin=0, vmax=vmax), interpolation='bilinear')
    axF.plot(bb, np.zeros_like(bb) - 0.035, '^', ms=4.0, color=INK, clip_on=False)
    axF.plot(pp, np.ones_like(pp) + 0.035, 'v', ms=4.0, color=INK, clip_on=False)
    axF.text(s[0] + 0.08, 0.035, r'$\blacktriangle$ spec$(BgB)$ at $\tau=0$', fontsize=5.8, va='bottom', ha='left',
             color=INK)
    axF.text(s[-1] - 0.08, 0.965, r'$\blacktriangledown$ spec$(PgP)$ at $\tau=1$', fontsize=5.8, va='top',
             ha='right', color=INK)
    axF.set_xlim(s[0], s[-1]); axF.set_ylim(0, 1)
    axF.set_xlabel(r'$s$')
    axF.set_ylabel(r'$\tau$')
    for sp in ['top', 'right']:
        axF.spines[sp].set_visible(True)
    cb = fig.colorbar(im, cax=caxF)
    cb.ax.tick_params(labelsize=5, length=1.5)
    cb.outline.set_linewidth(0.4)
    cb.set_label(r'$F(s,\tau)=\frac{1}{2\pi}\sum_i|{\rm Im}\,x_i(s,\tau)|$', fontsize=6, labelpad=2)
    panel_label(axF, 'a', x=-0.075, y=1.04)

    # (b) M = 2 semicircles
    ax = axM
    tauk = np.linspace(0.1, 0.9, 9)
    sv = np.linspace(-1.9, 2.1, 1200)
    scale = 0.2
    for t in tauk[::-1]:
        f = F2(sv, t)
        ax.fill_between(sv, t, t + scale*f, color=C_VERM, alpha=0.25, lw=0, zorder=2)
        ax.plot(sv[f > 0], t + scale*f[f > 0], color=C_VERM, lw=0.8, zorder=3)
        ax.plot(sv, np.full_like(sv, t), color=HAIR, lw=0.4, zorder=1)
        num_s = np.linspace(t*be + (1 - t)*al - 2*cc*np.sqrt(t*(1 - t)), t*be + (1 - t)*al + 2*cc*np.sqrt(t*(1 - t)), 7)
        ax.plot(num_s, t + scale*F_vals(B2, g2, num_s, t), 'o', ms=1.6, color=INK, zorder=4)
    ax.plot([al, be], [0, 1], color=INK2, lw=0.5, ls=(0, (2, 2)))
    ax.plot([al], [0], '^', ms=4, color=INK, clip_on=False); ax.plot([be], [1], 'v', ms=4, color=INK, clip_on=False)
    ax.set_xlim(-1.9, 2.1); ax.set_ylim(0, 1.2)
    ax.set_xlabel(r'$s$'); ax.set_ylabel(r'$\tau$ (slices offset by $\tau$)')
    ax.set_yticks([0, 0.25, 0.5, 0.75, 1.0])
    ax.text(-1.85, 1.15, r'$M=2$: every slice is a semicircle of mass $|c|^2$', fontsize=5.9, va='top')
    panel_label(ax, 'b', x=-0.13, y=1.04)

    # (c) defect = balayage
    ax = axD
    lg = np.linspace(-3.4, 3.9, 800)
    dg = lhs_star(B, g, lg) - rhs_star(B, g, lg)
    ax.fill_between(lg, 0, dg, color=C_VERM, alpha=0.18, lw=0)
    ax.plot(lg, dg, color=C_VERM, lw=1.1, label=r'defect $\sum_k h_\lambda(\nu_k)-{\rm Tr}[(P(g-\lambda)P)_+]$')
    ax.plot(lam_mark, V, 'o', ms=3.6, mfc='white', mec=INK, mew=0.8,
            label=r'$\int\!\!\int K_{1-\tau}(s-\lambda)\,F(s,\tau)\,ds\,d\tau$')
    ax.set_xlim(lg[0], lg[-1]); ax.set_ylim(0, 1.25)
    ax.set_xlabel(r'threshold $\lambda$'); ax.set_ylabel('defect of the strip inequality')
    ax.legend(loc='upper left', handlelength=1.6)
    mant, expo = f'{err_bal:.1e}'.split('e')
    ax.text(0.02, 0.5, 'largest difference\n' + r'$%s\times10^{%d}$' % (mant, int(expo)),
            transform=ax.transAxes, ha='left', va='center', fontsize=5.8, color=INK2, linespacing=1.2)
    panel_label(ax, 'c', x=-0.075, y=1.02)

    # (d) tau-marginals
    ax = axT
    ax.axhline(bgp, color=INK, lw=0.9)
    ax.plot(tau_m, marg, 'o', ms=3.6, mfc='white', mec=C_VERM, mew=0.9, zorder=3)
    ax.axhline(cc**2, color=MUTED, lw=0.9)
    tt = np.array([0.02, 0.1, 0.3, 0.5, 0.7, 0.9, 0.98])
    m2 = []
    for t in tt:
        lo_, hi_ = t*be + (1 - t)*al - 2*cc*np.sqrt(t*(1 - t)), t*be + (1 - t)*al + 2*cc*np.sqrt(t*(1 - t))
        xg, wg = np.polynomial.legendre.leggauss(80)
        th = (xg + 1)*PI/2
        sx = lo_ + (hi_ - lo_)*(1 - np.cos(th))/2
        m2.append(np.sum(wg*PI/2*(hi_ - lo_)*np.sin(th)/2*F_vals(B2, g2, sx, t)))
    ax.plot(tt, m2, 's', ms=3.0, mfc='white', mec=MUTED, mew=0.8, zorder=3)
    ax.text(0.5, bgp + 0.25, r'example of a: $\|BgP\|_F^2=%.3f$' % bgp, ha='center', fontsize=5.9)
    ax.text(0.5, cc**2 + 0.25, r'$M=2$ example: $|c|^2=%.4f$' % cc**2, ha='center', fontsize=5.9, color=INK2)
    ax.set_xlim(0, 1); ax.set_ylim(0, bgp + 1.3)
    ax.set_xlabel(r'$\tau$'); ax.set_ylabel(r'$\int F(s,\tau)\,ds$')
    panel_label(ax, 'd', x=-0.13, y=1.02)
    save(fig, 'fig4')
    return {'err_bal': err_bal, 'err_marg': err_marg, 'bgp': bgp, 'chk2': chk}


# ================================================================================================ Figure 5
def _q(s):
    """Exact value of a number stored in a certificate file (exact rational 'p/q' or a finite decimal string)."""
    return Fraction(s)


def load_certs():
    """Read the certificates.  2 <= d <= 200: exact LP certificates (certs/cert_d*.json).  201 <= d <= 2000: the
    single-run certificates of verify_cert.py (logs/cert_g_d*.json; every bound is the exact decimal expansion of the
    lower endpoint of a certified enclosure, computed on the widened Poincare-Miranda box).  d >= 2001: the interval
    Taylor-model boxes of the final run (logs/alld/zone*_*.json; exact rationals stored as strings)."""
    lp = []
    for f in glob.glob(os.path.join(QD2, 'certs', 'cert_d*.json')):
        c = json.load(open(f))
        m = re.search(r'min certified lambda >= ([0-9.eE+-]+)', c['note'])
        lp.append((c['d'], float(m.group(1)), len(c['cells']), min(min(x) for x in c['cells'])/c['q']))
    lp.sort()
    cg = []
    for f in glob.glob(os.path.join(QD2, 'logs', 'cert_g_d*.json')):
        c = json.load(open(f))
        d = c['d']
        if not 201 <= d <= 2000:
            continue
        b = c['bounds']
        at = Decimal(b['at_min_lo'])*d*d                              # d^2 min_k a_k
        sl = Decimal(b['slack_min_lo'])*d                             # d min_m Delta^2 W
        ratio = Decimal(b['D_cD_lo'])/(Decimal(b['c1min_lo'])/4)      # certified inf Hc_m' / (c_1,min/4); 1 suffices
        ok = bool(c['ok']) and all(c['checks'].values())
        cg.append((d, at, sl, ratio, ok, c['code_sha256'], c['iv_prec']))
    cg.sort()
    zo, zi = [], []
    for f in sorted(glob.glob(os.path.join(QD2, 'logs', 'alld', 'zoneO_*.json'))):
        for b in json.load(open(f))['boxes']:
            zo.append(tuple(float(_q(b[k])) for k in ('xlo', 'xhi', 'qlo', 'qhi')))
    for f in sorted(glob.glob(os.path.join(QD2, 'logs', 'alld', 'zoneI_*.json'))):
        j = json.load(open(f))
        for b in j['boxes']:
            lo, hi, qlo, qhi = (_q(b[k]) for k in ('lo', 'hi', 'qlo', 'qhi'))
            if j['mode'] == 'b':
                zi.append((float(lo), float(hi), float(qlo), float(qhi)))
            else:                                  # w = 1/b boxes
                blo = float(1/hi) if hi > 0 else np.inf
                bhi = float(1/lo) if lo > 0 else np.inf
                zi.append((blo, bhi, float(qlo), float(qhi)))
    return lp, cg, zo, zi


def figure5():
    lp, cg, zo, zi = load_certs()
    lp_d = np.array([r[0] for r in lp]); lp_lam = np.array([r[1] for r in lp]); lp_K = np.array([r[2] for r in lp])
    cg_d = np.array([r[0] for r in cg])
    cg_at = np.array([float(r[1]) for r in cg])
    cg_sl = np.array([float(r[2]) for r in cg])
    cg_rt = np.array([float(r[3]) for r in cg])
    ev = cg_d % 2 == 0
    missing = sorted(set(range(201, 2001)) - set(cg_d.tolist()))

    def exact_min(rows, col):
        r = min(rows, key=lambda r: r[col])
        return r[col], r[0]
    at_e, d_e = exact_min([r for r in cg if r[0] % 2 == 0], 1)
    at_o, d_o = exact_min([r for r in cg if r[0] % 2 == 1], 1)
    sl_m, d_s = exact_min(cg, 2)
    rt_m, d_r = exact_min(cg, 3)
    kd_lo, kd_hi = (lp_K/lp_d).min(), (lp_K/lp_d).max()
    print(f'[fig5] LP certificates: {len(lp)} values of d in [{lp_d.min()}, {lp_d.max()}]; d*min(lambda) in '
          f'[{(lp_d*lp_lam).min():.4f}, {(lp_d*lp_lam).max():.4f}]; cells per d K/d in [{kd_lo:.2f}, {kd_hi:.2f}]; '
          f'smallest cell {min(r[3] for r in lp)}')
    print(f'[fig5] single-run certificates (verify_cert.py): {len(cg)} of 1800, missing {len(missing)}; all checks ok: '
          f'{all(r[4] for r in cg)}; code SHA-256 {sorted(set(r[5] for r in cg))}; '
          f'precision {sorted(set(r[6] for r in cg))} bits')
    print(f'[fig5] minima of the lower endpoints: d^2 min_k a_k = {at_e:.7f} (even d, d = {d_e}), {at_o:.7f} (odd d, '
          f'd = {d_o}); d min Delta^2 W = {sl_m:.6f} (d = {d_s}); derivative ratio = {rt_m:.6f} (d = {d_r})')
    if missing:
        print('[fig5] WARNING: certificates missing for', missing[:5], '...')
    print(f'[fig5] analytic regime: outer zone min lower bound {min(z[2] for z in zo):.4f} over {len(zo)} boxes; '
          f'inner zone min lower bound {min(z[2] for z in zi):.4f} over {len(zi)} boxes')

    fig = plt.figure(figsize=(183*MM, 122*MM))
    axT = fig.add_axes([0.335, 0.69, 0.645, 0.295])
    axB = fig.add_axes([0.07, 0.08, 0.22, 0.47])
    axC1 = fig.add_axes([0.385, 0.405, 0.24, 0.145])
    axC2 = fig.add_axes([0.385, 0.2425, 0.24, 0.145], sharex=axC1)
    axC3 = fig.add_axes([0.385, 0.08, 0.24, 0.145], sharex=axC1)
    axD1 = fig.add_axes([0.715, 0.08, 0.125, 0.47])
    axD2 = fig.add_axes([0.855, 0.08, 0.125, 0.47], sharey=axD1)

    # (a) coverage (Gantt-like)
    ax = axT
    ax.set_xscale('log')
    XMAX = 2e5
    ax.set_xlim(1.7, XMAX)
    ax.set_ylim(-0.2, 5.1)
    rows = [
        (4.8, r'Tsirelson bound ($d=2$)', [(2, 2)], MUTED, 'point'),
        (4.1, r'semidefinite numerics, $d=3$ (general measurements)', [(3, 3)], MUTED, 'point'),
        (3.4, 'exact sum-of-squares certificates (earlier work)', [(3, 20)], '#8c8c8c', 'bar'),
        (2.7, 'commuting (equal-link) strategies only (earlier work)', [(2, XMAX)], '#9a9a9a', 'hatch'),
    ]
    for y, lab, spans, col, kind in rows:
        for (a, b) in spans:
            if kind == 'point':
                ax.plot([a], [y], 'o', ms=4.0, color=col, zorder=3, clip_on=False)
            elif kind == 'bar':
                ax.add_patch(Rectangle((a, y - 0.2), b - a, 0.4, fc=col, ec='none', zorder=2))
            else:
                ax.add_patch(Rectangle((a, y - 0.2), b - a, 0.4, fc='white', ec=col, hatch='////', lw=0.5, zorder=2))
        ax.text(-0.012, y, lab, transform=ax.get_yaxis_transform(), va='center', ha='right', fontsize=6.0, color=INK2)
    # this work: the three regimes of CONE_d
    y = 1.6
    segs = [(2, 200.5, '#f4b48c'), (200.5, 2000.5, C_VERM), (2000.5, XMAX, '#8a3300')]
    for (a, b, col) in segs:
        ax.add_patch(Rectangle((a, y - 0.32), b - a, 0.64, fc=col, ec='white', lw=1.0, zorder=2))
    ax.text(np.sqrt(2*200), y, r'$2\leq d\leq200$', ha='center', va='center', fontsize=6.0, color=INK, zorder=3)
    ax.text(np.sqrt(201*2000), y, r'$201$-$2000$', ha='center', va='center', fontsize=6.0, color='white', zorder=3)
    ax.text(np.sqrt(2001*XMAX), y, r'every $d\geq2001$', ha='center', va='center', fontsize=6.0, color='white',
            zorder=3)
    ax.annotate('', xy=(XMAX*1.35, y), xytext=(XMAX*0.97, y),
                arrowprops=dict(arrowstyle='-|>', lw=0.9, color='#8a3300', mutation_scale=7), annotation_clip=False)
    ax.text(-0.012, y + 0.1, 'this work: every projective strategy', transform=ax.get_yaxis_transform(), va='bottom',
            ha='right', fontsize=6.3, fontweight='bold', color=C_VERM)
    ax.text(-0.012, y - 0.06, r'(CONE$_d$ certified in interval arithmetic)', transform=ax.get_yaxis_transform(),
            va='top', ha='right', fontsize=5.8, color=C_VERM)
    # this work: the Lean 4 formalisation
    y = 0.45
    ax.add_patch(Rectangle((2, y - 0.32), 20.5 - 2, 0.64, fc=C_BLUE, ec='white', lw=1.0, zorder=2))
    ax.add_patch(Rectangle((20.5, y - 0.32), XMAX - 20.5, 0.64, fc='#d4e6f4', ec='white', lw=1.0, zorder=2))
    ax.text(np.sqrt(2*20.5), y, 'complete', ha='center', va='center', fontsize=6.0, color='white', zorder=3)
    ax.text(np.sqrt(21*XMAX), y, r'complete except for the input CONE$_d$', ha='center', va='center',
            fontsize=6.0, color=INK, zorder=3)
    ax.annotate('', xy=(XMAX*1.35, y), xytext=(XMAX*0.97, y),
                arrowprops=dict(arrowstyle='-|>', lw=0.9, color='#8fbfe0', mutation_scale=7), annotation_clip=False)
    ax.text(-0.012, y + 0.1, 'this work: Lean 4 formal proof', transform=ax.get_yaxis_transform(), va='bottom',
            ha='right', fontsize=6.3, fontweight='bold', color=C_BLUE)
    ax.text(-0.012, y - 0.06, '(proof of Theorems 1 and 2)', transform=ax.get_yaxis_transform(),
            va='top', ha='right', fontsize=5.8, color=C_BLUE)
    ax.set_yticks([])
    ax.spines['left'].set_visible(False)
    ax.set_xlabel(r'number of outcomes $d$', labelpad=1)
    panel_label(ax, 'a', x=-0.5, y=0.97)

    # (b) LP regime
    ax = axB
    ax.plot(lp_d, lp_d*lp_lam, 'o', ms=1.9, color='#e8804a', mec='none')
    ax.set_xscale('log')
    ax.set_xlim(1.7, 230)
    ax.set_ylim(0, 0.3)
    ax.axhline(0, color=INK, lw=0.6)
    ax.set_xlabel(r'$d$')
    ax.set_ylabel(r'$d\,\times$ smallest certified weight $\lambda_k$')
    ax.text(0.04, 0.96, f'{len(lp)} certificates, ' + r'$%.1fd$-$%.1fd$ cell vectors each,' % (kd_lo, kd_hi)
            + '\nall cell lengths ' + r'$\geq1/16$; all weights $>0$', transform=ax.transAxes, fontsize=5.6, va='top',
            color=INK2, linespacing=1.15)
    panel_label(ax, 'b', x=-0.2, y=1.02)

    # (c) Gaussian regime: lower endpoints of the certified enclosures, one single-run certificate per d
    ax = axC1
    ax.plot(cg_d[ev], cg_at[ev], '.', ms=1.2, color=C_VERM, mec='none')
    ax.plot(cg_d[~ev], cg_at[~ev], '.', ms=1.2, color='#8a3300', mec='none')
    ax.text(1995, cg_at[~ev].min() - 0.008, r'odd $d$', ha='right', va='top', fontsize=5.6, color='#8a3300')
    ax.text(1995, cg_at[ev].min() - 0.008, r'even $d$', ha='right', va='top', fontsize=5.6, color=C_VERM)
    ax.set_ylim(0, 0.15)
    ax.set_yticks([0, 0.05, 0.1])
    ax.set_ylabel(r'$d^2\,\min_k\,a_k$', labelpad=2)
    ax.tick_params(axis='x', labelbottom=False)
    ax.text(0.03, 0.06, 'positive-definiteness margin', transform=ax.transAxes, fontsize=5.6, va='bottom', color=INK2)
    panel_label(ax, 'c', x=-0.2, y=1.04)
    ax = axC2
    ax.plot(cg_d, cg_sl, '.', ms=1.2, color=C_VERM, mec='none')
    ax.set_ylim(0, 0.8)
    ax.set_yticks([0, 0.3, 0.6])
    ax.set_ylabel(r'$d\,\min_m\,\Delta^2W$', labelpad=2)
    ax.tick_params(axis='x', labelbottom=False)
    ax.text(0.03, 0.06, 'slack of the symmetric remainder', transform=ax.transAxes, fontsize=5.6, va='bottom',
            color=INK2)
    ax = axC3
    ax.axhline(1.0, color=MUTED, lw=0.7, ls=(0, (3, 2)))
    ax.text(1995, 1.25, 'required: 1', fontsize=5.6, color=INK2, ha='right', va='bottom')
    ax.plot(cg_d, cg_rt, '.', ms=1.2, color=C_VERM, mec='none')
    ax.set_ylim(0, 5.2)
    ax.set_yticks([0, 2, 4])
    ax.set_xlim(150, 2050)
    ax.set_ylabel('derivative ratio', labelpad=6)
    ax.set_xlabel(r'$d$')
    ax.text(0.03, 0.47, 'Poincare-Miranda step', transform=ax.transAxes, fontsize=5.6, va='center', color=INK2)

    # (d) analytic regime: interval enclosures of the normalised fourth differences
    ax = axD1
    for (a, b, lo, hi) in sorted(zi):
        bb_ = min(b, 2e4)
        ax.add_patch(Rectangle((a, lo), bb_ - a, hi - lo, fc='#f6c4a5', ec='none', lw=0, alpha=0.9))
        ax.plot([a, bb_], [lo, lo], color='#8a3300', lw=0.7, solid_capstyle='butt')
    ax.set_xscale('log')
    ax.set_xlim(0.9, 2e4)
    ax.set_ylim(0, 15)
    ax.axhline(0.25, color=MUTED, lw=0.7, ls=(0, (3, 2)))
    ax.set_xlabel(r'position $b$ (all $d\geq2001$)')
    ax.set_ylabel(r'enclosure of normalized fourth difference')
    ax.set_title('inner zone', fontsize=6.2)
    ax.text(1.0, 0.5, 'sufficient: 1/4', fontsize=5.4, color=INK2, va='bottom')
    ax.annotate('', xy=(1.9e4, 10.0), xytext=(6e3, 10.0), arrowprops=dict(arrowstyle='-|>', lw=0.6, color='#8a3300',
                                                                        mutation_scale=5))
    panel_label(ax, 'd', x=-0.42, y=1.02)
    ax = axD2
    for (a, b, lo, hi) in sorted(zo):
        ax.add_patch(Rectangle((a, lo), b - a, hi - lo, fc='#f6c4a5', ec='none', lw=0, alpha=0.9))
        ax.plot([a, b], [lo, lo], color='#8a3300', lw=0.7, solid_capstyle='butt')
    ax.set_xlim(0, 0.51)
    ax.axhline(0.25, color=MUTED, lw=0.7, ls=(0, (3, 2)))
    ax.legend(handles=[Rectangle((0, 0), 1, 1, fc='#f6c4a5', ec='none', label='enclosure'),
                       Line2D([], [], color='#8a3300', lw=0.8, label='lower bound')], loc='lower right',
              fontsize=5.3, handlelength=1.2, bbox_to_anchor=(1.0, 0.04))
    ax.set_xlabel(r'$x=b/d$')
    ax.set_title('outer zone', fontsize=6.2)
    ax.tick_params(axis='y', labelleft=False)
    save(fig, 'fig5')
    return {'n_lp': len(lp), 'n_cert': len(cg), 'missing': missing}


if __name__ == '__main__':
    which = [a for a in sys.argv[1:] if a.isdigit()]
    todo = which or ['1', '2', '3', '4', '5']
    res = {}
    if '1' in todo:
        res['fig1'] = figure1()
    if '2' in todo:
        figure2()
    if '3' in todo:
        res['fig3'] = figure3()
    if '4' in todo:
        res['fig4'] = figure4()
    if '5' in todo:
        res['fig5'] = figure5()
    print('figures written to', OUT)
