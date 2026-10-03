"""Non-uniform d-periodic cell embeddings of 27B configurations.

A 27B configuration (N = 4d, A_x = Q_x, B_x = Q_{x+d}) is embedded on the circle R/NZ with cell I_x = [L_x, L_{x+1}),
L_{x+1} - L_x = ell_{x mod d} > 0, sum_r ell_r = d.  Then int B~ = sum_x ell_x B_x = sum_r ell_r * 1 = d * 1 (operator constraint)
and the same for A~, so the continuum bound (Q-T1, given (*)) gives
      Q^ell := sum_{x,y} K^ell(x,y) tau(A_x B_y) <= N^2 Phi_c(1/4,1/4),   K^ell(x,y) = int_{I_x} int_{I_y} cot(pi(xi-eta)/N),
with equality at every window (all windows embed as adjacent arcs of length d).  Averaging over rotations (which preserve the 27B
structure) gives the translation-invariant kernel Kt(m) = (1/d) sum_{r<d} K^ell(r+m, r) and the linear inequality
      <u^ell, delta> <= 0,   u^ell_m = Kt(m) + Kt(2d-m)  (m = 1..d-1),   delta_m = N(m) - m.
Target direction: v_m = 2 csc(pi m/2d)  (<A,B> - Phi_N = <v, delta>).
"""
import numpy as np
from scipy.special import spence

PI = np.pi


def cl2(theta):
    """Clausen function Cl2(theta) = Im Li2(e^{i theta}) (vectorised, float)."""
    th = np.asarray(theta, float)
    z = np.exp(1j * th)
    out = np.imag(spence(1 - z))
    return np.where(np.abs(np.sin(th / 2)) < 1e-300, 0.0, out)


def Gfun(u, N):
    """second antiderivative of cot(pi u/N) (up to linear terms): G(u) = -(N^2/2pi^2) Cl2(2 pi u/N)."""
    return -(N ** 2 / (2 * PI ** 2)) * cl2(2 * PI * np.asarray(u, float) / N)


def cell_kernel(ell):
    """Full kernel K[x, y] = int_{I_x} int_{I_y} cot(pi(xi - eta)/N) for the d-periodic cell lengths ell (length d, sum d)."""
    ell = np.asarray(ell, float)
    d = len(ell)
    N = 4 * d
    lens = np.tile(ell, 4)
    L = np.concatenate([[0.0], np.cumsum(lens)])     # L[0..N], L[N] = N
    a = L[:-1]
    b = L[1:]
    # K = G(b_x - a_y) - G(a_x - a_y) - G(b_x - b_y) + G(a_x - b_y)
    K = (Gfun(b[:, None] - a[None, :], N) - Gfun(a[:, None] - a[None, :], N)
         - Gfun(b[:, None] - b[None, :], N) + Gfun(a[:, None] - b[None, :], N))
    np.fill_diagonal(K, 0.0)
    return K


def u_vector(ell):
    """rotation-averaged kernel Kt(m) (m = 0..N-1) and the direction u_m = Kt(m) + Kt(2d - m), m = 1..d-1."""
    ell = np.asarray(ell, float)
    d = len(ell)
    N = 4 * d
    K = cell_kernel(ell)
    Kt = np.zeros(N)
    for m in range(N):
        Kt[m] = np.mean([K[(r + m) % N, r] for r in range(d)])
    u = np.array([Kt[m] + Kt[2 * d - m] for m in range(1, d)])
    return u, Kt


def v_vector(d):
    return np.array([2 / np.sin(PI * m / (2 * d)) for m in range(1, d)])


def phic(al, be):
    return (cl2(2 * PI * al) + cl2(2 * PI * be) + cl2(2 * PI * (1 - al - be))) / (2 * PI ** 2)


def tight_check(ell):
    d = len(ell)
    N = 4 * d
    u, Kt = u_vector(ell)
    lhs = sum(u[m - 1] * m for m in range(1, d)) + Kt[d] * d
    return lhs - N ** 2 * float(phic(0.25, 0.25))


def u_fast(ell):
    """same as u_vector but only computes the d x N entries K(r+m, r) (r < d): returns (u, Kt)."""
    ell = np.asarray(ell, float)
    d = len(ell)
    N = 4 * d
    lens = np.tile(ell, 4)
    L = np.concatenate([[0.0], np.cumsum(lens)])
    a = L[:-1]
    b = L[1:]
    r = np.arange(d)[:, None]
    m = np.arange(N)[None, :]
    x = (r + m) % N
    ax, bx = a[x], b[x]
    ay, by = a[r], b[r]
    K = (Gfun(bx - ay, N) - Gfun(ax - ay, N) - Gfun(bx - by, N) + Gfun(ax - by, N))
    K[:, 0] = 0.0
    Kt = K.mean(axis=0)
    u = Kt[1:d] + Kt[2 * d - np.arange(1, d)]
    return u, Kt


def Ghat_vec(u, d):
    N = 4 * d
    u = np.asarray(u, float)
    return Gfun(u, N) + Gfun(2 * d - u, N)


def u_window(ell):
    """window-sum form (QD2-L2): u_m = Delta^2_m (1/d) sum_r Ghat(S_r(m)), m = 1..d-1."""
    ell = np.asarray(ell, float)
    d = len(ell)
    ext = np.concatenate([ell, ell])
    cs = np.concatenate([[0.0], np.cumsum(ext)])
    r = np.arange(d)[:, None]
    m = np.arange(d + 1)[None, :]
    S = cs[r + m] - cs[r]                     # S_r(m), m = 0..d
    P = Ghat_vec(S, d).mean(axis=0)
    return P[2:] - 2 * P[1:-1] + P[:-2]
