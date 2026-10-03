"""Referee core numerics for Q_r1/PROOF.md (independent implementation; does not import the author's code)."""
import numpy as np
from scipy.special import spence
import mpmath as mp

PI = np.pi


# ------------------------------------------------------------------ strip function h, phi'
def _h0(x, y):
    """h for y <= 0 (|u| <= 1):  -(1/pi^2) Im Li2(e^{pi y} e^{-i pi x})."""
    u = np.exp(PI*y)*np.exp(-1j*PI*x)
    return -np.imag(spence(1 - u))/PI**2


def h(nu):
    """h(x+iy) via (F2) reflection: h(x+iy) = h(x-|y| i) + (1-x) y_+  (exact identity)."""
    nu = np.asarray(nu, dtype=complex)
    x = np.clip(nu.real, 0.0, 1.0); y = nu.imag
    return _h0(x, -np.abs(y)) + (1 - x)*np.maximum(y, 0.0)


def h_direct(nu):
    """h straight from the definition (for |y| moderate), used only to cross-check h()."""
    nu = np.asarray(nu, dtype=complex)
    u = np.exp(PI*nu.imag)*np.exp(-1j*PI*nu.real)
    return -np.imag(spence(1 - u))/PI**2


def phip(nu):
    """phi'(nu) = -(1/pi) log(1 - e^{-i pi nu}) (principal), overflow-safe, for 0 < Re nu < 1 (and extensions)."""
    nu0 = np.asarray(nu, dtype=complex)
    nu = np.atleast_1d(nu0)
    x = nu.real; y = nu.imag
    small = y <= 0
    w = np.exp(PI*np.where(small, y, 0.0))*np.exp(-1j*PI*x)
    out = np.array(-np.log(1 - w)/PI, dtype=complex)
    if np.any(~small):
        yb = y[~small]; xb = x[~small]
        winv = np.exp(-PI*yb)*np.exp(1j*PI*xb)
        out[~small] = -((PI*yb + 1j*PI*(1 - xb)) + np.log(1 - winv))/PI
    return out.reshape(nu0.shape)


def h_mp(nu):
    nu = mp.mpc(nu)
    x = mp.re(nu); y = mp.im(nu)
    if x <= 0:
        return max(y, 0)
    if x >= 1:
        return mp.mpf(0)
    return -mp.im(mp.polylog(2, mp.exp(mp.pi*y)*mp.exp(-1j*mp.pi*x)))/mp.pi**2


def phip_mp(nu):
    return -mp.log(1 - mp.exp(-1j*mp.pi*nu))/mp.pi


# ------------------------------------------------------------------ configurations and quantiles
def Fdist(t, x, y):
    t = np.asarray(t, float)[..., None]
    pos = x > 0
    val = np.zeros(t.shape[:-1])
    if np.any(pos):
        val = val + np.sum(0.5 + np.arctan((t - y[pos])/x[pos])/PI, axis=-1)
    if np.any(~pos):
        val = val + np.sum((t >= y[~pos]).astype(float), axis=-1)
    return val


def quantiles(x, y, iters=200):
    """integer quantiles gamma_j = min{t : F(t) >= j}, j = 1..M-1 (bisection on the predicate; exact at atoms)."""
    x = np.asarray(x, float); y = np.asarray(y, float); M = len(x)
    if M == 1:
        return np.zeros(0)
    lo0 = y.min() - 1.0 - 1e-9; hi0 = y.max() + 1.0
    js = np.arange(1, M)
    lo = np.full(M - 1, lo0); hi = np.full(M - 1, hi0)
    for _ in range(iters):
        mid = 0.5*(lo + hi)
        ok = Fdist(mid, x, y) >= js
        hi = np.where(ok, mid, hi); lo = np.where(ok, lo, mid)
        if np.max(hi - lo) < 1e-15*max(1.0, np.abs(y).max()):
            break
    g = hi.copy()
    # snap to atoms
    for k in np.where(x == 0)[0]:
        for j in range(M - 1):
            if abs(g[j] - y[k]) < 1e-9*max(1.0, abs(y[k])) and Fdist(y[k], x, y) >= j + 1:
                g[j] = y[k]
    return g


def Tfun(x, y, s=None):
    x = np.asarray(x, float); y = np.asarray(y, float)
    if s is None:
        s = x.sum()
    al = (1 - s)/s
    gam = quantiles(x, y)
    return float(np.sum(h(x + 1j*y)) - np.sum(np.maximum(gam, 0)) - al*max(np.sum(x*y), 0.0))


# ------------------------------------------------------------------ matrices
def rand_unit(M, rng):
    v = rng.normal(size=M) + 1j*rng.normal(size=M)
    return v/np.linalg.norm(v)


def rand_herm(M, rng, scale=1.0):
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M))
    return scale*(G + G.conj().T)/2


def herm_from(p, M):
    Hm = np.zeros((M, M), complex)
    iu = np.triu_indices(M, 1); n = len(iu[0])
    Hm[np.diag_indices(M)] = p[:M]
    Hm[iu] = p[M:M+n] + 1j*p[M+n:M+2*n]
    return Hm + np.triu(Hm, 1).conj().T


def unitary_from(p, M):
    Hm = herm_from(p, M)
    w, V = np.linalg.eigh(Hm)
    return (V*np.exp(1j*w)) @ V.conj().T


def compress_spec(g, v):
    """spec of PgP restricted to ran P, P = 1 - vv*."""
    M = len(v)
    P = np.eye(M) - np.outer(v, v.conj())
    w, V = np.linalg.eigh(P)
    Q = V[:, w > 0.5]
    return np.linalg.eigvalsh(Q.conj().T @ g @ Q)


def star_defect(B, g):
    P = np.eye(B.shape[0]) - B
    lhs = np.sum(h(np.linalg.eigvals(B + 1j*g)))
    w = np.linalg.eigvalsh(P @ g @ P)
    return float(lhs - np.sum(np.maximum(w, 0)))


# ------------------------------------------------------------------ mpmath versions
def to_mp(X):
    X = np.asarray(X)
    return mp.matrix([[mp.mpc(complex(X[i, j])) for j in range(X.shape[1])] for i in range(X.shape[0])])


def star_defect_mp(B, g):
    Bm = to_mp(B) if not isinstance(B, mp.matrix) else B
    gm = to_mp(g) if not isinstance(g, mp.matrix) else g
    n = Bm.rows
    E, _ = mp.eig(Bm + 1j*gm)
    lhs = mp.fsum([h_mp(e) for e in E])
    P = mp.eye(n) - Bm
    Y = P*gm*P
    Y = (Y + Y.H)/2
    w, _ = mp.eighe(Y)
    return lhs - mp.fsum([max(mp.re(e), 0) for e in w])


# ------------------------------------------------------------------ dual form
def Cl2(t):
    return np.imag(spence(1 - np.exp(1j*np.asarray(t, dtype=float))))


def Lfun(t):
    t = np.clip(np.asarray(t, dtype=float), 0.0, 1.0)
    return Cl2(2*PI*t)/(2*PI**2)


def L_mp(t):
    return mp.clsin(2, 2*mp.pi*t)/(2*mp.pi**2)


def Tri(X):
    M = X.shape[0]
    S = np.sign(np.subtract.outer(np.arange(M), np.arange(M))).astype(float)
    return S*X
