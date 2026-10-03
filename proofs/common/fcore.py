"""Core numerics for the strip inequality (*) (helper module shared by several numerical checks).

(*)  sum_{nu in spec(B+ig)} h(nu) >= Tr[(PgP)_+],   B projection, P = 1-B, g Hermitian (lambda = 0 WLOG),
     h(x+iy) = -(1/pi^2) Im Li2(e^{pi y} e^{-i pi x})  (harmonic on 0<x<1, boundary y_+ on x=0, 0 on x=1).
Dual form (Q-L12): for a PVM (A,B,C) and ordered ONB,  Tr(A iT(B)) <= sum_k Phi(a_k,b_k,c_k).
"""
import numpy as np
from scipy.special import spence
from scipy.linalg import expm

PI = np.pi


# ---------------------------------------------------------------- scalar functions
def Cl2(t):
    return np.imag(spence(1 - np.exp(1j*np.asarray(t, dtype=float))))


def L(t):
    t = np.clip(np.asarray(t, dtype=float), 0.0, 1.0)
    return Cl2(2*PI*t)/(2*PI**2)


def Lp(t, eps=1e-300):
    t = np.asarray(t, dtype=float)
    return -np.log(np.maximum(2*np.sin(PI*t), eps))/PI


def Phi(a, b, c=None):
    a = np.asarray(a, float); b = np.asarray(b, float)
    if c is None:
        c = 1 - a - b
    return L(a) + L(b) + L(c)


def Li2(u):
    return spence(1 - np.asarray(u, dtype=complex))


def hstrip(nu):
    """strip harmonic function h(x+iy), eigenvalues clipped into the open strip (see Q_quantum LOG s.6 hygiene)."""
    nu = np.asarray(nu, dtype=complex)
    x = np.clip(nu.real, 1e-15, 1 - 1e-15); y = nu.imag
    out = np.empty(x.shape)
    big = y > 30.0
    # for large y use h ~ (1-x) y + exponentially small correction:  Li2(u) for |u| large via inversion
    yb = np.where(big, 0.0, y)
    u = np.exp(PI*yb)*np.exp(-1j*PI*x)
    out = -np.imag(Li2(u))/PI**2
    if np.any(big):
        # inversion: Li2(u) + Li2(1/u) = -pi^2/6 - (1/2) log^2(-u), log(-u) = pi y + i pi (1 - x) (principal)
        xb = x[big]; ybb = y[big]
        lmu = PI*ybb + 1j*PI*(1 - xb)
        ui = np.exp(-PI*ybb)*np.exp(1j*PI*xb)
        val = -PI**2/6 - 0.5*lmu**2 - Li2(ui)
        out = np.array(out, dtype=float)
        out[big] = -np.imag(val)/PI**2
    return out


def psi_fun(nu):
    """psi = i phi', phi analytic with Re phi = h:  psi(w) = -(i/pi) log(1 - e^{-i pi w});  Re psi = h_y, Im psi = h_x."""
    nu = np.asarray(nu, dtype=complex)
    x = np.clip(nu.real, 1e-15, 1 - 1e-15)
    w = x + 1j*nu.imag
    return -(1j/PI)*np.log(1 - np.exp(-1j*PI*w))


# ---------------------------------------------------------------- random matrices
def haar(M, rng):
    Z = (rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)))/np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q*(np.diag(R)/np.abs(np.diag(R)))


def rand_herm(M, rng, scale=1.0):
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M))
    return scale*(G + G.conj().T)/2


def proj_from_U(U, r):
    return U[:, :r] @ U[:, :r].conj().T


def herm_from_params(p, M):
    Hm = np.zeros((M, M), complex)
    iu = np.triu_indices(M, 1); n = len(iu[0])
    Hm[np.diag_indices(M)] = p[:M]
    Hm[iu] = p[M:M+n] + 1j*p[M+n:M+2*n]
    return Hm + np.triu(Hm, 1).conj().T


def unitary_from_params(p, M):
    Hm = herm_from_params(p, M)
    w, V = np.linalg.eigh(Hm)
    return (V*np.exp(1j*w)) @ V.conj().T


# ---------------------------------------------------------------- (*) primal quantities
def Psi(B, g):
    return float(np.sum(hstrip(np.linalg.eigvals(B + 1j*g))))


def rhs_star(B, g):
    P = np.eye(B.shape[0]) - B
    w = np.linalg.eigvalsh(P @ g @ P)
    return float(np.sum(np.maximum(w, 0.0)))


def star_defect(B, g):
    return Psi(B, g) - rhs_star(B, g)


def blocks(B, g):
    P = np.eye(B.shape[0]) - B
    gd = B @ g @ B + P @ g @ P
    go = g - gd
    return gd, go


def fmat(X, fn):
    w, V = np.linalg.eig(X)
    return (V*fn(w)) @ np.linalg.inv(V), np.linalg.cond(V)


def DC(B, g):
    """coupling-monotonicity derivative Re Tr(psi(X) g_o) (= t d/dt Psi(g_d + t g_o) at t = 1)."""
    gd, go = blocks(B, g)
    X = B + 1j*g
    w, V = np.linalg.eig(X)
    Vi = np.linalg.inv(V)
    val = np.sum(psi_fun(w)*np.diag(Vi @ go @ V))
    return float(np.real(val)), np.linalg.cond(V)


# ---------------------------------------------------------------- dual form
_S_cache = {}


def Smat(M):
    if M not in _S_cache:
        _S_cache[M] = np.sign(np.subtract.outer(np.arange(M), np.arange(M))).astype(float)
    return _S_cache[M]


def Hn(X):
    return 1j*Smat(X.shape[0])*X


def lhs_dual(A, B):
    return float(np.real(np.trace(A @ Hn(B))))


def rhs_dual(A, B, C=None):
    if C is None:
        C = np.eye(A.shape[0]) - A - B
    a = np.real(np.diag(A)); b = np.real(np.diag(B)); c = np.real(np.diag(C))
    return float(np.sum(L(a) + L(b) + L(c)))


def dual_defect(A, B, C=None):
    """RHS - LHS  (>= 0 is the claim)"""
    return rhs_dual(A, B, C) - lhs_dual(A, B)


def pvm_from_U(U, ranks):
    rA, rB, rC = ranks
    UA = U[:, :rA]; UB = U[:, rA:rA+rB]; UC = U[:, rA+rB:]
    return UA @ UA.conj().T, UB @ UB.conj().T, UC @ UC.conj().T


def dft(M):
    k = np.arange(M)
    return np.exp(2j*PI*np.outer(k, k)/M)/np.sqrt(M)
