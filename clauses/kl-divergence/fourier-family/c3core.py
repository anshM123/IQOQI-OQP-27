"""
c3core.py -- numerics for the KL (van Dam-Gruenwald-Gill) strength of rank-one PVM strategies on Phi_3.
Written from scratch for THEORY_C2C3 (imports nothing from P4_kl).  Numerics only; nothing here is a proof.

Conventions.  A strategy is U[m] (m = 0..3) = (A_0, A_1, Bt_0, Bt_1), 3x3 unitaries whose columns are basis vectors;
Bt_y = conj(B_y) is the basis of Alice-side "steered" states phi^y_b.  The behaviour is
    q[x, y, a, b] = |<alpha^x_a | phi^y_b>|^2 / 3 = |(A_x^H Bt_y)_{ab}|^2 / 3      (max-ent identity on Phi_3).
Deterministic strategies lam = (a0, a1, b0, b1); cells i = ((x*2+y)*3+a)*3+b.
S^UNI(q) = min over local p of (1/4) sum_xy D(q_xy || p_xy)  (nats).
"""
import itertools
import math
import numpy as np

LOG2 = math.log(2.0)
S0_BITS = 0.05778302549332865
S0 = S0_BITS * LOG2                     # nats
W3 = np.exp(2j * np.pi / 3)

STRATS = np.array(list(itertools.product(range(3), repeat=4)))   # 81 x 4
EMAT = np.zeros((81, 36))
for _x in range(2):
    for _y in range(2):
        EMAT[np.arange(81), ((_x * 2 + _y) * 3 + STRATS[:, _x]) * 3 + STRATS[:, 2 + _y]] = 1.0


def fourier_basis(shift, sign=+1):
    """columns: 3^-1/2 sum_k w^{sign*k(a+shift)} |k>, a = 0,1,2"""
    k = np.arange(3)
    return np.array([np.exp(sign * 2j * np.pi * k * (a + shift) / 3) / np.sqrt(3) for a in range(3)]).T


def dkz():
    """DKZ_3: A_x = F(alpha_x), alpha = (1/2, 0); Bt_y = conj(B_y), B_y columns 3^-1/2 sum_k w^{-k(b+beta_y)}|k>,
    beta = (1/4, -1/4), so Bt_y columns are 3^-1/2 sum_k w^{+k(b+beta_y)}|k>."""
    return np.array([fourier_basis(0.5), fourier_basis(0.0), fourier_basis(0.25), fourier_basis(-0.25)])


def corr(U):
    """q[x,y,a,b]"""
    M = np.einsum("xka,ykb->xyab", U[0:2].conj(), U[2:4])
    return (np.abs(M) ** 2) / 3.0


def em_solve(q, w=None, iters=3000, tol=1e-15):
    """min_w (1/4) sum D(q_xy||p_xy(w)); returns (value, certified lower bound, w, p) in nats."""
    s = q.reshape(36) / 4.0
    if w is None:
        w = np.full(81, 1.0 / 81)
    for it in range(iters):
        p = w @ EMAT
        g = EMAT @ (s / p)
        w_new = w * g
        w_new /= w_new.sum()
        if np.max(np.abs(w_new - w)) < tol:
            w = w_new
            break
        w = w_new
    p = w @ EMAT
    mask = s > 0
    val = float(np.sum(s[mask] * np.log(4 * s[mask] / p[mask])))
    g = EMAT @ (s / p)
    lb = val - math.log(g.max())
    return val, lb, w, p


def s_uni(q, iters=3000):
    v, lb, _, _ = em_solve(q, iters=iters)
    return v, lb


# ---------- Hermitian basis and chart ----------
def herm_basis():
    Hs = []
    for i in range(3):
        H = np.zeros((3, 3), complex); H[i, i] = 1; Hs.append(H)
    for i in range(3):
        for j in range(i + 1, 3):
            H = np.zeros((3, 3), complex); H[i, j] = H[j, i] = 1 / np.sqrt(2); Hs.append(H)
            H = np.zeros((3, 3), complex); H[i, j] = -1j / np.sqrt(2); H[j, i] = 1j / np.sqrt(2); Hs.append(H)
    return np.array(Hs)


HB = herm_basis()


def expmh(H):
    """exp(iH) for Hermitian H"""
    ev, V = np.linalg.eigh(H)
    return (V * np.exp(1j * ev)) @ V.conj().T


def chart(U0, z):
    """U_m = exp(i sum_j z[m,j] h_j) U0_m, z in R^{4x9}"""
    z = np.asarray(z).reshape(4, 9)
    return np.array([expmh(np.einsum("j,jkl->kl", z[m], HB)) @ U0[m] for m in range(4)])


def jacobian(U0, h=1e-6):
    """d q / d z at z = 0 (36 x 36), central differences."""
    J = np.zeros((36, 36))
    for j in range(36):
        e = np.zeros(36); e[j] = h
        J[:, j] = (corr(chart(U0, e)).reshape(36) - corr(chart(U0, -e)).reshape(36)) / (2 * h)
    return J


# ---------- F3 (Fourier-shift family) ----------
def Kfun(psi):
    return (3 + 4 * np.cos(psi) + 2 * np.cos(2 * psi)) / 9.0


def f3_corr(z):
    """z = (phi00, phi01, phi10); phi11 = phi01 + phi10 - phi00; q = K(phi_xy + 2 pi (b-a)/3)/3"""
    p00, p01, p10 = z
    ph = np.array([[p00, p01], [p10, p01 + p10 - p00]])
    q = np.zeros((2, 2, 3, 3))
    for x in range(2):
        for y in range(2):
            for a in range(3):
                for b in range(3):
                    q[x, y, a, b] = Kfun(ph[x, y] + 2 * np.pi * ((b - a) % 3) / 3) / 3
    return q


def haar_unitary(rng):
    Z = (rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    d = np.diag(R)
    return Q * (d / np.abs(d))


def random_strategy(rng):
    return np.array([haar_unitary(rng) for _ in range(4)])
