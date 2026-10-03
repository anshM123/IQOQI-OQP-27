"""Q_rig core helpers (self-contained; conventions of QD2/LOG.md s.4 and paper-classical-all-d).

N = 4d.  Reduced family V_0..V_{d-1} in U(M), V_k^4 = 1, E_k = V_k^*.  Q_x (x in Z_N), x = k - d a (0 <= k < d, a in Z_4) is the
spectral projection of E_k for the eigenvalue i^a.  A_x = Q_x, B_x = Q_{x+d}.  kappa(u) = cot(pi u/N).
F(V) = sum_{j<k} Re[h_{k-j} tr(V_j V_k^*)] = <A,B>_tau/2 - d/2,  <A,B>_tau = sum kappa(x-y) tau(A_x B_y).
"""
import numpy as np
from scipy.special import spence

PI = np.pi


# ------------------------------------------------------------------ special functions
def cl2(theta):
    th = np.asarray(theta, float)
    out = np.imag(spence(1 - np.exp(1j * th)))
    return np.where(np.abs(np.sin(th / 2)) < 1e-300, 0.0, out)


def phic(al, be):
    return float((cl2(2 * PI * al) + cl2(2 * PI * be) + cl2(2 * PI * (1 - al - be))) / (2 * PI ** 2))


def hlam(x, y, lam):
    """strip harmonic function h_lam(x+iy): boundary data (y-lam)_+ on x = 0 and 0 on x = 1."""
    x = np.asarray(x, float)
    y = np.asarray(y, float)
    x, y = np.broadcast_arrays(x, y)
    out = np.zeros(x.shape)
    left = x <= 1e-13
    right = x >= 1 - 1e-13
    mid = ~(left | right)
    out[left] = np.clip(y[left] - lam, 0, None)
    z = np.exp(PI * (y[mid] - lam)) * np.exp(-1j * PI * x[mid])
    out[mid] = -np.imag(spence(1 - z)) / PI ** 2
    return out


def lam_star(al, be):
    """minimiser of lam -> lam*al + h_lam(be) (Legendre identity, Q-L12): lam* = (1/pi) log(sin(pi(al+be))/sin(pi al))."""
    return (1 / PI) * np.log(np.sin(PI * (al + be)) / np.sin(PI * al))


# ------------------------------------------------------------------ discrete kernels
def cotk(N):
    k = np.zeros(N)
    k[1:] = 1.0 / np.tan(PI * np.arange(1, N) / N)
    return k


def phiN(d):
    N = 4 * d
    k = cotk(N)
    return float(sum(k[(x - y) % N] for x in range(d) for y in range(-d, 0)))


def v_vector(d):
    return np.array([2 / np.sin(PI * m / (2 * d)) for m in range(1, d)])


def Gfun(u, N):
    return -(N ** 2 / (2 * PI ** 2)) * cl2(2 * PI * np.asarray(u, float) / N)


def cell_endpoints(ell):
    ell = np.asarray(ell, float)
    lens = np.tile(ell, 4)
    return np.concatenate([[0.0], np.cumsum(lens)])        # L_0..L_N, L_N = N


def cell_kernel(ell):
    """K[x,y] = int_{I_x} int_{I_y} cot(pi(xi-eta)/N) (I_x = [L_x, L_{x+1}), |I_x| = ell_{x mod d})."""
    ell = np.asarray(ell, float)
    d = len(ell)
    N = 4 * d
    L = cell_endpoints(ell)
    a, b = L[:-1], L[1:]
    K = (Gfun(b[:, None] - a[None, :], N) - Gfun(a[:, None] - a[None, :], N)
         - Gfun(b[:, None] - b[None, :], N) + Gfun(a[:, None] - b[None, :], N))
    np.fill_diagonal(K, 0.0)
    return K


def u_window(ell):
    """QD2-L2: u_m = Delta^2_m (1/d) sum_r Ghat(S_r(m)), m = 1..d-1."""
    ell = np.asarray(ell, float)
    d = len(ell)
    N = 4 * d
    ext = np.concatenate([ell, ell])
    cs = np.concatenate([[0.0], np.cumsum(ext)])
    r = np.arange(d)[:, None]
    m = np.arange(d + 1)[None, :]
    S = cs[r + m] - cs[r]
    P = (Gfun(S, N) + Gfun(2 * d - S, N)).mean(axis=0)
    return P[2:] - 2 * P[1:-1] + P[:-2]


# ------------------------------------------------------------------ configurations
def haar(M, rng):
    Z = (rng.standard_normal((M, M)) + 1j * rng.standard_normal((M, M))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def family_from(U, S):
    """V_k = U_k diag(i^{-s_{k,mu}}) U_k^*  (U: (d,M,M), S: (d,M) integer labels)."""
    d, M = S.shape
    return np.array([U[k] @ np.diag((1j) ** (-S[k])) @ U[k].conj().T for k in range(d)])


def random_family(d, M, rng):
    U = np.array([haar(M, rng) for _ in range(d)])
    S = rng.integers(0, 4, size=(d, M))
    return family_from(U, S)


def Q_from_family(V):
    """Q[x] (x in Z_N): spectral projection of E_k = V_k^* for eigenvalue i^a, x = k - d a mod N."""
    d, M, _ = V.shape
    N = 4 * d
    Q = np.zeros((N, M, M), complex)
    for k in range(d):
        E = V[k].conj().T
        for a in range(4):
            lam = (1j) ** a
            # spectral projection by the Lagrange polynomial prod_{b != a} (E - i^b)/(i^a - i^b) (E normal, E^4 = 1)
            P = np.eye(M, dtype=complex)
            for b in range(4):
                if b != a:
                    P = P @ (E - (1j) ** b * np.eye(M)) / (lam - (1j) ** b)
            Q[(k - d * a) % N] = P
    return Q


def AB(Q):
    d = Q.shape[0] // 4
    return Q.copy(), np.roll(Q, -d, axis=0)          # A_x = Q_x, B_x = Q_{x+d}


def pair_matrix(X, Y):
    M = X.shape[-1]
    return np.einsum('xij,yji->xy', X, Y).real / M


def F_clock(V):
    d, M, _ = V.shape
    F = 0.0
    for j in range(d):
        for k in range(j + 1, d):
            m = k - j
            psi = PI * m / (2 * d)
            h = 1 / np.cos(psi) - 1j / np.sin(psi)
            F += (h * np.trace(V[j] @ V[k].conj().T) / M).real
    return F


def F_DKZ(d):
    return sum((d - m) / np.cos(PI * m / (2 * d)) for m in range(1, d))


def counts(Q):
    """T(m) = sum_y tau(A_{y+m} B_y), N(m) = T(m) - T(-m), delta_m = N(m) - m (m = 1..d-1)."""
    N = Q.shape[0]
    d = N // 4
    A, B = AB(Q)
    P = pair_matrix(A, B)
    T = np.array([sum(P[(y + m) % N, y] for y in range(N)) for m in range(N)])
    Nm = np.array([T[m] - T[(-m) % N] for m in range(N)])
    delta = np.array([Nm[m] - m for m in range(1, d)])
    return P, T, Nm, delta


def commutator_norm(Q):
    N = Q.shape[0]
    return max(np.linalg.norm(Q[x] @ Q[y] - Q[y] @ Q[x]) for x in range(N) for y in range(N))
