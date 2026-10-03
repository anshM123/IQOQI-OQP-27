"""
povm_core.py -- CGLMP_d on the maximally entangled state Phi_D with general POVMs.

Model.  Alice POVMs A^x (x = 0, 1), Bob POVMs B^y (y = 0, 1), d outcomes each, on C^D.
    p(a, b | x, y) = <Phi_D| A^x_a (x) B^y_b |Phi_D> = Tr(A^x_a (B^y_b)^T) / D .
Bob's transposed effects (B^y_b)^T again form a POVM, so we optimise directly over
    p(a, b | x, y) = tau(A^x_a B'^y_b),   tau = Tr / D.
Chain order of the four POVMs: g = 0: X1 = A^0, g = 1: Y1 = B'^0, g = 2: X2 = A^1, g = 3: Y2 = B'^1.
CGLMP in chain form (bell22d.cglmp_coeffs convention):
    Pi = P(X1<Y1) + P(Y1<X2) + P(X2<Y2) + P(Y2<=X1),   I = 4 - 2 (d Pi - 1)/(d - 1).
Maximising I <=> minimising Pi.

Parametrisation of a POVM: M in C^{dD x D} (blocks M_a in C^{D x D}), K = M^* M (> 0),
    E_a = K^{-1/2} M_a^* M_a K^{-1/2}       (every POVM arises, e.g. M_a = E_a^{1/2}).
Exact gradient through K^{-1/2} (Daleckii-Krein divided differences).
"""
import numpy as np

I_ME_CACHE = {}


def I_ME(d):
    k = np.arange(1, d)
    return 4.0 / (d * (d - 1)) * np.sum((d - k) / np.cos(np.pi * k / (2 * d)))


def cglmp_coeffs(d):
    """c[x, y, a, b] (x: 0 = X1, 1 = X2; y: 0 = Y1, 1 = Y2), Pi = sum c p."""
    a = np.arange(d)
    lt = (a[:, None] < a[None, :]).astype(float)
    le = (a[:, None] <= a[None, :]).astype(float)
    c = np.zeros((2, 2, d, d))
    c[0, 0] = lt          # X1 < Y1
    c[1, 0] = lt.T        # Y1 < X2
    c[1, 1] = lt          # X2 < Y2
    c[0, 1] = le.T        # Y2 <= X1
    return c


def I_from_Pi(Pi, d):
    return 4.0 - 2.0 * (d * Pi - 1.0) / (d - 1.0)


# ------------------------------------------------------------------ POVM from parameters
def povm_from_M(M, d):
    """M: (d, D, D) complex (block a = M_a, D x D).  returns E (d, D, D), aux for gradient."""
    K = np.einsum('aki,akj->ij', M.conj(), M)          # sum_a M_a^* M_a
    K = (K + K.conj().T) / 2
    lam, U = np.linalg.eigh(K)
    lam = np.maximum(lam, 1e-300)
    s = lam ** -0.5
    S = (U * s) @ U.conj().T                             # K^{-1/2}
    Ka = np.einsum('aki,akj->aij', M.conj(), M)          # M_a^* M_a
    E = S[None] @ Ka @ S[None]
    return E, (K, lam, U, s, S, Ka)


def grad_M_from_G(M, G, aux):
    """f = sum_a Tr(E_a G_a) (G_a Hermitian).  returns real gradient df/dRe M + i df/dIm M  (shape of M)."""
    K, lam, U, s, S, Ka = aux
    # df = sum_a Tr(dK_a S G_a S) + Tr(dS H),  H = sum_a (K_a S G_a + G_a S K_a)
    SGS = S[None] @ G @ S[None]
    H = np.einsum('aij,jk,akl->il', Ka, S, G)
    H = H + H.conj().T
    # Tr(dS H) = Tr(dK H'),  H' = U[(U^* H U) o Phi]U^*,  Phi_ij = (s_i - s_j)/(lam_i - lam_j)
    li, lj = lam[:, None], lam[None, :]
    si, sj = s[:, None], s[None, :]
    with np.errstate(divide='ignore', invalid='ignore'):
        Phi = (si - sj) / (li - lj)
    diag = -0.5 * lam ** -1.5
    close = np.abs(li - lj) <= 1e-12 * np.maximum(li, lj)
    Phi = np.where(close, -0.5 * (0.5 * (li + lj)) ** -1.5, Phi)
    np.fill_diagonal(Phi, diag)
    Ht = U.conj().T @ H @ U
    Hp = U @ (Ht * Phi) @ U.conj().T
    W = SGS + Hp[None]                                    # Hermitian, per a
    # dK_a = dM_a^* M_a + M_a^* dM_a  ->  Tr(dK_a W_a) = 2 Re Tr(dM_a^* M_a W_a)
    return 2.0 * (M @ W)


# ------------------------------------------------------------------ objective
class CGLMPPovm:
    def __init__(self, d, D):
        self.d, self.D = d, D
        self.c = cglmp_coeffs(d)
        self.nper = d * D * D            # complex entries per POVM
        self.n = 4 * self.nper * 2       # real parameters

    def unpack(self, z):
        d, D = self.d, self.D
        zc = z[: self.n // 2] + 1j * z[self.n // 2:]
        return [zc[g * self.nper:(g + 1) * self.nper].reshape(d, D, D) for g in range(4)]

    def pack(self, Ms):
        zc = np.concatenate([M.reshape(-1) for M in Ms])
        return np.concatenate([zc.real, zc.imag])

    @staticmethod
    def T(E, F):
        """T[a, b] = tau-less trace Tr(E_a F_b)."""
        return np.einsum('aij,bji->ab', E, F).real

    def Pi_of_E(self, Es):
        """Es = [X1, Y1, X2, Y2] (each (d, D, D)).  p(a,b|x,y) = Tr(A^x_a B^y_b)/D."""
        X = [Es[0], Es[2]]
        Y = [Es[1], Es[3]]
        Pi = 0.0
        for x in range(2):
            for y in range(2):
                Pi += np.sum(self.c[x, y] * self.T(X[x], Y[y]))
        return Pi / self.D

    def probs(self, Es):
        X = [Es[0], Es[2]]
        Y = [Es[1], Es[3]]
        p = np.zeros((2, 2, self.d, self.d))
        for x in range(2):
            for y in range(2):
                p[x, y] = self.T(X[x], Y[y]) / self.D
        return p

    def fg(self, z):
        Ms = self.unpack(z)
        Es, auxs = [], []
        for M in Ms:
            E, aux = povm_from_M(M, self.d)
            Es.append(E)
            auxs.append(aux)
        X = [Es[0], Es[2]]
        Y = [Es[1], Es[3]]
        c = self.c
        D = self.D
        # G for each POVM: d Pi / d E_a (as Hermitian matrix acting via Tr(E_a G_a))
        GX = [np.einsum('yab,ybij->aij', c[x], np.stack(Y)) / D for x in range(2)]
        # careful: Tr(E_a F_b) = Tr(E_a G) with G = F_b  (Tr(AB) linear in A with "G" = B, since Tr(A G))
        GY = [np.einsum('xab,xaij->bij', c[:, y], np.stack(X)) / D for y in range(2)]
        Pi = float(np.sum(np.einsum('aij,aji->', X[0], GX[0]).real + np.einsum('aij,aji->', X[1], GX[1]).real))
        Gs = [GX[0], GY[0], GX[1], GY[1]]
        grads = [grad_M_from_G(M, G, aux) for M, G, aux in zip(Ms, Gs, auxs)]
        gc = np.concatenate([g.reshape(-1) for g in grads])
        return Pi, np.concatenate([gc.real, gc.imag])

    def Es_of_z(self, z):
        return [povm_from_M(M, self.d)[0] for M in self.unpack(z)]


def check_povm(E, tol=1e-9):
    d, D, _ = E.shape
    s = np.abs(E.sum(0) - np.eye(D)).max()
    mine = min(np.linalg.eigvalsh((e + e.conj().T) / 2).min() for e in E)
    return s, mine


# ------------------------------------------------------------------ DKZ reference strategy
def dkz_povms(d, k=1):
    """DKZ (x) 1_k as projective POVMs in the tau-picture (Bob transposed), D = d k."""
    kk = np.arange(d)
    w = np.exp(2j * np.pi / d)
    alpha = [0.5, 0.0]          # bell22d.dkz_bases convention (matches cglmp_coeffs)
    beta = [0.25, -0.25]
    A = [np.array([w ** (kk * (a + alpha[x])) / np.sqrt(d) for a in range(d)]).T for x in range(2)]
    B = [np.array([w ** (-kk * (b + beta[y])) / np.sqrt(d) for b in range(d)]).T for y in range(2)]
    # p = |A^T B|^2/d  with columns = vectors: P^x_a = conj(a_x) a_x^T ?  use Tr(P (Q)^T)/d convention:
    # <Phi| P (x) Q |Phi> = Tr(P Q^T)/d with P = |u><u|, Q = |v><v| -> |<conj u | v>|^2/d = |u^T v|^2/d.
    Es = []
    for g in range(4):
        if g in (0, 2):
            V = A[g // 2]
            P = np.stack([np.outer(V[:, a], V[:, a].conj()) for a in range(d)])
        else:
            V = B[g // 2]
            P = np.stack([np.outer(V[:, a], V[:, a].conj()).T for a in range(d)])   # Bob transposed
        Es.append(np.stack([np.kron(P[a], np.eye(k)) for a in range(d)]))
    return Es
