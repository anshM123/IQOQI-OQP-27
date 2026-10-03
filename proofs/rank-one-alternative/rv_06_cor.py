"""Referee check of Corollaries 1-3: cyclic symmetry/antisymmetry of Tr(X iT(Y)); the Schur-basis identities;
the duality step inf_y [h(x+iy) - p y] = Phi_c(x,p); the corank <= 3 chain, step by step."""
import numpy as np
from scipy.linalg import schur
from scipy.optimize import brentq
from rv_core import h, Lfun, Tri, PI, rand_herm

rng = np.random.default_rng(606)
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

def haar(M):
    Z = (rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)))/np.sqrt(2)
    Q, R = np.linalg.qr(Z); return Q*(np.diag(R)/np.abs(np.diag(R)))
def iT(X): return 1j*Tri(X)
def Phi(a, b, c): return Lfun(a) + Lfun(b) + Lfun(c)

# (i) cyclic symmetry
ecyc = 0.0
for t in range(500):
    M = int(rng.integers(2, 9)); U = haar(M)
    r = np.sort(rng.choice(np.arange(M + 1), size=2)); A = U[:, :r[0]] @ U[:, :r[0]].conj().T
    B = U[:, r[0]:r[1]] @ U[:, r[0]:r[1]].conj().T; C = np.eye(M) - A - B
    v1 = np.trace(A @ iT(B)); v2 = np.trace(B @ iT(C)); v3 = np.trace(C @ iT(A)); v4 = -np.trace(B @ iT(A))
    ecyc = max(ecyc, abs(v1 - v2), abs(v1 - v3), abs(v1 - v4), abs(v1.imag))
say(f'(i) cyclic symmetry Tr(A iT(B)) = Tr(B iT(C)) = Tr(C iT(A)) = -Tr(B iT(A)), real: max err {ecyc:.2e}')

# (ii) Corollary 2 construction for rank-one B
etri = 0.0; worst_ineq = 1e9
for t in range(300):
    M = int(rng.integers(2, 8)); U = haar(M)
    B = np.outer(U[:, 0], U[:, 0].conj()); ra = int(rng.integers(0, M)); A = U[:, 1:1 + ra] @ U[:, 1:1 + ra].conj().T
    y = rng.normal(size=M)*10**rng.uniform(-1, 2)
    g = np.diag(y) + iT(B)
    X = B + 1j*g
    etri = max(etri, np.abs(np.tril(X, -1)).max(), np.max(np.abs(np.sort_complex(np.linalg.eigvals(X)) - np.sort_complex(np.diag(B).real + 1j*y))))
    lhs = np.trace(A @ iT(B)).real
    rhs = np.sum(h(np.diag(B).real + 1j*y) - np.diag(A).real*y)
    worst_ineq = min(worst_ineq, rhs - lhs)
say(f'(ii) g = diag(y) + iT(B): B + ig upper triangular & spec = B_kk + i y_k, err {etri:.2e};'
    f' min [sum(h - A_kk y_k) - Tr(A iT(B))] = {worst_ineq:.3e} (>= 0)')

# (iii) corank <= 3 chain in a Schur basis
def ystar(x, p):
    """stationary point of y -> h(x+iy) - p y : arg(1 - e^{pi y} e^{-i pi x}) = pi p."""
    fn = lambda yy: np.angle(1 - np.exp(PI*yy)*np.exp(-1j*PI*x))/PI - p
    return brentq(fn, -200, 200, xtol=1e-14)
e_schur = e_id = 0.0; s1 = s2 = s3 = 1e9; cnt = 0
for t in range(400):
    M = int(rng.integers(2, 8)); cor = int(rng.integers(0, min(3, M) + 1)); rk = M - cor
    U = haar(M); B = U[:, :rk] @ U[:, :rk].conj().T
    sc = 10**rng.uniform(-1, 2.5); G = rand_herm(M, rng, sc)
    if t % 3 == 0:
        w, V = np.linalg.eigh(G); w[-1] *= 20; G = (V*w) @ V.conj().T
    X = B + 1j*G
    T_, Z = schur(X, output='complex')
    Bp = Z.conj().T @ B @ Z; Gp = Z.conj().T @ G @ Z; y = np.diag(Gp).real
    e_schur = max(e_schur, np.abs(Gp - (np.diag(y) + iT(Bp))).max()/max(1, sc))
    P = np.eye(M) - Bp
    w, V = np.linalg.eigh(P @ Gp @ P); Vp = V[:, w > 1e-9*max(1, sc)]; Q = Vp @ Vp.conj().T
    rhs = np.sum(np.maximum(w, 0))
    tq = np.trace(Q @ iT(Bp)).real
    e_id = max(e_id, abs(rhs - (np.sum(np.diag(Q).real*y) + tq))/max(1, sc))
    q = np.clip(np.diag(Q).real, 0, 1); b = np.clip(np.diag(Bp).real, 0, 1); c = np.clip(np.diag(P - Q).real, 0, 1)
    ph = Phi(q, b, c)
    s1 = min(s1, np.sum(ph) - tq)                        # dual form (Cor. 2)
    s2 = min(s2, np.sum(h(b + 1j*y) - q*y - ph))           # (F5)
    s3 = min(s3, np.sum(h(np.linalg.eigvals(X))) - rhs)    # (*) itself
    cnt += 1
say(f'(iii) {cnt} cases, corank 0..3, scales 0.1-300: Schur identity G = diag(y)+iT(B) err {e_schur:.2e};'
    f' Tr(PGP)_+ = sum Q_kk y_k + Tr(Q iT(B)) err {e_id:.2e}')
say(f'      min slack: dual step {s1:.3e}, (F5) step {s2:.3e}, (*) {s3:.3e}  (all >= 0 required)')
open('rv_06_cor.log', 'w').write('\n'.join(out) + '\n')
