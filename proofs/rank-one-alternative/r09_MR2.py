# (MR) test in Schur form: X upper triangular, spectrum in S.  R0 = Re X, R1 = Re psi(X).
# minimise E = |R0^2-R0|^2 + |R1^2-R1|^2 + |R0 R1|^2  subject to non-normality |[X,X*]|_F = 1 (via normalisation penalty)
import numpy as np
from scipy.optimize import minimize
rng = np.random.default_rng(12)
PI = np.pi
def psi_s(z): return -(1j/PI)*np.log(1 - np.exp(-1j*PI*z))
def psi_tri(X):
    # Parlett recurrence for upper triangular X with distinct diagonal
    M = X.shape[0]; F = np.zeros_like(X); d = np.diag(X)
    for k in range(M): F[k,k] = psi_s(d[k])
    for p in range(1, M):
        for i in range(M-p):
            j = i+p
            s = X[i,j]*(F[j,j]-F[i,i])
            for k in range(i+1, j):
                s += X[i,k]*F[k,j] - F[i,k]*X[k,j]
            F[i,j] = s/(d[j]-d[i])
    return F
def build(p, M):
    x = 1/(1+np.exp(-p[:M])); y = p[M:2*M]
    iu = np.triu_indices(M,1); k = len(iu[0])
    X = np.diag(x+1j*y).astype(complex)
    X[iu] = p[2*M:2*M+k] + 1j*p[2*M+k:2*M+2*k]
    return X
def E(p, M):
    X = build(p, M)
    R0 = (X + X.conj().T)/2
    F1 = psi_tri(X); R1 = (F1 + F1.conj().T)/2
    nn = np.linalg.norm(X@X.conj().T - X.conj().T@X)
    e = np.linalg.norm(R0@R0-R0)**2 + np.linalg.norm(R1@R1-R1)**2 + np.linalg.norm(R0@R1)**2
    return e + (nn-1.0)**2, e, nn
for M in [3,4,5]:
    best = 1e9
    for t in range(60):
        k = M*(M-1)//2
        p0 = np.concatenate([rng.normal(size=M), rng.normal(size=M)*2, rng.normal(size=2*k)*0.5])
        try:
            r = minimize(lambda p: E(p, M)[0], p0, method='BFGS', options={'maxiter': 3000, 'gtol':1e-12})
        except Exception:
            continue
        tot, e, nn = E(r.x, M)
        if tot < best:
            best = tot; bb = (e, nn)
    print(f'M={M}: min [E + (|[X,X*]|-1)^2] = {best:.3e}   (E={bb[0]:.3e}, nonnormality={bb[1]:.3f})')
