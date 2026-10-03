# Matrix rigidity (MR): Re X = B (proj), Re psi(X) = Q (proj, Q <= 1-B)  ==>  X normal ?
# Solve Re psi(B + i g) = Q for g by least squares from random starts; report non-normal solutions.
import numpy as np
from scipy.linalg import expm, logm
from scipy.optimize import least_squares
rng = np.random.default_rng(8)
def psi(X):
    M = X.shape[0]
    return -(1j/np.pi)*logm(np.eye(M) - expm(-1j*np.pi*X))
def herm(p, M):
    g = np.zeros((M,M), complex); iu = np.triu_indices(M,1); k = len(iu[0])
    g[np.diag_indices(M)] = p[:M]; g[iu] = p[M:M+k] + 1j*p[M+k:]
    return g + np.triu(g,1).conj().T
def hvec(H):
    M = H.shape[0]; iu = np.triu_indices(M,1)
    return np.concatenate([H[np.diag_indices(M)].real, H[iu].real, H[iu].imag])
def run(M, r, q, trials=40):
    found = []
    for t in range(trials):
        U = np.linalg.qr(rng.normal(size=(M,M))+1j*rng.normal(size=(M,M)))[0]
        B = U[:, :r]@U[:, :r].conj().T
        Q = U[:, r:r+q]@U[:, r:r+q].conj().T      # Q <= P
        sc = 10**rng.uniform(-0.5, 1)
        p0 = rng.normal(size=M*M)*sc
        def res(p):
            X = B + 1j*herm(p, M)
            Rp = psi(X); Rh = (Rp + Rp.conj().T)/2
            return hvec(Rh - Q)
        try:
            sol = least_squares(res, p0, xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=4000)
        except Exception as e:
            continue
        g = herm(sol.x, M); X = B + 1j*g
        resid = np.linalg.norm(sol.fun)
        comm = np.linalg.norm(B@g - g@B)
        nrm = np.linalg.norm(X@X.conj().T - X.conj().T@X)
        if resid < 1e-9:
            found.append((comm, nrm, np.linalg.norm(g)))
    return found
for (M, r, q) in [(3,1,1), (4,1,2), (4,2,1), (5,2,2), (5,2,1), (6,2,2), (6,3,2)]:
    f = run(M, r, q)
    if f:
        cm = max(c for c,_,_ in f)
        print(f'M={M} r={r} q={q}: {len(f)} solutions, max |[B,g]| = {cm:.2e}, max |[X,X*]| = {max(n for _,n,_ in f):.2e}')
    else:
        print(f'M={M} r={r} q={q}: no converged solutions')
