# Rank-one (*) reformulation check:
#  eigenvalues nu_k = x_k + i y_k of B + i g (B rank one)
#  sigma = sum_k Cauchy(loc y_k, scale x_k)  -> integer quantiles gamma_j should = eig(PgP)
import numpy as np
from scipy.optimize import brentq
rng = np.random.default_rng(1)
def test(M, scale):
    g = rng.normal(size=(M,M)) + 1j*rng.normal(size=(M,M)); g = (g+g.conj().T)/2*scale
    v = rng.normal(size=M)+1j*rng.normal(size=M); v/=np.linalg.norm(v)
    B = np.outer(v,v.conj()); P = np.eye(M)-B
    nu = np.linalg.eigvals(B+1j*g)
    x, y = nu.real, nu.imag
    # eig of PgP on ran P
    w, V = np.linalg.eigh(P)
    Q = V[:, w>0.5]
    gam = np.sort(np.linalg.eigvalsh(Q.conj().T@g@Q))
    Fs = lambda t: np.sum(0.5+np.arctan((t-y)/x)/np.pi)
    lo, hi = -1e3*scale-1e3, 1e3*scale+1e3
    q = [brentq(lambda t: Fs(t)-j, lo, hi, xtol=1e-14) for j in range(1,M)]
    return np.max(np.abs(np.array(q)-gam)), x.sum()
for M in [2,3,5,8]:
    for s in [0.3, 3, 30]:
        print(M, s, test(M,s))
