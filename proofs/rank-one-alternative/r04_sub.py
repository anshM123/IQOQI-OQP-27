# Subcritical functional  T = sum h(spec(s vv* + i g)) - Tr[(PgP)_+] - (1-s) <v,gv>_+   (P = 1 - vv*)   >= 0 ?
import sys; sys.path.insert(0, '../common')
import numpy as np
from fcore import hstrip
from scipy.optimize import minimize
rng = np.random.default_rng(11)
def T(s, g, v):
    M = len(v); B1 = np.outer(v, v.conj()); P = np.eye(M) - B1
    lhs = np.sum(hstrip(np.linalg.eigvals(s*B1 + 1j*g)))
    rhs = np.sum(np.maximum(np.linalg.eigvalsh(P@g@P), 0)) + (1-s)*max(np.real(v.conj()@g@v), 0)
    return lhs - rhs, rhs
def unpack(p, M):
    g = np.zeros((M,M), complex); iu = np.triu_indices(M, 1)
    g[np.diag_indices(M)] = p[:M]
    k = len(iu[0]); g[iu] = p[M:M+k] + 1j*p[M+k:M+2*k]; g = g + np.triu(g,1).conj().T
    v = p[M+2*k:M+2*k+M] + 1j*p[M+2*k+M:]; v = v/np.linalg.norm(v)
    return g, v
worst = 1e9
for trial in range(400):
    M = int(rng.integers(2, 6)); s = float(rng.uniform(0.05, 1.0))
    npar = M + M*(M-1) + 2*M
    sc = 10**rng.uniform(-0.5, 1.5)
    p0 = rng.normal(size=npar)*sc
    fun = lambda p: (lambda r: r[0]/max(1.0, abs(r[1])))(T(s, *unpack(p, M)))
    try:
        res = minimize(fun, p0, method='Nelder-Mead', options={'maxiter': 4000, 'xatol':1e-10,'fatol':1e-12})
        val = res.fun
    except Exception as e:
        continue
    if val < worst:
        worst = val; wc = (M, s, val)
print('worst relative T:', worst, wc)
