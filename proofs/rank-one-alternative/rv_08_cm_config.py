"""Referee: (*) at the known hard configuration Q_fresh/t03_CM_counterexample_M3.npy (rank B = 1, M = 3, gmax = 25):
50-digit defect, the same along g -> t g and g -> g_d + t g_o, and adversarial local minimisation from there.
Also checks that the configuration-space functional T of PROOF.md equals the matrix defect there."""
import numpy as np, mpmath as mp
from scipy.optimize import minimize
from rv_core import h, phip, unitary_from, herm_from, star_defect, star_defect_mp, quantiles, Tfun, PI

out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

def R2(B, g):
    wB, VB = np.linalg.eigh(B)
    Bv = VB[:, wB > 0.5]; Pv = VB[:, wB <= 0.5]
    k, Ek = np.linalg.eigh(Bv.conj().T @ g @ Bv); m, Em = np.linalg.eigh(Pv.conj().T @ g @ Pv)
    cc = Ek.conj().T @ (Bv.conj().T @ g @ Pv) @ Em
    w1 = (1 - 1e-13) + 1j*k[:, None]; w2 = 1e-13 + 1j*m[None, :]
    dd = (phip(w1 + 0*w2) - phip(w2 + 0*w1))/(w1 - w2)
    return float(np.sum(-2*np.real(dd)*np.abs(cc)**2))

d = np.load('../common/t03_CM_counterexample_M3.npy')
r = int(d[0]); gmax = d[1]; p = d[2:]; M = 3
U = unitary_from(p[:M*M], M); B = U[:, :r] @ U[:, :r].conj().T
g = herm_from(gmax*np.tanh(p[M*M:]), M)
say('CM configuration: rank B =', r, ' eig g =', np.round(np.linalg.eigvalsh(g), 4))
mp.mp.dps = 50
D50 = star_defect_mp(B, g)
say('  defect (*) at 50 digits:', mp.nstr(D50, 20), '  double:', star_defect(B, g), '  R2 =', R2(B, g))
# configuration functional T (s = 1)
nu = np.linalg.eigvals(B + 1j*g)
say('  spec(B+ig) =', np.round(nu, 6), '  T(nu) (1-D form) =', Tfun(nu.real, nu.imag, 1.0))
P = np.eye(M) - B
gd = B @ g @ B + P @ g @ P; go = g - gd
mins = []
for t in [0.1, 0.3, 0.5, 0.8, 1.0, 1.5, 2, 4, 10]:
    mins.append((t, star_defect(B, t*g), star_defect(B, gd + t*go)))
say('  along g -> t g and g_d + t g_o:', [(t, f'{a:.4e}', f'{b:.4e}') for t, a, b in mins])

# adversarial local minimisation from the CM point (ratio and absolute), with growing coupling scale
def build(q, gm):
    Uq = unitary_from(q[:M*M], M); Bq = Uq[:, :1] @ Uq[:, :1].conj().T
    return Bq, herm_from(gm*np.tanh(q[M*M:]), M)
def obj(q, gm):
    Bq, gq = build(q, gm)
    Pq = np.eye(M) - Bq
    goq = gq - Bq @ gq @ Bq - Pq @ gq @ Pq
    den = min(R2(Bq, gq), np.sum(np.abs(np.linalg.eigvalsh(goq))))
    if den < 1e-10: return 1e3
    return star_defect(Bq, gq)/den
rng = np.random.default_rng(808)
best = 1e9
for gm in [25, 100, 300]:
    for rep in range(8):
        q0 = p + rng.normal(size=p.size)*(0.0 if rep == 0 else 0.3)
        res = minimize(obj, q0, args=(gm,), method='Nelder-Mead', options=dict(maxiter=20000, maxfev=20000, xatol=1e-12, fatol=1e-15))
        Bq, gq = build(res.x, gm)
        Dq = star_defect(Bq, gq)
        best = min(best, res.fun)
        if Dq < -1e-10:
            say('  CANDIDATE', gm, rep, Dq, ' 50-digit:', mp.nstr(star_defect_mp(Bq, gq), 15))
    say(f'  gmax={gm}: min D/min(R2,|g_o|_1) near CM point = {best:.4e}')
open('rv_08_cm_config.log', 'w').write('\n'.join(out) + '\n')
