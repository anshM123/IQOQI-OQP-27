"""DKZ_k (+) L_m (local block of size m): check R = 1/v_c = 1 + (kappa_k - 1) d/(2d - k), d = k + m, and inspect the
LP structure (optimal Bell functional, support of the optimal local model).  Numerics only."""
import sys, os, itertools
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import vc, behaviour, dkz_bases, ime, det_T   # noqa: E402


def bd(X, Y):
    n, m = X.shape[0], Y.shape[0]
    Z = np.zeros((n + m, n + m), complex); Z[:n, :n] = X; Z[n:, n:] = Y
    return Z


def strat(k, m, local='identity', rng=None):
    Ak, Fk = dkz_bases(k)
    if local == 'identity':
        AL = np.array([np.eye(m), np.eye(m)]); FL = np.array([np.eye(m), np.eye(m)])
    else:   # a random 'local' block: Alice's two bases equal, Bob's two bases equal (commuting -> local)
        from scipy.stats import unitary_group
        U = unitary_group.rvs(m, random_state=rng) if m > 1 else np.eye(1)
        V = unitary_group.rvs(m, random_state=rng) if m > 1 else np.eye(1)
        AL = np.array([U, U]); FL = np.array([V, V])
    A = np.array([bd(Ak[x], AL[x]) for x in range(2)]); F = np.array([bd(Fk[y], FL[y]) for y in range(2)])
    return A, F


rng = np.random.default_rng(0)
print(" k  m  d   v_c          R=1/v_c     formula     diff      (random local block: R)")
for k in (2, 3, 4, 5):
    for m in (1, 2, 3):
        d = k + m
        A, F = strat(k, m)
        v = vc(behaviour(A, F))
        kap = ime(k) / 2
        Rf = 1 + (kap - 1) * d / (2 * d - k)
        A2, F2 = strat(k, m, 'random', rng)
        v2 = vc(behaviour(A2, F2))
        print(f"{k:2d} {m:2d} {d:2d}  {v:.9f}  {1/v:.9f}  {Rf:.9f}  {1/v-Rf:+.1e}   {1/v2:.9f}", flush=True)
