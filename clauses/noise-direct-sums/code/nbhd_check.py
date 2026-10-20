"""Numerical sanity checks for Lemma U (additive local model) and Corollary P (neighbourhoods of strategies with
v_c > v*).  Not part of any proof; the proofs are in THEOREM.md."""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import vc, behaviour, dkz_bases, haar, vstar, is_local   # noqa: E402
rng = np.random.default_rng(1)


def additive_model_ok(Z):
    """the kernel K_y(b|a0,a1) = d Z(a0,b|0,y) + d Z(a1,b|1,y) - 1/d is >= 0 iff the additive model applies."""
    d = Z.shape[-1]
    worst = np.inf
    for y in range(2):
        K = d * Z[0, y][:, None, :] + d * Z[1, y][None, :, :] - 1.0 / d     # [a0, a1, b]
        worst = min(worst, K.min())
    return worst


# Lemma U: random uniform-marginal Z with entries >= 1/(2 d^2) are local (LP) and the additive kernel is >= 0
for d in (3, 4, 5, 6):
    bad = 0
    for t in range(30):
        # random doubly-stochastic link laws with entries in [1/(2d^2), ...]: mix uniform with random Birkhoff points
        Z = np.empty((2, 2, d, d))
        for x in range(2):
            for y in range(2):
                M = sum(rng.dirichlet(np.ones(1))[0] * np.eye(d)[rng.permutation(d)] for _ in range(1))
                Z[x, y] = 0.5 / d ** 2 + 0.5 * M / d
        ok, _ = is_local(Z)
        bad += (not ok) or (additive_model_ok(Z) < -1e-12)
    print(f"d={d}: 30 random uniform-marginal behaviours with entries >= 1/(2d^2): failures {bad}")
# Corollary P: neighbourhood of a direct sum
d = 5
A3, F3 = dkz_bases(3)
A2, F2 = dkz_bases(2)
def bd(X, Y):
    Z = np.zeros((X.shape[0] + Y.shape[0],) * 2, complex); Z[:X.shape[0], :X.shape[0]] = X; Z[X.shape[0]:, X.shape[0]:] = Y; return Z
A = np.array([bd(A3[x], A2[x]) for x in range(2)]); F = np.array([bd(F3[y], F2[y]) for y in range(2)])
P = behaviour(A, F); v0 = vc(P); vs = vstar(d)
eps = (v0 - vs) / (2 * d * d * vs * v0)
print(f"DKZ_3 (+) DKZ_2: v_c = {v0:.7f}, v* = {vs:.7f}, guaranteed radius in max|dP| = {eps:.3e}")
for t in range(10):
    H = [rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)) for _ in range(4)]
    H = [(h + h.conj().T) / 2 for h in H]
    from scipy.linalg import expm
    s = 0.01
    A2_ = np.array([expm(1j * s * H[x]) @ A[x] for x in range(2)]); F2_ = np.array([expm(1j * s * H[2 + y]) @ F[y] for y in range(2)])
    P2 = behaviour(A2_, F2_); dP = np.abs(P2 - P).max()
    print(f"  perturbation s={s}: max|dP| = {dP:.2e} ({'inside' if dP <= eps else 'outside'} radius), v_c = {vc(P2):.6f} (>= v* {vc(P2) >= vs})")
