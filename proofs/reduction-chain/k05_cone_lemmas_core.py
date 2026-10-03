import numpy as np
from scipy import special
PI = np.pi
CN = np.array([abs(special.bernoulli(2 * n)[-1]) / (2 * n * special.factorial(2 * n + 1)) for n in range(1, 31)])
def cl2(t):
    t = np.asarray(t, float)
    out = np.where(t > 0, t - t * np.log(np.where(t > 0, t, 1.0)), 0.0)
    pw = t ** 3; t2 = t * t
    for c in CN:
        out = out + c * pw; pw = pw * t2
    return out
def u_window_q(n, q, d):
    """u^ell for ell = n/q via exact integer window sums J_r(m) (units 1/q): Ghat(J/q) on the grid."""
    N = 4 * d; Kg = 2 * d * q
    j = np.arange(d * q + 1)
    gh = -(N ** 2 / (2 * PI ** 2)) * (cl2(PI * j / Kg) + cl2(PI * (Kg - j) / Kg))
    e2 = np.concatenate([n, n]); cs = np.concatenate([[0], np.cumsum(e2)])
    r = np.arange(d)[:, None]; m = np.arange(d + 1)[None, :]
    J = cs[r + m] - cs[r]
    P = gh[J].mean(axis=0)
    return P[2:] - 2 * P[1:-1] + P[:-2]
