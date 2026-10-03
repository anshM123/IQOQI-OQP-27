"""
Floating-point LP helpers (exploration only; every DECISION in this folder is re-done in exact arithmetic).

Behaviour arrays: p[x, y, a, b], shape (2, 2, n, n).
Local polytope L(2,2,n) = conv of the n^4 deterministic behaviours
    D_{(al0, al1, be0, be1)}(a,b|x,y) = [a = al_x][b = be_y].
v_c(p, q) = max{v in [0,1] : v p + (1-v) q in L}.
"""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csc_matrix


def det_strategies(n):
    return list(itertools.product(range(n), repeat=4))  # (al0, al1, be0, be1)


def det_matrix(n):
    """Sparse matrix M (4 n^2 x n^4): column lam = vectorised deterministic behaviour."""
    strats = det_strategies(n)
    M = lil_matrix((4 * n * n, len(strats)))
    for j, (a0, a1, b0, b1) in enumerate(strats):
        al = (a0, a1)
        be = (b0, b1)
        for x in range(2):
            for y in range(2):
                M[((x * 2 + y) * n + al[x]) * n + be[y], j] = 1.0
    return csc_matrix(M), strats


def vc(p, q, M=None, return_weights=False):
    """LP critical visibility of p against noise q (both arrays (2,2,n,n))."""
    n = p.shape[2]
    if M is None:
        M, _ = det_matrix(n)
    pv = p.reshape(-1)
    qv = q.reshape(-1)
    nl = M.shape[1]
    # variables: w (nl), v ;  M w - v (p - q) = q
    from scipy.sparse import hstack
    A = hstack([M, csc_matrix((-(pv - qv)).reshape(-1, 1))]).tocsc()
    c = np.zeros(nl + 1)
    c[-1] = -1.0
    bounds = [(0, None)] * nl + [(0, 1)]
    res = linprog(c, A_eq=A, b_eq=qv, bounds=bounds, method='highs')
    if res.status != 0:
        raise RuntimeError(res.message)
    if return_weights:
        return res.x[-1], res.x[:-1], res
    return res.x[-1]


def uniform(n):
    return np.full((2, 2, n, n), 1.0 / n ** 2)
