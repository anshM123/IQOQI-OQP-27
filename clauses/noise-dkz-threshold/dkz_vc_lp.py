"""numerical sanity check of Theorem M's consequence: v_c(DKZ_d) by LP over the full local polytope L(2,2,d)."""
import sys, itertools, math
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
def dkz_behaviour(d):
    w = np.exp(2j * np.pi / d); k = np.arange(d)
    al = (0.5, 0.0); be = (0.25, -0.25)
    A = [np.array([w ** (k * (a + al[x])) for a in range(d)]).T / np.sqrt(d) for x in range(2)]
    Bt = [np.array([w ** (k * (b + be[y])) for b in range(d)]).T / np.sqrt(d) for y in range(2)]
    q = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            q[x, y] = np.abs(A[x].conj().T @ Bt[y]) ** 2 / d
    return q
def vc(d):
    q = dkz_behaviour(d).reshape(-1)
    u = np.full(4 * d * d, 1.0 / d ** 2)
    lams = list(itertools.product(range(d), repeat=4))
    nl = len(lams)
    A = lil_matrix((4 * d * d + 1, nl + 1))
    for j, (a0, a1, b0, b1) in enumerate(lams):
        for x, a in ((0, a0), (1, a1)):
            for y, b in ((0, b0), (1, b1)):
                A[((x * 2 + y) * d + a) * d + b, j] = 1.0
        A[4 * d * d, j] = 1.0
    A[:4 * d * d, nl] = -(q - u)
    beq = np.concatenate([u, [1.0]])
    c = np.zeros(nl + 1); c[-1] = -1.0
    res = linprog(c, A_eq=csr_matrix(A), b_eq=beq, bounds=[(0, None)] * nl + [(None, None)], method="highs")
    return res.x[-1]
for d in [int(a) for a in sys.argv[1:]]:
    I = 4 / (d * (d - 1)) * sum((d - j) / math.cos(math.pi * j / (2 * d)) for j in range(1, d))
    v = vc(d)
    print(f"d={d}: LP v_c(DKZ_d) = {v:.10f}   2/I_ME(d) = {2/I:.10f}   difference {v - 2/I:+.1e}", flush=True)
