"""
ref_lp.py -- [sanity, floating point] full (2,2,d) critical visibilities by my own LP formulation (HiGHS):
maximise v s.t. v p + (1 - v) u = sum_lambda w_lambda delta_lambda, w >= 0  (equalities on all 4 d^2 entries).
Competitor C_d (Lemma 1 behaviour) for d = 4..9 and DKZ_d (closed form) for d = 3..8, compared with v_even/v_odd and
2/I_ME(d).  Informational only (no decision of the referee report rests on these floats).
"""
import itertools
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix


def vc(p):
    d = p.shape[2]
    S = list(itertools.product(range(d), repeat=4))
    rows, cols = [], []
    for i, s in enumerate(S):
        for x in range(2):
            for y in range(2):
                rows.append(((x * 2 + y) * d + s[x]) * d + s[2 + y])
                cols.append(i)
    E = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(4 * d * d, len(S)))
    pf = p.reshape(-1)
    uf = np.full_like(pf, 1.0 / d ** 2)
    from scipy.sparse import hstack
    Aeq = hstack([E, csr_matrix((-(pf - uf))[:, None])]).tocsr()
    c = np.zeros(len(S) + 1)
    c[-1] = -1
    r = linprog(c, A_eq=Aeq, b_eq=uf, bounds=[(0, None)] * len(S) + [(0, 1)], method="highs")
    return r.x[-1]


def competitor(d):
    s = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    p = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    p[x, y, a, b] = (1 + (1 if a == b else -1) * s[(x, y)] / np.sqrt(2)) / 4
            if d % 2:
                p[x, y] *= (d - 1) / d
                p[x, y, 0, 0] += 1 / d
    return p


def dkz(d):
    delta = {(0, 0): 0.25, (0, 1): -0.25, (1, 0): 0.75, (1, 1): 0.25}
    p = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    p[x, y, a, b] = 1 / (2 * d ** 3 * np.sin(np.pi * (b - a - delta[(x, y)]) / d) ** 2)
    return p


if __name__ == "__main__":
    r2 = np.sqrt(2)
    for d in range(4, 10):
        t0 = time.time()
        v = vc(competitor(d))
        want = 4 * (d - 1) / ((r2 - 1) * d * d + 4 * (d - 1)) if d % 2 == 0 else 4 / ((r2 - 1) * d + 4)
        print(f"competitor d={d}: LP v_c = {v:.10f}, closed form {want:.10f}, diff {v - want:+.1e}  ({time.time() - t0:.1f}s)",
              flush=True)
    for d in range(3, 9):
        t0 = time.time()
        v = vc(dkz(d))
        j = np.arange(1, d)
        ime = 4 / (d * (d - 1)) * np.sum((d - j) / np.cos(np.pi * j / (2 * d)))
        print(f"DKZ d={d}: LP v_c = {v:.10f}, 2/I_ME = {2 / ime:.10f}, diff {v - 2 / ime:+.1e}  ({time.time() - t0:.1f}s)",
              flush=True)
