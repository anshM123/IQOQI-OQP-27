"""ref_cglmp_conv.py -- referee: the DKZ representative of THEOREM.md (alpha=(1/2,0), beta=(1/4,-1/4)) attains
I_ME(d) for the BRIEF's CGLMP chain form, up to local relabellings (setting swaps, outcome a -> +-a + c)."""
import itertools
import numpy as np
from ref_dkz import dkz_bases
from ref_solver import corr_from_bases


def cglmp_I(q, d):
    a = np.arange(d)
    lt = (a[:, None] < a[None, :]).astype(float)
    le = (a[:, None] <= a[None, :]).astype(float)
    Pi = (q[0, 0] * lt).sum() + (q[1, 0] * lt.T).sum() + (q[1, 1] * lt).sum() + (q[0, 1] * le.T).sum()
    return 4 - 2 * (d * Pi - 1) / (d - 1)


def IME(d):
    return 4 / (d * (d - 1)) * sum((d - j) / np.cos(np.pi * j / (2 * d)) for j in range(1, d))


for d in range(3, 9):
    A, B = dkz_bases(d)
    qd = corr_from_bases(A, B)
    q = np.zeros((2, 2, d, d))
    for (x, y, a, b), v in qd.items():
        q[x, y, a, b] = v
    best = -9
    for sx, sy, fa, fb in itertools.product((0, 1), (0, 1), (1, -1), (1, -1)):
        for ca0, ca1, cb0, cb1 in itertools.product(range(d), repeat=4):
            # relabelled behaviour: q'(a,b|x,y) = q(fa*a + ca_x, fb*b + cb_y | x^sx, y^sy)
            ca, cb = (ca0, ca1), (cb0, cb1)
            qq = np.zeros_like(q)
            for x in range(2):
                for y in range(2):
                    ia = (fa * np.arange(d) + ca[x]) % d
                    ib = (fb * np.arange(d) + cb[y]) % d
                    qq[x, y] = q[x ^ sx, y ^ sy][np.ix_(ia, ib)]
            best = max(best, cglmp_I(qq, d))
        if d > 5:
            break  # (offsets loop is d^4; for d > 5 the first sign/swap pattern already attains the optimum below)
    print(f"d={d}: max CGLMP value over relabellings = {best:.10f}; I_ME(d) = {IME(d):.10f}; equal: {abs(best - IME(d)) < 1e-9}")
