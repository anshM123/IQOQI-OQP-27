"""
dkz_lower.py -- certified LOWER bound for S^UNI(DKZ_D) (dual test factor, exact feasibility check), D given.
Shift-invariant test factor r_xy(m) (Lemma D + Lemma SI): feasible iff for every a in Z_D
     max_b [r00(b) + r10(b-a)] + max_b [r01(b) + r11(b-a)] <= 4      (checked in exact rational arithmetic),
then S^UNI(DKZ_D) >= (1/4) sum_xy sum_m Q_xy(m) log r_xy(m)  (interval arithmetic, Q from the closed form).
By Lemma W (monotonicity along multiples) the bound also holds for S(DKZ_{kD}), k >= 1.
usage: python dkz_lower.py D
"""
import sys
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf
sys.path.insert(0, ".")
from dkz_limit import dkz_Q, strength_dual

iv.dps = 40
D = int(sys.argv[1])
Q = dkz_Q(D)
val, r, _ = strength_dual(Q, D)
R = {k: [Fr(float(x)).limit_denominator(10 ** 12) for x in r[k]] for k in r}
worst = Fr(0)
for a in range(D):
    F = max(R[(0, 0)][b] + R[(1, 0)][(b - a) % D] for b in range(D))
    G = max(R[(0, 1)][b] + R[(1, 1)][(b - a) % D] for b in range(D))
    worst = max(worst, F + G)
scale = Fr(4) / worst * (1 - Fr(1, 10 ** 9))
R = {k: [x * scale for x in v] for k, v in R.items()}
assert all(x > 0 for v in R.values() for x in v)
DL = {(0, 0): Fr(1, 4), (0, 1): Fr(3, 4), (1, 0): Fr(-1, 4), (1, 1): Fr(1, 4)}
L = iv.mpf(0)
for k, v in R.items():
    for m in range(D):
        s = iv.sin(iv.pi * (m - iv.mpf(DL[k].numerator) / DL[k].denominator) / D)
        Qm = 1 / (2 * D ** 2 * s * s)
        L += Qm * iv.log(iv.mpf(v[m].numerator) / v[m].denominator) / 4
Lb = L / iv.log(iv.mpf(2))
print(f"D={D}: exact max of the constraint before scaling = {float(worst):.12f} (<= 4 needed); "
      f"certified S^UNI(DKZ_{D}) >= {float(mpf(Lb.a)):.12f} bits (numerical {val / np.log(2):.12f})")
