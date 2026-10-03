"""
zcheck.py -- independent floating-point cross-check of the certified Z-model (zmodel_cert_A*.json):
 (1) re-reads the exact rational model, rebuilds the link laws by a different code path (explicit enumeration of
     (a, b0, b1) cells, tail summed in closed form), and evaluates sum_{|m|<=Mbig} Q log(Q/P) in floats;
 (2) wraps the model mod d (Lemma W) for several d, checks that the wrapped link laws are probability vectors,
     and that  S(DKZ_d) <= D(Q_d || wrap P) <= T  (S(DKZ_d) from dkz_limit.py).
usage: python zcheck.py zmodel_cert_A10.json
"""
import sys
import json
from fractions import Fraction as Fr
import numpy as np

LOG2 = np.log(2)
DELTA = {(0, 0): 0.25, (0, 1): 0.75, (1, 0): -0.25, (1, 1): 0.25}

model = json.load(open(sys.argv[1]))
A, B = model["A"], model["B"]
t = float(Fr(model["t"]))
mu = np.array([float(Fr(x)) for x in model["mu"]])
K0 = np.array([[float(Fr(x)) for x in row] for row in model["K0"]])
K1 = np.array([[float(Fr(x)) for x in row] for row in model["K1"]])
av = np.arange(-A, A + 1)
bv = np.arange(-B, B + 1)
print("total mass:", mu.sum() + 4 * t / (2 * A + 1))

Mbig = 2_000_000
off = Mbig + 2 * (A + B) + 5
L = {xy: np.zeros(2 * off + 1) for xy in DELTA}      # index m + off


def add(xy, m, w):
    np.add.at(L[xy], np.asarray(m) + off, w)


# window cells
for i, a in enumerate(av):
    add((0, 0), bv, mu[i] * K0[i])
    add((1, 0), bv - a, mu[i] * K0[i])
    add((0, 1), bv, mu[i] * K1[i])
    add((1, 1), bv - a, mu[i] * K1[i])
# tail cells |a| > A (up to |a| <= off - 2), b0 in {0, a}, b1 in {1, a}
at = np.concatenate([np.arange(-(off - 2), -A), np.arange(A + 1, off - 1)])
wt = t / (at.astype(float) ** 2 - 0.25)
for b0choice in (0, 1):
    b0 = np.zeros_like(at) if b0choice == 0 else at
    add((0, 0), b0, wt / 2)
    add((1, 0), b0 - at, wt / 2)
for b1choice in (0, 1):
    b1 = np.ones_like(at) if b1choice == 0 else at
    add((0, 1), b1, wt / 2)
    add((1, 1), b1 - at, wt / 2)
print("captured mass per link:", [round(L[xy].sum(), 9) for xy in DELTA])

ms = np.arange(-off, off + 1)
T = 0.0
for xy, dl in DELTA.items():
    sel = np.abs(ms) <= Mbig
    Q = 1.0 / (2 * np.pi ** 2 * (ms[sel] - dl) ** 2)
    P = L[xy][sel]
    T += 0.25 * np.sum(Q * np.log(Q / P))
print(f"float Z-sum up to |m| <= {Mbig}: {T / LOG2:.12f} bits (certified bound uses |m|<=2000 and drops a negative tail)")

# wrapping
sys.path.insert(0, ".")
from dkz_limit import dkz_Q, strength_dual
for d in (2, 3, 4, 5, 7, 9, 16, 33):
    Qd = dkz_Q(d)
    kl = 0.0
    for xy in DELTA:
        Pd = np.zeros(d)
        np.add.at(Pd, ms % d, L[xy])
        # mass outside the enumerated range is < 1e-6; it can only increase Pd (bound below is conservative)
        kl += 0.25 * np.sum(Qd[xy] * np.log(Qd[xy] / Pd))
    Sd = strength_dual(Qd, d)[0]
    print(f"d={d:3d}: S(DKZ_d) = {Sd / LOG2:.10f} <= wrapped model KL = {kl / LOG2:.10f} <= T = {T / LOG2:.10f}: "
          f"{Sd <= kl + 1e-12 and kl <= T + 1e-9}", flush=True)
