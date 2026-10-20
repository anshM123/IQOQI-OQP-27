"""ia_selftest.py -- randomized self-test of ia.py against mpmath (300-bit): every enclosure must contain the value
computed exactly (rational) or in high precision.  Sanity check of the implementation, not part of the proof."""
import numpy as np, mpmath
from fractions import Fraction as Fr
from ia import IA, PI, sin_ia
mpmath.mp.prec = 300
rng = np.random.default_rng(1)
bad = 0
for trial in range(200):
    x = rng.standard_normal(50) * 10.0 ** rng.integers(-8, 8); y = rng.standard_normal(50) * 10.0 ** rng.integers(-8, 8)
    y[np.abs(y) < 1e-300] = 1.0
    X, Y = IA.exact(x), IA.exact(y)
    for op, f in (('+', lambda a, b: a + b), ('-', lambda a, b: a - b), ('*', lambda a, b: a * b), ('/', lambda a, b: a / b)):
        Z = f(X, Y)
        for i in range(50):
            ex = f(Fr(float(x[i])), Fr(float(y[i])))
            if not (Fr(float(Z.lo[i])) <= ex <= Fr(float(Z.hi[i]))): bad += 1
    C = X.cumsum()
    acc = Fr(0)
    for i in range(50):
        acc += Fr(float(x[i]))
        if not (Fr(float(C.lo[i])) <= acc <= Fr(float(C.hi[i]))): bad += 1
th = IA.exact(rng.uniform(0, 1.5707, 2000))
s = sin_ia(th)
for i in range(2000):
    ex = mpmath.sin(mpmath.mpf(float(th.lo[i])))
    if not (mpmath.mpf(float(s.lo[i])) <= ex <= mpmath.mpf(float(s.hi[i]))): bad += 1
pth = PI * IA.exact(np.arange(1, 400, 2.0)) / IA.exact(1600.0)
sp = sin_ia(pth)
for i, j in enumerate(range(1, 400, 2)):
    ex = mpmath.sin(mpmath.pi * j / 1600)
    if not (mpmath.mpf(float(sp.lo[i])) <= ex <= mpmath.mpf(float(sp.hi[i]))): bad += 1
print("ia.py self-test: enclosure failures =", bad, "(", 200 * 50 * 5 + 2000 + 200, "checks )")
