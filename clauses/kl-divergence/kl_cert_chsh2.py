"""kl_cert_chsh2.py -- exact-certificate lower bound for the KL strength (uniform settings) of the
two-copy CHSH correlation with SHARED settings on |Phi_2> (x) |Phi_2> = |Phi_4> (4 outcomes, 2 settings):
  q((a1,a2),(b1,b2)|x,y) = c(a1,b1|x,y) c(a2,b2|x,y),   c(a,b|x,y) = (1 + (-1)^{a+b+xy}/sqrt2)/4.
Test factor r rational, checked EXACTLY against all 256 deterministic strategies; bound evaluated with
interval arithmetic (q in Q(sqrt2))."""
import itertools
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf
from bell22d import kl_strength

iv.dps = 50
d = 4
s2 = iv.sqrt(iv.mpf(2))


def c_iv(a, b, x, y):
    sgn = (-1) ** ((a + b + x * y) % 2)
    return (1 + sgn / s2) / 4


def c_f(a, b, x, y):
    return (1 + (-1) ** ((a + b + x * y) % 2) / np.sqrt(2)) / 4


q = np.zeros((2, 2, 4, 4))
Q = {}
for x, y in itertools.product(range(2), repeat=2):
    for A, B in itertools.product(range(4), repeat=2):
        a1, a2, b1, b2 = A >> 1, A & 1, B >> 1, B & 1
        q[x, y, A, B] = c_f(a1, b1, x, y) * c_f(a2, b2, x, y)
        Q[(x, y, A, B)] = c_iv(a1, b1, x, y) * c_iv(a2, b2, x, y)
r = kl_strength(q)
R = {k: Fr(float(q[k] / r['p'][k])).limit_denominator(10 ** 12) for k in Q}
Mx = max(sum(R[(x, y, lam[x], lam[2 + y])] for x in range(2) for y in range(2)) / 4
         for lam in itertools.product(range(4), repeat=4))
L = iv.mpf(0)
for k, rr in R.items():
    rn = rr / Mx * (1 - Fr(1, 10 ** 9))
    L += Q[k] * iv.log(iv.mpf(rn.numerator) / rn.denominator) / 4
L = L / iv.log(iv.mpf(2))
print(f"CHSH (x) CHSH, shared settings, |Phi_4>: certified KL >= {float(mpf(L.a)):.12f} bits "
      f"(numerical {r['kl']/np.log(2):.12f}; exact normaliser {float(Mx):.15f})")
