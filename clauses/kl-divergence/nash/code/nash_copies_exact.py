"""EXACT (sympy) check that the CKM points used as DKZ copies reproduce symmetry images of DKZ_3's Bob basis:
for key = (d, f1, f2) (units of pi/12), with t12 = t23 = pi/4, t13 = asin(3^{-1/2}),
Bt(x_c) and conj^c(Z^j Bt*_0 P_sigma) have columns equal up to unimodular factors (|<col, col'>| = 1 exactly).
usage: python nash_copies_exact.py"""
import itertools
import sympy as sp

w = sp.exp(2 * sp.pi * sp.I / 3)
s3 = sp.sqrt(3)


def ckm_exact(key):
    c12 = s12 = c23 = s23 = 1 / sp.sqrt(2)
    s13 = 1 / s3
    c13 = sp.sqrt(2) / s3
    d, f1, f2 = [sp.pi * k / 12 for k in key]
    e = sp.exp(sp.I * d)
    V = sp.Matrix([[c12 * c13, s12 * c13, s13 * sp.exp(-sp.I * d)],
                   [-s12 * c23 - c12 * s23 * s13 * e, c12 * c23 - s12 * s23 * s13 * e, s23 * c13],
                   [s12 * s23 - c12 * c23 * s13 * e, -c12 * s23 - s12 * c23 * s13 * e, c23 * c13]])
    L = sp.diag(1, sp.exp(sp.I * f1), sp.exp(sp.I * f2))
    return L * V


def bob0():
    return sp.Matrix(3, 3, lambda k, b: w ** (k * (b + sp.Rational(1, 4)))) / s3


def images():
    Z = sp.diag(1, w, w ** 2)
    B = bob0()
    for j in range(3):
        for sig in itertools.permutations(range(3)):
            for cj in range(2):
                M = (Z ** j) * B[:, list(sig)]
                if cj:
                    M = M.conjugate()
                yield (j, sig, cj), M


def match(Bt, M):
    """numerical pre-screen at 50 digits, then an exact proof that |<col, col'>|^2 - 1 = 0 for every column
    (its minimal polynomial over Q is x)."""
    ips = [sp.expand((Bt[:, b].H * M[:, b])[0]) for b in range(3)]
    if any(abs(sp.N(sp.Abs(ip), 50) - 1) > sp.Float(10) ** -40 for ip in ips):
        return False
    x = sp.Symbol("x")
    for ip in ips:
        val = sp.expand(ip * sp.conjugate(ip) - 1)
        val = sp.nsimplify(sp.expand_complex(val)) if False else sp.expand_complex(val)
        mp_ = sp.minimal_polynomial(val, x)
        if mp_ != x:
            return False
    return True


if __name__ == "__main__":
    keys = [(6, 0, 6), (6, 4, 14), (6, 8, 22), (6, 8, -2)]
    for key in keys:
        Bt = ckm_exact(key)
        found = None
        for lab, M in images():
            if match(Bt, M):
                found = lab
                break
        print(key, "EXACT image of DKZ Bob basis 0 under (j, sigma, conj) =", found, flush=True)
