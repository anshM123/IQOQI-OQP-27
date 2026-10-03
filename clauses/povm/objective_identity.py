"""
objective_identity.py -- exact checks linking the certified quantity S to the literal CGLMP expression.

(a) Sawtooth Fourier identity in Q(zeta_{4d}) (exact):  for k = 0..d-1,
        (d-1)/2 + sum_{n=1}^{d-1} c_n w^{n k} = k,     c_n = -1/(1 - w^{-n}),  w = exp(2 pi i/d).
    Hence for every behaviour, tau(S_op) = S(p) := E<X1-Y1>_d + E<Y1-X2>_d + E<X2-Y2>_d + E<Y2-X1-1>_d,
    <t>_d in {0..d-1} the residue (S_op as in verify_povm.py / publish/CGLMP/verify/verify_tracial.py).
(b) For every deterministic local strategy (a0, a1, b0, b1) in Z_d^4 (exact rationals):
        I_d(p') = 4 - 2 S(p)/(d-1),
    where I_d is the literal CGLMP expression of OQP 27 (the mathematical paper, with A_1 = x0, A_2 = x1, B_1 = y0, B_2 = y1)
    and p' is p with BOTH setting labels exchanged (x <-> 1-x, y <-> 1-y); X1 = a0, X2 = a1, Y1 = b0, Y2 = b1.
    Both sides are affine in p and the deterministic points affinely span the no-signalling behaviours, so the
    identity holds for every no-signalling (in particular every quantum) behaviour.
Consequently  sup over strategies of I_d = sup of 4 - 2 S/(d-1)  (relabelling settings maps strategies to
strategies), and S >= S_DKZ  <=>  I_d <= I_ME(d).
usage: python objective_identity.py dmax
"""
import sys
import itertools
from fractions import Fraction
from verify_povm import CF


def literal_I(d, X1, X2, Y1, Y2):
    """literal CGLMP for the deterministic behaviour A1 = X1, A2 = X2, B1 = Y1, B2 = Y2 (exact)."""
    A1, A2, B1, B2 = X1, X2, Y1, Y2
    I = Fraction(0)
    for k in range(d // 2):
        w = 1 - Fraction(2 * k, d - 1)
        t = 0
        t += (A1 % d == (B1 + k) % d) + (B1 % d == (A2 + k + 1) % d) + (A2 % d == (B2 + k) % d) \
            + (B2 % d == (A1 + k) % d)
        t -= (A1 % d == (B1 - k - 1) % d) + (B1 % d == (A2 - k) % d) + (A2 % d == (B2 - k - 1) % d) \
            + (B2 % d == (A1 - k - 1) % d)
        I += w * t
    return I


def main(dmax):
    for d in range(3, dmax + 1):
        # (a) exact sawtooth identity
        F = CF(4 * d)
        w_ = lambda k: F.zpow(4 * k)
        for k in range(d):
            acc = F.const(Fraction(d - 1, 2))
            for n in range(1, d):
                cn = F.sub(F.zero(), F.inv(F.sub(F.const(1), w_(-n))))
                acc = F.add(acc, F.mul(cn, w_(n * k)))
            assert F.iszero(F.sub(acc, F.const(k))), (d, k)
        # (b) deterministic strategies
        for (a0, a1, b0, b1) in itertools.product(range(d), repeat=4):
            S = (a0 - b0) % d + (b0 - a1) % d + (a1 - b1) % d + (b1 - a0 - 1) % d
            # p' = settings exchanged: literal A1 <- x=1 (a1), A2 <- x=0 (a0), B1 <- y=1 (b1), B2 <- y=0 (b0)
            Ilit = literal_I(d, a1, a0, b1, b0)
            assert Ilit == 4 - Fraction(2 * S, d - 1), (d, a0, a1, b0, b1, Ilit, S)
        print(f"d={d}: sawtooth identity exact for k = 0..{d - 1};  I_d(p') = 4 - 2 S(p)/(d-1) on all {d ** 4} "
              f"deterministic strategies (exact)", flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]))
