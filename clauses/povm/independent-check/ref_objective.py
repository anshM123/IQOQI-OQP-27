"""
ref_objective.py -- referee's exact checks of the objective link (independent of P1 code).
(1) literal CGLMP I_d (BRIEF / math paper eq. (cglmp), A_1 = x0, A_2 = x1, B_1 = y0, B_2 = y1) on every deterministic
    strategy vs 4 - 2 S/(d-1), S = <X1-Y1> + <Y1-X2> + <X2-Y2> + <Y2-X1-1> (X1 = a(x0), X2 = a(x1), Y1 = b(y0),
    Y2 = b(y1)), for the four relabellings (identity, swap x, swap y, swap both) -> which one matches.
(2) S_op (Fourier form, built as in ref_verify.py) is invariant under every element of the referee's group G
    modulo cyclic rotation only (exact, in the lazy ring with reduction mod Phi_N), so S(f.E) = S(E) for all f in G.
(3) chain form of BRIEF:  S = d Pi - 1 with Pi = P(X1<Y1)+P(Y1<X2)+P(X2<Y2)+P(Y2<=X1)  (deterministic points).
usage: python ref_objective.py dmax
"""
import sys
import itertools
from fractions import Fraction
from ref_verify import Lazy, make_group, apply, canon_rot


def literal_I(d, A1, A2, B1, B2):
    I = Fraction(0)
    for k in range(d // 2):
        wk = 1 - Fraction(2 * k, d - 1)
        pos = [(A1 - B1 - k) % d == 0, (B1 - A2 - k - 1) % d == 0, (A2 - B2 - k) % d == 0, (B2 - A1 - k) % d == 0]
        neg = [(A1 - B1 + k + 1) % d == 0, (B1 - A2 + k) % d == 0, (A2 - B2 + k + 1) % d == 0, (B2 - A1 + k + 1) % d == 0]
        I += wk * (sum(pos) - sum(neg))
    return I


def S_det(d, X1, X2, Y1, Y2):
    return (X1 - Y1) % d + (Y1 - X2) % d + (X2 - Y2) % d + (Y2 - X1 - 1) % d


def main(dmax):
    for d in range(3, dmax + 1):
        match = {}
        for name, perm in [("identity", lambda a0, a1, b0, b1: (a0, a1, b0, b1)),
                           ("swap x", lambda a0, a1, b0, b1: (a1, a0, b0, b1)),
                           ("swap y", lambda a0, a1, b0, b1: (a0, a1, b1, b0)),
                           ("swap both", lambda a0, a1, b0, b1: (a1, a0, b1, b0))]:
            ok = True
            for (a0, a1, b0, b1) in itertools.product(range(d), repeat=4):
                # literal I of the RELABELLED strategy p' (p'(.|x,y) = p(.|pi(x), pi(y))): A1 <- first slot etc.
                A1, A2, B1, B2 = perm(a0, a1, b0, b1)
                lhs = literal_I(d, A1, A2, B1, B2)
                rhs = 4 - Fraction(2 * S_det(d, a0, a1, b0, b1), d - 1)
                if lhs != rhs:
                    ok = False
                    break
            match[name] = ok
        # chain form
        chain_ok = all(S_det(d, X1, X2, Y1, Y2) == d * ((X1 < Y1) + (Y1 < X2) + (X2 < Y2) + (Y2 <= X1)) - 1
                       for (X1, X2, Y1, Y2) in itertools.product(range(d), repeat=4))
        # local bound / max of 4 - 2S/(d-1) over deterministic strategies
        Smin = min(S_det(d, *t) for t in itertools.product(range(d), repeat=4))
        # (2) S_op invariance under G modulo rotation only
        N = 4 * d
        R = Lazy(N)
        S0 = {}
        links = [(0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, 1)]
        for (g1, g2, delta) in links:
            h = [(kk - delta) % d for kk in range(d)]
            for nn in range(1, d):
                vec = [0] * N
                for kk in range(d):
                    vec[(4 * (-nn * kk)) % N] += h[kk]
                key = canon_rot(((g1, nn), (g2, (-nn) % d)))
                S0[key] = R.add(S0.get(key, [0] * N), vec)
        G = make_group(d)
        inv_ok = True
        for f in G:
            img = {}
            for key, vec in S0.items():
                v, ph = apply(f, key, d)
                v = canon_rot(v)
                sh = [0] * N
                for kk, x in enumerate(vec):
                    sh[(kk + 4 * ph) % N] += x          # L_{f.E}(key) = w^ph L_E(f(key))
                img[v] = R.add(img.get(v, [0] * N), sh)
            for key in set(img) | set(S0):
                diff = [x - y for x, y in zip(img.get(key, [0] * N), S0.get(key, [0] * N))]
                if any(R.reduce(diff)):
                    inv_ok = False
        print(f"d={d}: I_d(relabelled p) = 4 - 2S(p)/(d-1) on all {d ** 4} deterministic points for: "
              f"{[k for k, v in match.items() if v]};  chain form S = d Pi - 1: {chain_ok};  "
              f"min_det S = {Smin} -> local max of 4-2S/(d-1) = {4 - Fraction(2 * Smin, d - 1)};  "
              f"S_op invariant under all |G| = {len(G)} elements (mod rotation): {inv_ok}", flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]))
