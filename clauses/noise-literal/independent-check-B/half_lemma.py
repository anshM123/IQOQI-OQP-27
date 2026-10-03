"""
Step 3: the 1/2-lemma.

LEMMA.  Let p be a no-signalling behaviour in (2,2,d) with marginals p_A(.|x), p_B(.|y).  Then
        (p + p_A (x) p_B)/2 is local.  In particular, if all marginals are uniform, v p + (1-v) u is local for v <= 1/2.
PROOF (explicit local models, see REPORT.md):
   M1: (A0,B0) ~ p(.,.|0,0) and (A1,B1) ~ p(.,.|1,1), the two pairs independent.
       links 00, 11 reproduce p; links 01, 10 give p_A(.|0)p_B(.|1), p_A(.|1)p_B(.|0).
   M2: (A0,B1) ~ p(.,.|0,1) and (A1,B0) ~ p(.,.|1,0), independent.  links 01, 10 reproduce p; 00, 11 give products.
   (M1 + M2)/2 = (p + p_A p_B)/2  (no-signalling makes the marginals of each link well defined).

This script (a) checks the identity EXACTLY (Fractions) on random rational no-signalling boxes with uniform
marginals, by building M1, M2 as explicit distributions on (A0, A1, B0, B1) in Z_d^4; (b) float LP sanity check:
v_c >= 1/2 for such boxes; (c) sharpness: the d-outcome PR box p(a,b|xy) = [b - a = xy mod d]/d has v_c = 1/2
exactly (CGLMP value 4 > 2 for v > 1/2 -- checked exactly with Fractions; local model at 1/2 is the lemma);
(d) exact range of d for which v_thr(d) < 1/2.
"""
import itertools
import random
from fractions import Fraction as Fr
import numpy as np
from lp_tools import vc, uniform
from competitor_exact import QS2, v_thr_exact


def random_uniform_marginal_box(d, rng, nterms=4):
    """random rational mixture of 'permutation boxes' p(a,b|xy) = [b = s_xy(a)]/d (NS, uniform marginals)"""
    ws = [Fr(rng.randint(1, 9)) for _ in range(nterms)]
    tot = sum(ws)
    ws = [w / tot for w in ws]
    p = {}
    for x, y, a, b in itertools.product(range(2), range(2), range(d), range(d)):
        p[(x, y, a, b)] = Fr(0)
    for w in ws:
        perms = {(x, y): rng.sample(range(d), d) for x in range(2) for y in range(2)}
        for x, y in perms:
            for a in range(d):
                p[(x, y, a, perms[(x, y)][a])] += w / d
    return p


def lemma_models(p, d):
    """explicit M1, M2 as distributions on (a0, a1, b0, b1)"""
    M1 = {}
    M2 = {}
    for a0, a1, b0, b1 in itertools.product(range(d), repeat=4):
        M1[(a0, a1, b0, b1)] = p[(0, 0, a0, b0)] * p[(1, 1, a1, b1)]
        M2[(a0, a1, b0, b1)] = p[(0, 1, a0, b1)] * p[(1, 0, a1, b0)]
    return M1, M2


def behaviour(M, d):
    B = {k: Fr(0) for k in itertools.product(range(2), range(2), range(d), range(d))}
    for (a0, a1, b0, b1), w in M.items():
        al, be = (a0, a1), (b0, b1)
        for x in range(2):
            for y in range(2):
                B[(x, y, al[x], be[y])] += w
    return B


def main():
    rng = random.Random(20261002)
    # (a) exact identity
    for d in range(2, 6):
        for trial in range(5):
            p = random_uniform_marginal_box(d, rng)
            M1, M2 = lemma_models(p, d)
            assert sum(M1.values()) == 1 and sum(M2.values()) == 1
            assert min(M1.values()) >= 0 and min(M2.values()) >= 0
            B1, B2 = behaviour(M1, d), behaviour(M2, d)
            for key in B1:
                assert (B1[key] + B2[key]) / 2 == (p[key] + Fr(1, d * d)) / 2, (d, key)
        print(f'(a) d={d}: (M1+M2)/2 == (p+u)/2 exactly for 5 random rational NS boxes with uniform marginals')
    # (b) float LP sanity
    for d in range(2, 6):
        worst = 1.0
        for trial in range(20):
            p = random_uniform_marginal_box(d, rng, nterms=rng.randint(1, 3))
            arr = np.zeros((2, 2, d, d))
            for (x, y, a, b), val in p.items():
                arr[x, y, a, b] = float(val)
            worst = min(worst, vc(arr, uniform(d)))
        print(f'(b) d={d}: min LP v_c over 20 random uniform-marginal NS boxes = {worst:.12f} (>= 1/2)')
        assert worst >= 0.5 - 1e-9
    # (c) sharpness: PR_d box p(a,b|xy) = [b - a = x(1-y) mod d]/d  (A0=B0, B0=A1+1, A1=B1, B1=A0)
    for d in range(2, 10):
        PR = {(x, y, a, b): (Fr(1, d) if (b - a - x * (1 - y)) % d == 0 else Fr(0))
              for x, y, a, b in itertools.product(range(2), range(2), range(d), range(d))}
        # CGLMP (chain form of BRIEF): I = sum_k c_k [P(A0-B0=k) + P(A1-B0=-(k+1)) + P(A1-B1=k) + P(A0-B1=-k)
        #                                        - P(A0-B0=-k-1) - P(A1-B0=k) - P(A1-B1=-k-1) - P(A0-B1=k+1)]
        def Pd(beh, x, y, rel):
            return sum(beh[(x, y, (l + rel) % d, l)] for l in range(d))

        def cglmp(beh):
            I = Fr(0)
            for k in range(d // 2):
                c = 1 - Fr(2 * k, d - 1)
                I += c * (Pd(beh, 0, 0, k) + Pd(beh, 1, 0, -(k + 1)) + Pd(beh, 1, 1, k) + Pd(beh, 0, 1, -k)
                          - Pd(beh, 0, 0, -k - 1) - Pd(beh, 1, 0, k) - Pd(beh, 1, 1, -k - 1) - Pd(beh, 0, 1, k + 1))
            return I
        U = {k: Fr(1, d * d) for k in PR}
        assert cglmp(PR) == 4 and cglmp(U) == 0
        # uniform marginals, no-signalling:
        for x, a in itertools.product(range(2), range(d)):
            for y in range(2):
                assert sum(PR[(x, y, a, b)] for b in range(d)) == Fr(1, d)
        # CGLMP(v PR + (1-v) u) = 4v > 2 iff v > 1/2;  lemma: local at v = 1/2  =>  v_c(PR_d) = 1/2 exactly
        print(f'(c) d={d}: CGLMP(PR_d) = 4, CGLMP(u) = 0  =>  v_c(PR_d) = 1/2 (lemma is sharp)')
    # (d) where is v_thr(d) < 1/2 ?
    half = QS2(Fr(1, 2))
    below = [d for d in range(2, 200) if (v_thr_exact(d) - half).sign() < 0]
    above = [d for d in range(2, 200) if (v_thr_exact(d) - half).sign() > 0]
    print('(d) v_thr(d) < 1/2 exactly for d in', below[:6], '...', below[-1], '; > 1/2 for d in', above)


if __name__ == '__main__':
    main()
