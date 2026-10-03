"""
Remark (robustness of the counterexample to the 'unused outcomes' objection).

On Phi_D, D = 2M (M >= d-1), take orthonormal real vectors e_2..e_{d-1} in R^M, Pi = 1_M - sum_k e_k e_k^T and
    A^x_a = P^x_a (x) Pi  (a = 0,1),   A^x_k = 1_2 (x) e_k e_k^T  (k = 2..d-1),   same for Bob (P -> Q),
with P, Q the qubit CHSH projectors.  Every outcome has a nonzero effect, and
    p = (1 - eps) p_CHSH + (1/M) sum_{k>=2} delta_{kk},     eps = (d-2)/M
(Tr((P(x)Pi)^T (Q(x)Pi))/D = Tr(P^T Q)(M-d+2)/(2M), Tr((1(x)e_k e_k^T)^T (1(x)e_l e_l^T))/D = delta_kl/M, cross terms 0).
Coarse CHSH (0 | rest): S(p) = (1-eps) 2sqrt2 + 2 eps, S(u) = 2c, c = (d-2)^2/d^2, so
    v_c(p) <= v_M := (1-c)/((1-eps) sqrt2 + eps - c).
This script finds, exactly (Q(sqrt2) sign tests), the least M with v_M < v_cert(d), where v_cert(d) is the certified
lower bound of v_c(DKZ_d) from certificates/dkz_d{d}.json ('main'), and checks the behaviour formula exactly
(QS2 arithmetic) by building the D x D matrices for the least M when D <= 40.
"""
import json
import os
from fractions import Fraction as Fr
import sympy as sp
from competitor_exact import QS2, SQ2

HERE = os.path.dirname(os.path.abspath(__file__))


def v_M(d, M):
    c = Fr((d - 2) ** 2, d * d)
    eps = Fr(d - 2, M)
    return QS2(1 - c) / ((1 - eps) * SQ2 + (eps - c))


def check_matrices(d, M):
    S2 = sp.sqrt(2)
    c2, s2, cs = (2 + S2) / 4, (2 - S2) / 4, S2 / 4
    P = {('A', 0): sp.Matrix([[1, 0], [0, 0]]), ('A', 1): sp.Matrix([[sp.Rational(1, 2)] * 2] * 2),
         ('B', 0): sp.Matrix([[c2, cs], [cs, s2]]), ('B', 1): sp.Matrix([[c2, -cs], [-cs, s2]])}
    E = [sp.zeros(M, M) for _ in range(d)]
    for k in range(2, d):
        E[k][k - 2, k - 2] = 1                       # e_k = standard basis vector
    Pi = sp.eye(M) - sum((E[k] for k in range(2, d)), sp.zeros(M, M))
    D = 2 * M
    eff = {}
    for key, P0 in P.items():
        effs = [sp.kronecker_product(P0, Pi), sp.kronecker_product(sp.eye(2) - P0, Pi)]
        effs += [sp.kronecker_product(sp.eye(2), E[k]) for k in range(2, d)]
        assert sp.simplify(sum(effs, sp.zeros(D, D)) - sp.eye(D)) == sp.zeros(D, D)
        assert all(sp.simplify(F * F - F) == sp.zeros(D, D) and F.trace() != 0 for F in effs)
        eff[key] = effs
    eps = sp.Rational(d - 2, M)
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    val = sp.simplify((eff[('A', x)][a].T * eff[('B', y)][b]).trace() / D)
                    if a <= 1 and b <= 1:
                        want = (1 - eps) * (1 + (-1) ** (a + b + x * y) / S2) / 4
                    else:
                        want = sp.Rational(1, M) if (a == b) else 0
                    assert sp.simplify(val - want) == 0, (d, M, x, y, a, b, val, want)


def main():
    for d in range(3, 13):
        path = os.path.join(HERE, 'certificates', f'dkz_d{d}.json')
        vcert = Fr(json.load(open(path))['certificates']['main']['v'])
        M = d - 1
        while (v_M(d, M) - QS2(vcert)).sign() >= 0:
            M += 1
            if M > 10 ** 4:
                break
        msg = f'd={d:2d}: v_cert(DKZ) = {float(vcert):.6f};  least M with v_M < v_cert: M = {M} (D = {2 * M}), ' \
              f'v_M = {float(v_M(d, M)):.6f};  limit M->inf: {float(v_M(d, 10 ** 12)):.6f}'
        if 2 * M <= 40:
            check_matrices(d, M)
            msg += '  [matrices checked exactly]'
        print(msg)


if __name__ == '__main__':
    main()
