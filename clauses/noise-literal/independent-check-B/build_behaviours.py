"""
Step 1: build the two behaviours of the (2,2,d) literal-noise claim and verify them EXACTLY.

Convention: Phi_d = d^{-1/2} sum_i |ii>,  p(a,b|x,y) = Tr((A^x_a)^T B^y_b)/d,  x,y in {0,1}, a,b in {0..d-1}.

(i) Competitor C_d.
    Qubit CHSH projectors (real): outcome 0 = |theta><theta|, outcome 1 = complement,
    theta_A0 = 0, theta_A1 = pi/4, theta_B0 = pi/8, theta_B1 = -pi/8.  All entries lie in Q(sqrt2):
    cos^2(pi/8) = (2+sqrt2)/4, cos(pi/8) sin(pi/8) = sqrt2/4, sin^2(pi/8) = (2-sqrt2)/4.
    even d: A^x_a = P^x_a (x) 1_{d/2} (a = 0,1), A^x_a = 0 (a >= 2); same for B.
    odd d : C^d = (C^2)^{(d-1)/2} (+) C; on each 2x2 block the qubit projectors, the last basis vector goes to outcome 1.
    Everything is checked in exact arithmetic over Q(sqrt2) (sympy): projector, PVM completeness, ranks,
    probabilities against the closed forms
        even: p(a,b|xy) = (1 + (-1)^{a+b+xy}/sqrt2)/4 on {0,1}^2, 0 elsewhere
        odd : p = ((d-1)/d) p_CHSH + (1/d) delta_{a,1} delta_{b,1}.

(ii) DKZ_d (CGLMP PRL 88, 040404, eqs. (12)-(15) conventions):
    |k>_{A,x} = d^{-1/2} sum_j w^{j(k+alpha_x)} |j>,  |l>_{B,y} = d^{-1/2} sum_j w^{j(-l+beta_y)} |j>,
    w = exp(2 pi i/d), alpha = (0, 1/2), beta = (1/4, -1/4).
    Closed form:  p(k,l|x,y) = 1 / (2 d^3 sin^2(pi (k - l + alpha_x + beta_y)/d)).
    Exact check in the cyclotomic field Q(zeta_N), N = 4d: orthonormality of every basis (PVM), and
    p(k,l|x,y) * 2 d^3 * sin^2(...) = 1 with sin^2(pi m/N) = (2 - zeta^m - zeta^{-m})/4.

Run:  python build_behaviours.py      (prints PASS lines; exits with error on any failure)
"""
import sys
from fractions import Fraction as Fr
import sympy as sp

S2 = sp.sqrt(2)


# ---------------------------------------------------------------- competitor (exact, Q(sqrt2))
def qubit_projectors():
    """Return dict (party, setting) -> [P0, P1] as exact 2x2 sympy matrices."""
    c2 = (2 + S2) / 4      # cos^2(pi/8)
    s2 = (2 - S2) / 4      # sin^2(pi/8)
    cs = S2 / 4            # cos(pi/8) sin(pi/8)

    def proj(c2_, cs_, s2_):
        P0 = sp.Matrix([[c2_, cs_], [cs_, s2_]])
        return [P0, sp.eye(2) - P0]
    out = {}
    out[('A', 0)] = proj(sp.Integer(1), sp.Integer(0), sp.Integer(0))      # theta = 0
    out[('A', 1)] = proj(sp.Rational(1, 2), sp.Rational(1, 2), sp.Rational(1, 2))  # theta = pi/4
    out[('B', 0)] = proj(c2, cs, s2)                                         # theta = pi/8
    out[('B', 1)] = proj(c2, -cs, s2)                                        # theta = -pi/8
    return out


def competitor_pvms(d):
    """Exact d x d PVMs of the competitor (list of d effects per (party, setting))."""
    Q = qubit_projectors()
    pv = {}
    for key, (P0, P1) in Q.items():
        if d % 2 == 0:
            m = d // 2
            E0 = sp.kronecker_product(P0, sp.eye(m))
            E1 = sp.kronecker_product(P1, sp.eye(m))
        else:
            nb = (d - 1) // 2
            E0 = sp.zeros(d, d)
            E1 = sp.zeros(d, d)
            for blk in range(nb):
                E0[2 * blk:2 * blk + 2, 2 * blk:2 * blk + 2] = P0
                E1[2 * blk:2 * blk + 2, 2 * blk:2 * blk + 2] = P1
            E1[d - 1, d - 1] = 1
        effects = [E0, E1] + [sp.zeros(d, d) for _ in range(d - 2)]
        pv[key] = effects
    return pv


def p_chsh_closed(a, b, x, y):
    if a > 1 or b > 1:
        return sp.Integer(0)
    return (1 + (-1) ** (a + b + x * y) / S2) / 4


def competitor_closed(d, a, b, x, y):
    if d % 2 == 0:
        return p_chsh_closed(a, b, x, y)
    extra = sp.Integer(1) if (a == 1 and b == 1) else sp.Integer(0)
    return sp.Rational(d - 1, d) * p_chsh_closed(a, b, x, y) + sp.Rational(1, d) * extra


def check_competitor(d):
    pv = competitor_pvms(d)
    I = sp.eye(d)
    for key, effs in pv.items():
        tot = sp.zeros(d, d)
        for E in effs:
            assert sp.simplify(E * E - E) == sp.zeros(d, d), (d, key, 'not idempotent')
            assert E == E.T, (d, key, 'not symmetric (real Hermitian)')
            tot += E
        assert sp.simplify(tot - I) == sp.zeros(d, d), (d, key, 'not complete')
        ranks = [sp.simplify(E.trace()) for E in effs]   # rank = trace for projectors
        if d % 2 == 0:
            want = [d // 2, d // 2] + [0] * (d - 2)
        else:
            want = [(d - 1) // 2, (d + 1) // 2] + [0] * (d - 2)
        assert ranks == want, (d, key, ranks, want)
    # probabilities
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    val = sp.nsimplify(sp.simplify((pv[('A', x)][a].T * pv[('B', y)][b]).trace() / d))
                    want = competitor_closed(d, a, b, x, y)
                    assert sp.simplify(val - want) == 0, (d, x, y, a, b, val, want)
    return True


# ---------------------------------------------------------------- DKZ (exact, cyclotomic field)
class Cyc:
    """Element of Q(zeta_N) as {exponent mod N: Fraction}; zero test via reduction mod Phi_N."""
    def __init__(self, N, coeffs=None):
        self.N = N
        self.c = {}
        if coeffs:
            for e, v in coeffs.items():
                self._add(e, v)

    def _add(self, e, v):
        e %= self.N
        nv = self.c.get(e, Fr(0)) + Fr(v)
        if nv == 0:
            self.c.pop(e, None)
        else:
            self.c[e] = nv

    def __add__(self, o):
        r = Cyc(self.N, self.c)
        for e, v in o.c.items():
            r._add(e, v)
        return r

    def __sub__(self, o):
        r = Cyc(self.N, self.c)
        for e, v in o.c.items():
            r._add(e, -v)
        return r

    def __mul__(self, o):
        r = Cyc(self.N)
        if isinstance(o, (int, Fr)):
            for e, v in self.c.items():
                r._add(e, v * o)
            return r
        for e1, v1 in self.c.items():
            for e2, v2 in o.c.items():
                r._add(e1 + e2, v1 * v2)
        return r

    def conj(self):
        return Cyc(self.N, {-e: v for e, v in self.c.items()})

    def is_zero(self):
        if not self.c:
            return True
        X = sp.Symbol('X')
        poly = sum(sp.Rational(v.numerator, v.denominator) * X ** e for e, v in self.c.items())
        rem = sp.rem(sp.Poly(poly, X, domain='QQ'), sp.Poly(sp.cyclotomic_poly(self.N, X), X, domain='QQ'))
        return rem.is_zero


def dkz_vectors(d):
    """Return dict (party, setting) -> list of d basis vectors, each a list of d Cyc entries,
    WITHOUT the d^{-1/2} normalisation (so <v_k|v_k'> = d delta)."""
    N = 4 * d
    four_alpha = [0, 2]      # 4*alpha_x, alpha = (0, 1/2)
    four_beta = [1, -1]      # 4*beta_y,  beta  = (1/4, -1/4)
    vec = {}
    for x in range(2):
        vec[('A', x)] = [[Cyc(N, {4 * j * k + j * four_alpha[x]: 1}) for j in range(d)] for k in range(d)]
    for y in range(2):
        vec[('B', y)] = [[Cyc(N, {-4 * j * l + j * four_beta[y]: 1}) for j in range(d)] for l in range(d)]
    return vec, four_alpha, four_beta


def check_dkz(d):
    N = 4 * d
    vec, fa, fb = dkz_vectors(d)
    # orthonormality (=> rank-one PVMs): sum_j conj(v_k[j]) v_k'[j] = d delta_{k k'}
    for key, vs in vec.items():
        for k in range(d):
            for k2 in range(d):
                s = Cyc(N)
                for j in range(d):
                    s = s + vs[k][j].conj() * vs[k2][j]
                target = Cyc(N, {0: d if k == k2 else 0})
                assert (s - target).is_zero(), (d, key, k, k2)
    # probabilities: p = |sum_j phi_j chi_j|^2 / d with phi, chi normalised -> |sum_j v_j w_j|^2 / d^3
    # closed form: p = 1/(2 d^3 sin^2(pi m / N)), m = 4(k-l) + 4 alpha_x + 4 beta_y,
    # sin^2(pi m/N) = (2 - zeta^m - zeta^-m)/4.  Check |S|^2 * 2 * (2 - zeta^m - zeta^-m)/4 == 1.
    for x in range(2):
        for y in range(2):
            for k in range(d):
                for l in range(d):
                    S = Cyc(N)
                    for j in range(d):
                        S = S + vec[('A', x)][k][j] * vec[('B', y)][l][j]
                    mod2 = S * S.conj()
                    m = 4 * (k - l) + fa[x] + fb[y]
                    sin2x4 = Cyc(N, {0: 2}) - Cyc(N, {m: 1}) - Cyc(N, {-m: 1})   # = 4 sin^2
                    lhs = mod2 * sin2x4 * Fr(1, 2)        # = 2 |S|^2 sin^2
                    assert (lhs - Cyc(N, {0: 1})).is_zero(), (d, x, y, k, l)
    return True


def dkz_closed_float(d, k, l, x, y):
    import mpmath as mp
    al = [mp.mpf(0), mp.mpf(1) / 2]
    be = [mp.mpf(1) / 4, -mp.mpf(1) / 4]
    return 1 / (2 * d ** 3 * mp.sin(mp.pi * (k - l + al[x] + be[y]) / d) ** 2)


def cglmp_value_dkz(d):
    """CGLMP value of DKZ from the closed form (high precision; sanity check vs I_ME(d))."""
    import mpmath as mp
    mp.mp.dps = 40
    P = lambda x, y, k, l: dkz_closed_float(d, k, l, x, y)
    # chain form with A1=x0, A2=x1, B1=y0, B2=y1:  I = sum_k (1-2k/(d-1)) [P(A1=B1+k)+P(B1=A2+k+1)+P(A2=B2+k)+P(B2=A1+k)
    #   - P(A1=B1-k-1) - P(B1=A2-k) - P(A2=B2-k-1) - P(B2=A1-k-1)]
    def Pd(x, y, rel):     # P(A_x - B_y = rel mod d)
        return sum(P(x, y, (l + rel) % d, l) for l in range(d))
    I = 0
    for kk in range(d // 2):
        c = 1 - mp.mpf(2 * kk) / (d - 1)
        I += c * (Pd(0, 0, kk) + Pd(1, 0, -(kk + 1)) + Pd(1, 1, kk) + Pd(0, 1, -kk)
                  - Pd(0, 0, -kk - 1) - Pd(1, 0, kk) - Pd(1, 1, -kk - 1) - Pd(0, 1, kk + 1))
    IME = 4 / mp.mpf(d * (d - 1)) * sum((d - j) / mp.cos(mp.pi * j / (2 * d)) for j in range(1, d))
    return I, IME


if __name__ == '__main__':
    ok = True
    for d in range(2, 10):
        check_competitor(d)
        print(f'PASS competitor d={d}: exact PVMs (projectors, complete, ranks), p = closed form (Q(sqrt2))')
    for d in range(2, 10):
        check_dkz(d)
        print(f'PASS DKZ d={d}: exact orthonormal Fourier bases, p = 1/(2 d^3 sin^2(pi(k-l+alpha+beta)/d)) in Q(zeta_{4*d})')
    for d in range(3, 10):
        I, IME = cglmp_value_dkz(d)
        assert abs(I - IME) < 1e-30
        print(f'     d={d}: CGLMP(DKZ) = {float(I):.10f} = I_ME(d) = {float(IME):.10f}')
    print('ALL PASS')
