"""
Step 2: the competitor C_d -- coarse-grained CHSH threshold and an EXACT local model at the threshold.

Part A (symbolic, all d):  sympy derivation of the coarse-grained CHSH values and of the violation thresholds
         v_even(d) = 4(d-1)/(4(d-1) + (sqrt2-1) d^2),  v_odd(d) = 4/(4 + (sqrt2-1) d).
Part B (symbolic, all s = 1/d in (0, 1/2]): the explicit 'flag' local model of the 3-outcome reduction
         R_v = v P + (1-v) nu(x)nu,  nu = (s, s, 1-2s)  reproduces R_v exactly at v = T(s) = 4s(1-s)/(sqrt2-(1-2s)^2),
         all weights are >= 0 for every s in (0, 1/2]; odd-d reduction identity.
Part C (exact, per d): for d = 2..D_MAX the d-outcome local model (stars refined uniformly into 2..d-1) is built
         with weights in Q(sqrt2) (exact class QS2), all weights checked >= 0 and the model checked to reproduce
         q = v_thr p_C + (1 - v_thr) u ENTRY BY ENTRY in exact arithmetic; the coarse-grained CHSH value of q is
         exactly 2 (tight) and the coarse-grained CHSH inequality is checked on all d^4 deterministic strategies.

Run: python competitor_exact.py [D_MAX]     (default D_MAX = 9)
"""
import sys
import itertools
from fractions import Fraction as Fr
import sympy as sp


# ============================================================ exact arithmetic in Q(sqrt2)
class QS2:
    __slots__ = ('a', 'b')

    def __init__(self, a=0, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    @staticmethod
    def c(x):
        return x if isinstance(x, QS2) else QS2(x, 0)

    def __add__(self, o):
        o = QS2.c(o)
        return QS2(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __neg__(self):
        return QS2(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-QS2.c(o))

    def __rsub__(self, o):
        return QS2.c(o) - self

    def __mul__(self, o):
        o = QS2.c(o)
        return QS2(self.a * o.a + 2 * self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def __pow__(self, k):
        assert isinstance(k, int) and k >= 0
        r = QS2(1)
        for _ in range(k):
            r = r * self
        return r

    def inv(self):
        n = self.a * self.a - 2 * self.b * self.b      # != 0 unless self == 0 (sqrt2 irrational)
        if n == 0:
            raise ZeroDivisionError
        return QS2(self.a / n, -self.b / n)

    def __truediv__(self, o):
        return self * QS2.c(o).inv()

    def __rtruediv__(self, o):
        return QS2.c(o) * self.inv()

    def sign(self):
        """exact sign of a + b sqrt2"""
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        # opposite signs: compare a^2 with 2 b^2
        if a > 0:      # a > 0 > b: positive iff a^2 > 2 b^2
            return 1 if a * a > 2 * b * b else -1
        return 1 if 2 * b * b > a * a else -1   # a < 0 < b

    def __eq__(self, o):
        o = QS2.c(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def __float__(self):
        return float(self.a) + float(self.b) * 2 ** 0.5

    def __repr__(self):
        return f'({self.a} + {self.b}*sqrt2)'


SQ2 = QS2(0, 1)


# ============================================================ Part A: symbolic thresholds
def part_A():
    d, v = sp.symbols('d v', positive=True)
    r2 = sp.sqrt(2)
    s = 1 / d
    # coarse-grained uniform noise: mu = (1/d, (d-1)/d) per party; E_xy(pi u) = (mu0 - mu1)^2
    Eu = ((1 - (d - 1)) / d) ** 2
    S_u = 2 * Eu                                    # E00 + E01 + E10 - E11 = 2 Eu
    S_even = 4 / r2                                 # 2 sqrt2: CHSH qubit box
    S_odd = (d - 1) / d * 4 / r2 + 2 / d            # ((d-1)/d) 2sqrt2 + (1/d) S(delta_11), S(delta_11) = 2
    out = {}
    for name, Sp, claimed in [('even', S_even, 4 * (d - 1) / (4 * (d - 1) + (r2 - 1) * d ** 2)),
                              ('odd', S_odd, 4 / (4 + (r2 - 1) * d))]:
        thr = sp.solve(sp.Eq(v * Sp + (1 - v) * S_u, 2), v)
        assert len(thr) == 1
        diff = sp.simplify(thr[0] - claimed)
        assert diff == 0, (name, thr[0], claimed)
        # violation is equivalent to v > thr because S(p) - S(u) > 0:
        gap = sp.simplify(Sp - S_u)
        out[name] = (sp.simplify(thr[0]), gap)
        print(f'A: {name}: CHSH(q_v) = 2 at v = {sp.simplify(thr[0])}  (== claimed);  S(p) - S(u) = {sp.factor(gap)}')
    # S(p) - S(u) > 0 for d >= 2:
    #   even: 2sqrt2 - 2(d-2)^2/d^2 >= 2sqrt2 - 2 > 0 ;   odd: (2sqrt2 (d-1) + 2)/d - 2(d-2)^2/d^2 > 0 shown below
    g_odd = sp.expand((out['odd'][1]) * d ** 2)    # = 2 sqrt2 d(d-1) + 2d - 2(d-2)^2
    # g_odd = 2(sqrt2-1) d(d-1) + 8(d-1)  > 0 for d >= 2  (exact identity checked here)
    assert sp.simplify(g_odd - (2 * (r2 - 1) * d * (d - 1) + 8 * (d - 1))) == 0
    print('   odd: (S(p) - S(u)) d^2 = 2(sqrt2-1) d(d-1) + 8(d-1) > 0 for d >= 2;  even: S(p)-S(u) >= 2sqrt2-2 > 0')
    return out


# ============================================================ Part B: symbolic flag model for general s
CH = [(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, -1)]    # (x, y, sign s_xy) of CHSH = E00+E01+E10-E11
STAR = 2                                                # outcome index of '*' in the 3-outcome reduction


def chsh_saturating():
    """the 8 deterministic {0,1} strategies (a0,a1,b0,b1) with sum_xy s_xy (-1)^(a_x+b_y) = 2"""
    out = []
    for a0, a1, b0, b1 in itertools.product(range(2), repeat=4):
        al, be = (a0, a1), (b0, b1)
        val = sum(sg * (-1) ** (al[x] + be[y]) for x, y, sg in CH)
        if val == 2:
            out.append((a0, a1, b0, b1))
    assert len(out) == 8
    return out


def single_star_strategies():
    """the 4 single-star patterns x 2 root values: active links perfectly (anti)correlated with signs s_xy"""
    out = []
    for r in range(2):
        out.append((STAR, r, r, 1 - r))   # A0 = *: B0 = A1 (s10=+1), B1 = 1-A1 (s11=-1)
        out.append((r, STAR, r, r))       # A1 = *: B0 = A0 (s00=+1), B1 = A0 (s01=+1)
        out.append((r, 1 - r, STAR, r))   # B0 = *: A0 = B1 (s01=+1), A1 = 1-B1 (s11=-1)
        out.append((r, r, r, STAR))       # B1 = *: A0 = B0 (s00=+1), A1 = B0 (s10=+1)
    return out


def flag_model(v, s, one=1):
    """list of (strategy on {0,1,*}^4, weight) for the even target R_v (weights are expressions in v, s)."""
    rho = (one - v) * (one - 2 * s)
    sig = (one - v) * (one - 2 * s) ** 2
    model = [((STAR, STAR, STAR, STAR), sig)]
    for st in single_star_strategies():
        model.append((st, (rho - sig) / 2))
    pi0 = one - 4 * rho + 3 * sig
    for st in chsh_saturating():
        model.append((st, pi0 / 8))
    return model


def behaviour_of(model, n=3, zero=0):
    """sum of weights times deterministic behaviours, dict (x,y,a,b) -> value"""
    B = {}
    for x in range(2):
        for y in range(2):
            for a in range(n):
                for b in range(n):
                    B[(x, y, a, b)] = zero
    for st, w in model:
        al, be = st[:2], st[2:]
        for x in range(2):
            for y in range(2):
                B[(x, y, al[x], be[y])] = B[(x, y, al[x], be[y])] + w
    return B


def p_chsh(a, b, x, y, r2):
    if a > 1 or b > 1:
        return 0
    return (1 + (-1) ** (a + b + x * y) / r2) / 4


def part_B():
    s, v = sp.symbols('s v', positive=True)
    r2 = sp.sqrt(2)
    T = 4 * s * (1 - s) / (r2 - (1 - 2 * s) ** 2)
    nu = [s, s, 1 - 2 * s]
    model = flag_model(v, s, one=sp.Integer(1))
    B = behaviour_of(model, 3, sp.Integer(0))
    # target (even): R_v = v P_CHSH + (1-v) nu nu
    for (x, y, a, b), val in B.items():
        target = v * p_chsh(a, b, x, y, r2) + (1 - v) * nu[a] * nu[b]
        diff = sp.simplify((val - target).subs(v, T))
        assert diff == 0, ((x, y, a, b), diff)
    print('B: flag model reproduces R_v = v P_CHSH + (1-v) nu(x)nu identically in s at v = T(s)'
          ' = 4s(1-s)/(sqrt2-(1-2s)^2)')
    # nonnegativity of the weights at v = T(s), s in (0, 1/2]
    rho = (1 - T) * (1 - 2 * s)
    sig = (1 - T) * (1 - 2 * s) ** 2
    pi0 = sp.simplify(1 - 4 * rho + 3 * sig)
    one_minus_T = sp.simplify(1 - T)
    assert sp.simplify(one_minus_T - (r2 - 1) / (r2 - (1 - 2 * s) ** 2)) == 0
    # pi0 = [ (sqrt2 - (1-2s)^2) - (sqrt2-1)(1-2s)(1+6s) ] / (sqrt2 - (1-2s)^2) = 4s[(1-s) - (sqrt2-1)(1-3s)] / den
    num = sp.expand((r2 - (1 - 2 * s) ** 2) - (r2 - 1) * (1 - 2 * s) * (1 + 6 * s))
    assert sp.simplify(num - 4 * s * ((1 - s) - (r2 - 1) * (1 - 3 * s))) == 0
    assert sp.simplify(pi0 - num / (r2 - (1 - 2 * s) ** 2)) == 0
    print('B: weights at v = T(s): all-star = (1-T)(1-2s)^2 >= 0, single-star = (1-T)(1-2s)s >= 0 each,')
    print('   CHSH-saturating block pi0 = 4s[(1-s) - (sqrt2-1)(1-3s)]/(sqrt2-(1-2s)^2) > 0 for s in (0,1/2]')
    print('   (proof: (sqrt2-1)(1-3s) < 1-3s <= 1-s if s <= 1/3; < 0 < 1-s if s > 1/3; denominator >= sqrt2-1 > 0)')
    # odd reduction identity
    vodd = 4 * s / (4 * s + r2 - 1)        # = 4/(4 + (sqrt2-1) d) with s = 1/d
    vpp = vodd * (1 - s) / (1 - vodd * s)
    assert sp.simplify(vpp - T) == 0
    print('B: odd d: v_odd (1-s)/(1 - v_odd s) == T(s) identically  =>  R_v(odd) = v s delta_11 + (1-vs)[even target at T(s)]')
    # T(s) evaluated at s = 1/d equals v_even(d)
    d = sp.symbols('d', positive=True)
    assert sp.simplify(T.subs(s, 1 / d) - 4 * (d - 1) / (4 * (d - 1) + (r2 - 1) * d ** 2)) == 0
    print('B: T(1/d) == v_even(d) identically')


# ============================================================ Part C: exact per-d verification (full d outcomes)
def v_thr_exact(d):
    if d % 2 == 0:
        return QS2(4 * (d - 1)) / (QS2(4 * (d - 1)) + (SQ2 - 1) * (d * d))
    return QS2(4) / (QS2(4) + (SQ2 - 1) * d)


def competitor_exact_behaviour(d):
    """p_C(a,b|x,y) as dict with QS2 values"""
    half_inv_sqrt2 = QS2(0, Fr(1, 2))     # 1/sqrt2 = sqrt2/2
    P = {}
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    if a <= 1 and b <= 1:
                        val = (1 + (-1) ** (a + b + x * y) * half_inv_sqrt2) * Fr(1, 4)
                    else:
                        val = QS2(0)
                    if d % 2 == 1:
                        val = val * Fr(d - 1, d) + (Fr(1, d) if (a == 1 and b == 1) else 0)
                    P[(x, y, a, b)] = QS2.c(val)
    return P


def fine_model(d):
    """exact local model (list of (det strategy on Z_d^4, QS2 weight)) for q = v_thr p_C + (1-v_thr) u."""
    v = v_thr_exact(d)
    s = Fr(1, d)
    if d % 2 == 0:
        red = flag_model(v, s, one=QS2(1))
    else:
        vpp = v * (1 - s) / (1 - v * s)
        red = [((st), w * (1 - v * s)) for st, w in flag_model(vpp, s, one=QS2(1))]
        red.append(((1, 1, 1, 1), v * s))
    fine = []
    for st, w in red:
        stars = [i for i in range(4) if st[i] == STAR]
        if stars and d == 2:
            assert w == 0       # d = 2: no star mass
            continue
        k = len(stars)
        if k == 0:
            fine.append((st, w))
            continue
        wk = w * Fr(1, (d - 2) ** k)
        for fill in itertools.product(range(2, d), repeat=k):
            st2 = list(st)
            for i, val in zip(stars, fill):
                st2[i] = val
            fine.append((tuple(st2), wk))
    return v, red, fine


def part_C(dmax):
    for d in range(2, dmax + 1):
        v, red, fine = fine_model(d)
        # all weights >= 0 (exact sign)
        assert all(w.sign() >= 0 for _, w in fine), d
        P = competitor_exact_behaviour(d)
        B = behaviour_of(fine, d, QS2(0))
        u = QS2(Fr(1, d * d))
        for key, val in B.items():
            target = v * P[key] + (1 - v) * u
            assert val == target, (d, key, val, target)
        # total weight 1
        tot = QS2(0)
        for _, w in fine:
            tot = tot + w
        assert tot == 1, (d, tot)
        # coarse-grained CHSH of q at v_thr is exactly 2
        def coarse(a):
            return 0 if a == 0 else 1
        S = QS2(0)
        for x, y, sg in CH:
            for a in range(d):
                for b in range(d):
                    q = v * P[(x, y, a, b)] + (1 - v) * u
                    S = S + q * (sg * (-1) ** (coarse(a) + coarse(b)))
        assert S == 2, (d, S)
        # coarse-grained CHSH <= 2 on every deterministic strategy (validity, sanity check of the proof)
        mx = max(sum(sg * (-1) ** (coarse((a0, a1)[x]) + coarse((b0, b1)[y])) for x, y, sg in CH)
                 for a0, a1, b0, b1 in itertools.product(range(d), repeat=4))
        assert mx == 2
        # violation for every v > v_thr: S(v) is affine in v with slope S(p) - S(u) > 0
        Sp = QS2(0)
        Su = QS2(0)
        for x, y, sg in CH:
            for a in range(d):
                for b in range(d):
                    Sp = Sp + P[(x, y, a, b)] * (sg * (-1) ** (coarse(a) + coarse(b)))
                    Su = Su + u * (sg * (-1) ** (coarse(a) + coarse(b)))
        assert (Sp - Su).sign() > 0
        nz = sum(1 for _, w in fine if w.sign() > 0)
        print(f'C: d={d}: v_thr = {float(v):.15f} = {v};  exact local model with {nz} deterministic strategies '
              f'(weights in Q(sqrt2), all >= 0) reproduces v_thr p_C + (1-v_thr) u exactly; '
              f'coarse CHSH(q) = 2 exactly; max_det coarse CHSH = 2; S(p) - S(u) = {float(Sp - Su):.6f} > 0')


if __name__ == '__main__':
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    part_A()
    part_B()
    part_C(dmax)
    print('ALL PASS')
