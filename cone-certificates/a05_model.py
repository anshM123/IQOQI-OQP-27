"""a05: the smooth model u_e as interval jets (CONE_ALLD_PROOF.md section 2).
  Ch_j = eps^(j-1) { k_j [B_2j(1/w) - (x/(1-x))^(2j-1) B_2j(1/v)] + (pi/2) x^(2j-1) d_x^2j S / (2^j j!) },  k_j = 2 (2j-2)!/(2^j j!),
  w = eps/x = 1/b, v = eps/(1-x) = 1/(d-b);  tauh = (pi/2)(Tt + EMx);  u_e = Newton^NEWT(u0 = tauh/Ch_1) for sum_{j<=J} Ch_j u^j = tauh.
  Phi_e(b) = eps b^2 u_e(b).
Outputs:  zone O (variable x, eps an interval):  Q_O = d_x^4 [x^2 (u_e - A0/B(1/w))]  (= d^3 d_b^4 [eps b^2 (u_e - A0/B)]);
          zone I (variables x, w):  L = Lambda(d_x^2 u_e) = sum c_il x^i w^l d_x^(2+i) d_w^l u_e,  Lambda = (th+1)(th+2)(th+3)(th+4),
          th = x d_x - w d_w; then d_b^4[b^2 R](b) = Lambda(R2) in (1/2) hull(L over the box)  (R2 = x-Taylor remainder of u_e)."""
import math
from fractions import Fraction
import mpmath
from mpmath import iv
from a02_jets import Jet, Space, Z, ONE, compose2, ivq, ivfact, ivff
from a03_special import PI, binet_w, binet_near
from a04_regular import poch_sums, em_over_x, AEM

A0 = PI / 2 - 1
J_ORDER = 4
NEWT = 3


def kj(j):
    return ivq(Fraction(2 * math.factorial(2 * j - 2), 2 ** j * math.factorial(j)))


def is_const(J):
    return all(c is Z for c in J.c[1:])


def regular_parts(T, X, E, Nc, J=J_ORDER, ne=None):
    """returns ([G_1..G_J], Tt, EM) as jets in the target space T; G_j = d_x^2j S composed with (X, E).
    ne = eps-order needed for the composition (default T.T; may be smaller when E - E0 has x-degree >= its degree)."""
    xbox, ebox = X.c[0], E.c[0]
    n = T.T
    ne = n if ne is None else ne
    G, out = [], {}
    if is_const(E):
        S1 = Space(n + 2 * J, 0, n + 2 * J)
        Sj, Tj = poch_sums(S1, xbox, ebox, Nc)
        for j in range(1, J + 1):
            F = [Sj.c[2 * j + k] * ivff(2 * j + k, 2 * j) for k in range(n + 1)]       # (2j+k)!/k!, exact
            G.append(X.compose1(F))
        Tt = X.compose1([Tj.c[k] for k in range(n + 1)])
    else:
        S2 = Space(n + 2 * J, ne, n + 2 * J)
        Sj, Tj = poch_sums(S2, xbox, ebox, Nc)
        SG = Space(n, ne, n)
        for j in range(1, J + 1):
            Gj = Jet(SG, [Sj[(a + 2 * j, c)] * ivff(a + 2 * j, 2 * j) for (a, c) in SG.idx])
            G.append(compose2(Gj, X, E))
        Tt = compose2(Jet(SG, [Tj[(a, c)] for (a, c) in SG.idx]), X, E)
    S1x = Space(n, 0, n)
    em = em_over_x(S1x, Jet.var(S1x, 0, xbox))
    EM = {k: X.compose1(em[k].c) for k in (1, 2)}
    return G, Tt, EM


def model_jets(T, X, W, E, V, Nc, J=J_ORDER, ne=None, raw=False):
    """Ch_1..Ch_J and tauh as jets in T (raw=True: Ch_j/eps^(j-1), i.e. without the factor E^(j-1))."""
    G, Tt, EM = regular_parts(T, X, E, Nc, J, ne)
    ratio = X * (X * (-1) + 1).recip()
    vmax = V.c[0].b
    C = []
    for j in range(1, J + 1):
        Bw = binet_w(j, W)
        Bv = binet_near(j, V, vmax)
        sing = (Bw - (ratio ** (2 * j - 1)) * Bv) * kj(j)
        reg = (X ** (2 * j - 1)) * G[j - 1] * (PI / 2 / iv.mpf(2 ** j * math.factorial(j)))
        C.append((sing + reg) if raw else (sing + reg) * (E ** (j - 1)))
    tauh = (Tt + EM[1] * E * AEM[1] + EM[2] * (E ** 3) * AEM[2]) * (PI / 2)
    return C, tauh


def newton_u(C, tauh, nsteps=NEWT):
    u = tauh * C[0].recip()
    for _ in range(nsteps):
        P = C[-1] * 1
        for j in range(len(C) - 2, -1, -1):          # Horner: P = (((C_J u + C_{J-1}) u + ...) + C_1) u - tauh
            P = P * u + C[j]
        P = P * u - tauh
        dP = C[-1] * len(C)
        for j in range(len(C) - 2, -1, -1):
            dP = dP * u + C[j] * (j + 1)
        u = u - P * dP.recip()
    return u


def halfshift(J):
    """A(x)/(1-2x) for an antisymmetric A (A(1/2) = 0) on a box containing 1/2: coefficient k <- -(1/2) A[k+1] (target order -1)."""
    n = J.S.T - 1
    Sn = Space(n, 0, n)
    return Jet(Sn, [J.c[k + 1] * (-ONE / 2) for k in range(n + 1)])


def poly_eval(C, U, tauh):
    """P(U) = sum_j C_j U^j - tauh (jets)."""
    P = C[-1] * 1
    for j in range(len(C) - 2, -1, -1):
        P = P * U + C[j]
    return P * U - tauh


def krawczyk_root(c, t, guess):
    """enclosure R of the unique root of p(u) = sum_j c_j u^j - t (interval coefficients) near guess; raises if not verified."""
    def p(u):
        s = c[-1]
        for j in range(len(c) - 2, -1, -1):
            s = s * u + c[j]
        return s * u - t
    def dp(u):
        s = c[-1] * len(c)
        for j in range(len(c) - 2, -1, -1):
            s = s * u + c[j] * (j + 1)
        return s
    m = iv.mpf(guess.mid) if hasattr(guess, 'mid') else iv.mpf(guess)
    for _ in range(60):                                    # refine the midpoint (thin Newton on centre values)
        cm = [iv.mpf(x.mid) for x in c]
        tm = iv.mpf(t.mid)
        pm = cm[-1]
        for j in range(len(cm) - 2, -1, -1):
            pm = pm * m + cm[j]
        pm = pm * m - tm
        dm = cm[-1] * len(cm)
        for j in range(len(cm) - 2, -1, -1):
            dm = dm * m + cm[j] * (j + 1)
        m = iv.mpf((m - pm / dm).mid)
    Yinv = ONE / iv.mpf(dp(m).mid)
    r = abs((p(m) * Yinv)).b * 2 + abs(m).b * iv.mpf(2) ** (-100)
    for _ in range(40):
        R = m + iv.mpf([-r, r])
        Kr = m - p(m) * Yinv + (1 - dp(R) * Yinv) * (R - m)
        if Kr.a > R.a and Kr.b < R.b:
            return Kr
        r = r * 2
    raise ValueError("Krawczyk failed")


def _poly_iv(c, t, U):
    s = c[-1]
    for j in range(len(c) - 2, -1, -1):
        s = s * U + c[j]
    return s * U - t


def root_free(c, t, R, depth=12):
    """True if p(u) = sum_j c_j u^j - t (interval coefficients) is certainly nonzero on [0,1] minus the open interval int(R):
    interval Horner evaluation on [0, R.a] and [R.b, 1], bisected up to 'depth' levels."""
    def free(lo, hi, lev):
        if lo >= hi:
            return True
        v = _poly_iv(c, t, iv.mpf([lo, hi]))
        if v.a > 0 or v.b < 0:
            return True
        if lev == 0:
            return False
        mid = iv.mpf([lo, hi]).mid
        return free(lo, mid, lev - 1) and free(mid, hi, lev - 1)
    zero, one = iv.mpf(0).a, iv.mpf(1).a
    ok = True
    if R.a > 0:
        ok &= free(zero, R.a, depth)
    if R.b < 1:
        ok &= free(R.b, one, depth)
    return ok


def implicit_root_jet(C, tauh):
    """jet of the exact root u(s) of sum_j C_j(s) u^j = tauh(s): value by Krawczyk, higher coefficients degree by degree
    from [P(U)]_alpha = P_u(u0) c_alpha + F_alpha(c_{<alpha}) = 0  (u0 in R, F evaluated with the enclosures)."""
    S = C[0].S
    c0 = [cj.c[0] for cj in C]
    R = krawczyk_root(c0, tauh.c[0], tauh.c[0] / c0[0])
    # R must contain the MODEL root u_e (the unique root in (0,1), certified on the a10 boxes).  If R lies in (0,1) this holds;
    # otherwise we verify that the polynomial has no zero on [0,1] \ R for every coefficient choice in the box enclosures,
    # so the root u_e in (0,1) lies in R, where Krawczyk's root is unique.
    if not (R.a > 0 and R.b < 1):
        if not root_free(c0, tauh.c[0], R):
            raise ValueError("Krawczyk enclosure may miss the model root")
    dpR = c0[-1] * len(c0)
    for j in range(len(c0) - 2, -1, -1):
        dpR = dpR * R + c0[j] * (j + 1)
    U = Jet.const(S, R)
    for deg in range(1, S.T + 1):
        P = poly_eval(C, U, tauh)
        for k, (i, l) in enumerate(S.idx):
            if i + l == deg:
                U.c[k] = -P.c[k] / dpR
    return U
