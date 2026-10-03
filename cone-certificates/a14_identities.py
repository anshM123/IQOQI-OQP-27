"""a14: independent verification of the model identities of CONE_ALLD_PROOF.md (proofs: RIGOR_ALLD.md, section 2).
  (I1)  u_e(0, w) = A0/B(b)                         (b = 1/w; B = B_2 = b kappa_2(b))
  (I2)  b^3 d_x u_e(0, w) = phi_2(b)                 (phi_2 as in a08_A2.py)
  (W0)  omega(0, w) = -(1 - 2/pi)                    (slack function of a11_slack.py)
  (T/x) tauh_e = (pi/2) tau_e/b = (pi/2) (Tt + EMx)   (cancellation-free form used by a04/a05)
Part S (sympy, exact): the x-expansions at fixed w of every ingredient of the model, with generic symbols for the Taylor
  coefficients g_i, a_n and the Binet functions, then the special values g_3, a_2, a_3 from the closed form of g_r''.
Part N (mpmath, 80 digits, no code shared with a02-a11): the model equation sum_{j<=4} Ch_j u^j = tauh_e is solved at
  x = h, 2h, ..., 8h (fixed w), with Ch_j from psi-functions and Pochhammer polynomials, tauh_e from its DEFINITION
  (Euler-Maclaurin interpolant Pt and F_r, no Tt/EMx); U0, U1 by polynomial extrapolation; compared with A0/B and phi_2/b^3.
Part J (interval jets of a07_zoneI.u_jet at thin x = 0): enclosures of U0(w), U1(w) must contain A0/B, phi_2/b^3 (and the
  W0 value) at many w; a failure would refute the identity.
Usage: python a14_identities.py [S] [N] [J]   (default: all parts).  Log: logs/alld/identities.log, identities.json."""
import sys, json, time

PARTS = set(sys.argv[1:]) or {'S', 'N', 'J'}
OUT = {}


def part_S():
    import sympy as sp
    x, w = sp.symbols('x w', positive=True)
    eps = x * w
    NMAX = 10
    g = {i: (sp.Symbol(f'g{i}') if i % 2 == 1 else sp.Integer(0)) for i in range(0, NMAX + 1)}
    a = {n: sp.Symbol(f'a{n}') for n in range(0, NMAX + 1)}
    # Qt_n = (x^n - P_n)/(eps x), P_n = prod_{k<n} (x + k eps)/(1 + k eps);  along eps = x w:  r_k = x (1 + k w)/(1 + k w x),
    # so Qt_n = x^(n-2) [1 - prod_{k<n} (1 + k w)/(1 + k w x)]/w  (exact factorisation; the bracket is bounded near x = 0)
    Qt = {}
    ok_fac = True
    for n in range(0, NMAX + 1):
        Pdef = sp.prod([(x + k * eps) / (1 + k * eps) for k in range(n)]) if n else sp.Integer(1)
        fac = x ** (n - 2) * (1 - sp.prod([(1 + k * w) / (1 + k * w * x) for k in range(n)])) / w if n else sp.Integer(0)
        if n <= 6:
            ok_fac &= sp.cancel(sp.together((x ** n - Pdef) / (eps * x) - fac)) == 0
        Qt[n] = sp.expand(sp.series(fac, x, 0, 2).removeO()) if n <= 3 else sp.Integer(0)
    # n >= 4: Qt_n = x^(n-2) * (bounded) = O(x^2); the bracket at x = 0 is finite (1 - prod(1 + kw))
    ok_Qt = (Qt[0] == 0 and sp.simplify(Qt[1]) == 0
             and sp.simplify(Qt[2] - (-1 + (1 + w) * x)) == 0 and sp.simplify(Qt[3] - (-(3 + 2 * w) * x)) == 0 and ok_fac)
    print("S1  Qt_n = x^(n-2)[1 - prod_{k<n}(1+kw)/(1+kwx)]/w exactly (n <= 6); Qt_0 = Qt_1 = 0, Qt_2 = -1 + (1+w)x + O(x^2),"
          " Qt_3 = -(3+2w)x + O(x^2), Qt_n = O(x^2) for n >= 4:", ok_Qt, flush=True)
    # recursion check Qt_{n+1} = Qt_n r_n - x^(n-1) n (1-x)/(1 + n eps) (exact rational functions, n <= 8)
    ok_rec = True
    for n in range(1, 7):
        Pn = sp.prod([(x + k * eps) / (1 + k * eps) for k in range(n)])
        Pn1 = Pn * (x + n * eps) / (1 + n * eps)
        lhs = (x ** (n + 1) - Pn1) / (eps * x)
        rhs = (x ** n - Pn) / (eps * x) * (x + n * eps) / (1 + n * eps) - x ** (n - 1) * n * (1 - x) / (1 + n * eps)
        ok_rec &= sp.cancel(sp.together(lhs - rhs)) == 0
    print("S2  recursion Qt_{n+1} = Qt_n r_n - x^(n-1) n (1-x)/(1+n eps) exact (n <= 6):", ok_rec, flush=True)
    Tt = sp.expand(sum((g[n] - a[n]) * Qt[n] for n in range(0, NMAX + 1)))
    # EMx with g(x) = sum g_i x^i, g(1-x) = sum a_n x^n (so g^(2k)(1) = (2k)! a_2k)
    gx = sum(g[i] * x ** i for i in range(1, NMAX + 1))
    g1mx = sum(a[n] * x ** n for n in range(0, NMAX + 1))
    EM = 0
    for k, aEM in ((1, sp.Rational(-1, 12)), (2, sp.Rational(1, 240))):
        d2k = sp.diff(gx, x, 2 * k)
        d2k1 = sp.diff(g1mx, x, 2 * k)
        G1 = sp.factorial(2 * k) * a[2 * k]
        EM += aEM * eps ** (2 * k - 1) * (sp.cancel(d2k / x) - sp.cancel((d2k1 - G1) / x) - 2 * G1)
    EMs = sp.series(sp.expand(EM), x, 0, 2).removeO()
    tauh = sp.expand(sp.pi / 2 * (Tt + EMs))
    t0 = tauh.coeff(x, 0)
    t1 = tauh.coeff(x, 1)
    print("S3  tauh_e(0,w) =", sp.simplify(t0), ";  d_x tauh_e(0,w) =", sp.simplify(t1))
    # special values from the closed form g_r''(y) = 2 csc(pi y/2) - 4/(pi y)
    y = sp.Symbol('y')
    g2c = 2 / sp.sin(sp.pi * y / 2) - 4 / (sp.pi * y)
    ser = sp.series(g2c, y, 0, 6).removeO()
    g3v = sp.simplify(ser.coeff(y, 1) / 6)               # g_r'' = 6 g_3 y + 20 g_5 y^3 + ...
    g5v = sp.simplify(ser.coeff(y, 3) / 20)
    gpp1 = sp.simplify(g2c.subs(y, 1))
    gppp1 = sp.simplify(sp.diff(g2c, y).subs(y, 1))
    a2v = sp.simplify(gpp1 / 2)
    a3v = sp.simplify(-gppp1 / 6)
    ok_vals = (sp.simplify(ser.coeff(y, 0)) == 0 and sp.simplify(g3v - sp.pi / 36) == 0
               and sp.simplify(gpp1 - (2 - 4 / sp.pi)) == 0 and sp.simplify(gppp1 - 4 / sp.pi) == 0)
    print(f"S4  g_r''(0) = 0, g_3 = {g3v}, g_5 = {g5v}, g_r''(1) = {gpp1}, g_r'''(1) = {gppp1}, a_2 = {a2v}, a_3 = {a3v}:", ok_vals)
    # g_5 vs the Bernoulli formula of a03 (g_{2n+1} = 4 (1 - 2^(1-2n)) |B_2n| pi^(2n-1)/((2n+1)! 2n)), n = 1..4
    ok_bern = True
    for n in range(1, 5):
        gB = 4 * (1 - sp.Integer(2) ** (1 - 2 * n)) * abs(sp.bernoulli(2 * n)) * sp.pi ** (2 * n - 1) / (sp.factorial(2 * n + 1) * 2 * n)
        cf = sp.simplify(ser.coeff(y, 2 * n - 1) / ((2 * n + 1) * (2 * n))) if 2 * n - 1 <= 5 else None
        if cf is not None:
            ok_bern &= sp.simplify(cf - gB) == 0
    print("S5  Taylor coefficients of g_r'' at 0 agree with the Bernoulli formula of a03 (i = 3, 5):", ok_bern)
    sub = {a[2]: a2v, a[3]: a3v, g[3]: g3v}
    A0 = sp.pi / 2 - 1
    t1c = -(sp.Rational(2, 3) + 5 * sp.pi / 72 + 1 / (3 * sp.pi))
    ok_tau = (sp.simplify(t0.subs(sub) - A0) == 0
              and sp.simplify(t1.subs(sub) - sp.pi / 2 * (-(1 + sp.pi / 12) + t1c * w)) == 0)
    print("S6  tauh_e = A0 + (pi/2)[-(1 + pi/12) + t1c w] x + O(x^2) with t1c = -(2/3 + 5pi/72 + 1/(3pi)):", ok_tau)
    # Ch_j: B_2j(d-b) = Binet series in v = eps/(1-x) (1 - beta_j1 v^2 + O(v^4)); S^(2j)(x, eps) = sum (g_n - a_n) d_x^2j P_n
    Bs = {j: sp.Symbol(f'B{2*j}') for j in range(1, 5)}      # B_2j(b), b = 1/w fixed
    v = eps / (1 - x)
    # S^(2j)(x, eps) is C^1 near (0, 0) (RIGOR_ALLD.md, Lemma M1), so S^(2j)(x, x w) = S^(2j)(0, 0) + O(x); S^(2j)(0,0) =
    # sum_n (g_n - a_n) d_x^2j P_n(0, 0) and P_n(x, 0) = x^n, so only n = 2j contributes: (2j)! (g_2j - a_2j) = -(2j)! a_2j.
    xx, ee = sp.symbols('xx ee')
    ok_P = True
    for n in range(0, 9):
        Pn = sp.prod([(xx + k * ee) / (1 + k * ee) for k in range(n)]) if n else sp.Integer(1)
        ok_P &= sp.expand(sp.cancel(Pn.subs(ee, 0)) - xx ** n) == 0
    print("S6b P_n(x, 0) = x^n (n <= 8), hence d_x^2j S(0, 0) = -(2j)! a_2j:", ok_P, flush=True)
    Ch = {}
    for j in range(1, 5):
        kj = 2 * sp.factorial(2 * j - 2) / (2 ** j * sp.factorial(j))
        Bv = 1 - sp.Symbol(f'beta{j}') * v ** 2                    # Binet: B_2j(1/v) = 1 - beta_j1 v^2 + O(v^4), v = O(x)
        S2j0 = -sp.factorial(2 * j) * a[2 * j] + sp.Symbol(f'sig{j}') * x     # S^(2j)(x, xw) = S^(2j)(0,0) + O(x)
        Chj = eps ** (j - 1) * (kj * (Bs[j] - (x / (1 - x)) ** (2 * j - 1) * Bv)
                                + sp.pi / 2 * x ** (2 * j - 1) * S2j0 / (2 ** j * sp.factorial(j)))
        Ch[j] = sp.expand(sp.series(Chj, x, 0, 2).removeO())
    c10, c11 = Ch[1].coeff(x, 0), sp.simplify(Ch[1].coeff(x, 1).subs(sub))
    c20, c21 = Ch[2].coeff(x, 0), sp.simplify(Ch[2].coeff(x, 1))
    ok_ch = (sp.simplify(c10 - Bs[1]) == 0 and sp.simplify(c11 + sp.pi / 2) == 0 and c20 == 0
             and sp.simplify(c21 - w * Bs[2] / 2) == 0 and all(Ch[j] == 0 for j in (3, 4)))
    print(f"S7  Ch_1 = B - (pi/2) x + O(x^2), Ch_2 = (w B_4/2) x + O(x^2), Ch_3, Ch_4 = O(x^2):", ok_ch,
          f"  [Ch_1: {c10} + ({c11}) x;  Ch_2: ({c21}) x]")
    # implicit differentiation of sum_j Ch_j u^j = tauh_e at x = 0
    U0 = A0 / Bs[1]
    U1 = (t1.subs(sub) - c11 * U0 - c21 * U0 ** 2) / Bs[1]
    b = 1 / w
    phi2 = (-(sp.pi / 2) * (1 + sp.pi / 12) * b ** 3 / Bs[1] + (sp.pi / 2) * t1c * b ** 2 / Bs[1]
            + (sp.pi / 2) * A0 * b ** 3 / Bs[1] ** 2 - (A0 ** 2 / 2) * b ** 2 * Bs[2] / Bs[1] ** 3)
    ok_I1 = sp.simplify(t0.subs(sub) / c10 - A0 / Bs[1]) == 0
    ok_I2 = sp.simplify(b ** 3 * U1 - phi2) == 0
    print("S8  (I1) U0 = A0/B:", ok_I1, ";  (I2) b^3 U1 = phi_2 (exact symbolic identity):", ok_I2)
    # (W0): omega = Tg + EM_g - (2/pi) sum Ch+_j u^j at x = 0: Tg(0, 0) = sum g_n Qt_n(0,0) = g_2 (-1) = 0
    Tg0 = sp.expand(sum(g[n] * Qt[n] for n in range(0, NMAX + 1))).coeff(x, 0)
    om0 = sp.simplify(Tg0 - (2 / sp.pi) * Bs[1] * U0)
    ok_W0 = sp.simplify(om0 + (1 - 2 / sp.pi)) == 0
    print("S9  (W0) omega(0, w) = -(1 - 2/pi):", ok_W0, f"  [Tg(0,0) = {Tg0}]")
    allok = ok_Qt and ok_rec and ok_P and ok_vals and ok_bern and ok_tau and ok_ch and ok_I1 and ok_I2 and ok_W0
    OUT['S'] = dict(ok=bool(allok))
    print("PART S (symbolic):", "ALL IDENTITIES VERIFIED" if allok else "FAILED")
    return allok


def part_N():
    import mpmath as mpm
    from mpmath import mp, mpf, pi, psi
    mp.dps = 90
    A0 = pi / 2 - 1
    t1c = -(mpf(2) / 3 + 5 * pi / 72 + 1 / (3 * pi))
    # g_i from the zeta formula; a_n = g_r^(n)(1)(-1)^n/n! from mpmath.taylor of the closed form of g_r'' (no binomial sums)
    NG = 160
    g = {1: -(4 / pi) * (1 + mpm.log(4 / pi))}
    for i in range(3, NG + 1, 2):
        g[i] = (16 * mpm.zeta(i - 1) / pi) * (mpf(1) / 2 - mpf(2) ** (1 - i)) / (mpf(2) ** (i - 1) * (i - 1) * i)
    NA_ = 70
    g2c = lambda y: 2 / mpm.sin(pi * y / 2) - 4 / (pi * y)
    mp.dps = 140
    tay = mpm.taylor(g2c, mpf(1), NA_ - 2)          # g_r^(k+2)(1)/k!
    mp.dps = 90
    gr = lambda y: -(8 / pi ** 2) * (mpm.clsin(2, pi * y / 2) + mpm.clsin(2, pi - pi * y / 2)) - (4 / pi) * y * mpm.log(y)
    an = {0: gr(mpf(1)), 1: -(sum(g[i] * i for i in g))}
    for n in range(2, NA_ + 1):
        gn1 = tay[n - 2] * mpm.factorial(n - 2)        # g_r^(n)(1)
        an[n] = (-1) ** n * gn1 / mpm.factorial(n)
    # cross-check a_n against the binomial-sum formula (only as a sanity check of the two independent routes)
    chk = max(abs(an[n] - (-1) ** n * sum(g[i] * mpm.binomial(i, n) for i in g if i >= n)) for n in range(2, 12))
    def kap(n, bb):
        return n * psi(n - 1, bb + 1) + bb * psi(n, bb + 1)
    def Bj(j, bb):
        return bb ** (2 * j - 1) * kap(2 * j, bb) / mpm.factorial(2 * j - 2)
    def poch_derivs(xv, ev, n, r):
        """d_x^r P_n(x, eps) at (xv, ev): polynomial prod_{k<n}(x + k eps) expanded in x."""
        c = [mpf(1)]
        for k in range(n):
            ke = k * ev
            c = [(c[i] * ke if i < len(c) else 0) + (c[i - 1] if i >= 1 else 0) for i in range(len(c) + 1)]
        den = mpm.fprod([1 + k * ev for k in range(n)])
        s = sum(c[m] * mpm.ff(m, r) * xv ** (m - r) for m in range(r, len(c)))
        return s / den
    def Sder(xv, ev, r, NN=150):
        return sum((g.get(n, 0) - an.get(n, 0)) * poch_derivs(xv, ev, n, r) for n in range(r, NN) if n in an or n in g)
    def Gamma(xv, ev, coef, NN=150):
        return sum(coef[n] * poch_derivs(xv, ev, n, 0) for n in range(0, NN) if n in coef)
    def p_fun(y, ev):
        g2 = g2c(y)
        g4 = mpm.diff(g2c, y, 2)
        return gr(y) - ev ** 2 / 12 * g2 + ev ** 4 / 240 * g4
    def model_u(xv, wv):
        bb = 1 / wv; ev = xv * wv; dd = 1 / ev
        C = []
        for j in range(1, 5):
            kj = 2 * mpm.factorial(2 * j - 2) / (2 ** j * mpm.factorial(j))
            sing = kj * (Bj(j, bb) - (xv / (1 - xv)) ** (2 * j - 1) * Bj(j, dd - bb))
            reg = (pi / 2) * xv ** (2 * j - 1) * Sder(xv, ev, 2 * j) / (2 ** j * mpm.factorial(j))
            C.append(ev ** (j - 1) * (sing + reg))
        # tauh_e from the DEFINITION: tau_e = [Pt - F_r](b) - [Pt - F_r](d - b)
        p1 = p_fun(mpf(1), ev); g1 = gr(mpf(1))
        Pt = lambda c: dd ** 2 * (p_fun(c / dd, ev) - (c / dd) * (p1 - g1))
        Frb = dd ** 2 * Gamma(xv, ev, g)
        Frdb = dd ** 2 * Gamma(xv, ev, an)
        tau = (Pt(bb) - Frb) - (Pt(dd - bb) - Frdb)
        th = (pi / 2) * tau / bb
        # cancellation-free form (Tt + EMx), for the (T/x) check
        Tt = sum((g.get(n, 0) - an[n]) * (xv ** n - poch_derivs(xv, ev, n, 0)) / (ev * xv) for n in range(2, 150) if n in an)
        EMx = 0
        for k, aEM in ((1, mpf(-1) / 12), (2, mpf(1) / 240)):
            gk = lambda y: mpm.diff(g2c, y, 2 * k - 2)
            gk1 = gk(mpf(1))
            EMx += aEM * ev ** (2 * k - 1) * (gk(xv) / xv - (gk(1 - xv) - gk1) / xv - 2 * gk1)
        th2 = (pi / 2) * (Tt + EMx)
        u = th / C[0]
        for _ in range(60):
            P = sum(C[j] * u ** (j + 1) for j in range(4)) - th
            dP = sum((j + 1) * C[j] * u ** j for j in range(4))
            u -= P / dP
        return u, abs(th - th2) / abs(th)
    def phi2(bb):
        B = Bj(1, bb); B4 = Bj(2, bb)
        return (-(pi / 2) * (1 + pi / 12) * bb ** 3 / B + (pi / 2) * t1c * bb ** 2 / B + (pi / 2) * A0 * bb ** 3 / B ** 2
                - (A0 ** 2 / 2) * bb ** 2 * B4 / B ** 3)
    print(f"N0  a_n via taylor(closed form) vs binomial sums: max diff {mpm.nstr(chk, 3)} (n < 12)")
    h = mpf(10) ** -5
    KP = 8
    worst1 = worst2 = worstT = mpf(0)
    bs = [mpf(1), mpf(5) / 4, mpf(3) / 2, mpf(2), mpf(5) / 2, mpf(3), mpf(4), mpf(5), mpf(7), mpf(10), mpf(15), mpf(20),
          mpf(30), mpf(50), mpf(100), mpf(300), mpf(1000)]
    rows = []
    for bb in bs:
        wv = 1 / bb
        xs = [h * k for k in range(1, KP + 1)]
        us = []
        for xv in xs:
            u, rT = model_u(xv, wv)
            us.append(u)
            worstT = max(worstT, rT)
        # polynomial through (x_k, u_k), k = 1..KP: coefficients of 1, x by exact Lagrange/Vandermonde solve
        V = mpm.matrix([[xv ** i for i in range(KP)] for xv in xs])
        cfs = mpm.lu_solve(V, mpm.matrix(us))
        U0n, U1n = cfs[0], cfs[1]
        B = Bj(1, bb)
        e1 = abs(U0n - A0 / B) / abs(A0 / B)
        e2 = abs(bb ** 3 * U1n - phi2(bb)) / abs(phi2(bb))
        worst1 = max(worst1, e1); worst2 = max(worst2, e2)
        rows.append((float(bb), float(U0n), float(bb ** 3 * U1n), float(phi2(bb)), float(e1), float(e2)))
        print(f"N1  b = {mpm.nstr(bb, 6):>7}: U0 = {mpm.nstr(U0n, 15)} (A0/B rel.err {mpm.nstr(e1, 2)}),  b^3 U1 = {mpm.nstr(bb**3*U1n, 15)},"
              f"  phi_2 = {mpm.nstr(phi2(bb), 15)}  rel.err {mpm.nstr(e2, 2)}", flush=True)
    ok = worst1 < mpf(10) ** -25 and worst2 < mpf(10) ** -20 and worstT < mpf(10) ** -40
    print(f"N2  max rel. errors: (I1) {mpm.nstr(worst1, 3)}, (I2) {mpm.nstr(worst2, 3)} (extrapolation from x = 1e-5..8e-5, degree 7);"
          f" (T/x) definition vs Tt + EMx: {mpm.nstr(worstT, 3)}")
    OUT['N'] = dict(ok=bool(ok), I1_relerr=float(worst1), I2_relerr=float(worst2), Tx_relerr=float(worstT), rows=rows)
    print("PART N (numerical, independent implementation):", "CONSISTENT" if ok else "INCONSISTENT")
    return ok


def part_J():
    from mpmath import iv
    import mpmath
    from a02_jets import Z, ONE
    from a07_zoneI import u_jet
    from a03_special import kappa, PI
    from a05_model import A0
    from a11_slack import om_jet_xw
    T1C = -(iv.mpf(2) / 3 + 5 * PI / 72 + 1 / (3 * PI))
    def phi2(b):
        b = iv.mpf(b); B = b * kappa(2, b); B4 = b ** 3 * kappa(4, b) / 2
        return (-(PI / 2) * (1 + PI / 12) * b ** 3 / B + (PI / 2) * T1C * b ** 2 / B + (PI / 2) * A0 * b ** 3 / B ** 2
                - (A0 ** 2 / 2) * b ** 2 * B4 / B ** 3)
    from fractions import Fraction as Fr
    bs = [Fr(1) + Fr(k, 8) for k in range(0, 33)] + [Fr(5) + Fr(k, 2) for k in range(1, 31)] + [Fr(20 + 10 * k) for k in range(1, 99)]
    bad = []
    wmax1 = wmax2 = 0
    for bq in bs:
        b = iv.mpf(bq.numerator) / bq.denominator
        w = ONE / b
        U = u_jet(iv.mpf(0), w, 1, 0, ne=1)
        u0, u1 = U[(0, 0)], U[(1, 0)]
        B = b * kappa(2, b)
        t0 = A0 / B
        t1 = phi2(b) / b ** 3
        c0 = (u0.a <= t0.b) and (t0.a <= u0.b)          # the two enclosures intersect
        c1 = (u1.a <= t1.b) and (t1.a <= u1.b)
        wmax1 = max(wmax1, float(((u0.b - u0.a) / abs(t0.a)).b))          # display only
        wmax2 = max(wmax2, float(((u1.b - u1.a) / abs(t1.a)).b))
        if not (c0 and c1):
            bad.append(float(bq))
    # w = 0 (b = infinity): U1(0) = lim phi_2/b^3 = (pi/2)(-(1 + pi/12) + A0)  (B -> 1, B4 -> 1)
    U = u_jet(iv.mpf(0), iv.mpf(0), 1, 0, ne=1)
    lim = (PI / 2) * (-(1 + PI / 12) + A0)
    cinf = (U[(1, 0)].a <= lim.b) and (lim.a <= U[(1, 0)].b) and (U[(0, 0)].a <= A0.b) and (A0.a <= U[(0, 0)].b)
    if not cinf:
        bad.append('inf')
    # (W0) at the same points
    badw = []
    for bq in bs[::4]:
        b = iv.mpf(bq.numerator) / bq.denominator
        O = om_jet_xw(iv.mpf(0), ONE / b, 1, 0, 1, ne=1)
        tgt = -(1 - 2 / PI)
        if not ((O[(0, 0)].a <= tgt.b) and (tgt.a <= O[(0, 0)].b)):
            badw.append(float(bq))
    ok = not bad and not badw
    print(f"J1  interval jets at x = 0, {len(bs)} values of b in [1, 1000] and w = 0: enclosures of U0 and U1 intersect A0/B and"
          f" phi_2/b^3 at every point: {not bad} (bad: {bad[:5]});  max relative widths {wmax1:.1e}, {wmax2:.1e}")
    print(f"J2  omega(0, w) enclosures contain -(1 - 2/pi) at {len(bs[::4])} points: {not badw}")
    OUT['J'] = dict(ok=bool(ok), npts=len(bs) + 1, bad=bad, badw=badw)
    print("PART J (interval jets):", "CONSISTENT" if ok else "INCONSISTENT")
    return ok


if __name__ == '__main__':
    t0 = time.time()
    res = []
    if 'S' in PARTS:
        res.append(part_S())
    if 'N' in PARTS:
        res.append(part_N())
    if 'J' in PARTS:
        res.append(part_J())
    OUT['all_ok'] = all(res)
    print(f"IDENTITIES: {'ALL CONSISTENT' if all(res) else 'FAILURE'}  [{time.time()-t0:.0f}s]")
    if PARTS == {'S', 'N', 'J'}:
        json.dump(OUT, open('logs/alld/identities.json', 'w'), indent=1)
