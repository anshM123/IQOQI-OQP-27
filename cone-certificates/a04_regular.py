"""a04: regular (analytic) parts of the MODEL as interval jets in (x, eps)  (CONE_ALLD_PROOF.md section 2).
MODEL (exact functions):  P_n = prod_{k<n} r_k, r_k = (x + k eps)/(1 + k eps)  (= E X^n, X ~ Beta(x/eps, (1-x)/eps));
  Qt_n = (x^n - P_n)/(eps x)  (Qt_0 = Qt_1 = 0, Qt_{n+1} = Qt_n r_n - x^(n-1) n (1-x)/(1 + n eps));
  S  = sum_n (g_n - a_n) P_n = Gamma(x) - Gamma(1-x),   Tt = sum_n (g_n - a_n) Qt_n;
  EMx = sum_{k=1,2} aEM_k eps^(2k-1) [g^(2k)(x)/x - (g^(2k)(1-x) - g^(2k)(1))/x - 2 g^(2k)(1)],  aEM = (-1/12, 1/240);
  tauh_e = (pi/2)(Tt + EMx).
Jets: terms n <= Nc exactly; tail n > Nc by  |d_x^a d_eps^c P_n| <= n^(a+c) (n+c)^c prod_{k=a+c}^{n-1} R_k  (Leibniz count;
R_k = sup r_k = (X + k E)/(1 + k E) on [0,X]x[0,E]), Qt_n = -int int d_x d_eps P_n(t x, s eps) ds dt, |g_n - a_n| <= 34/n^2 for large n,
and prod_{k=N2}^{n-1} R_k <= ((1 + N2 E)/(1 + n E))^((1-X)/E) beyond N2."""
import mpmath
from mpmath import iv
from a02_jets import Jet, Space, Z, ONE, ivq, ivfact, ivff
from a03_special import gco, acoef, NA, a_bound, gtail_abs, PI, G_TAIL, A_TAIL

AEM = {1: -iv.mpf(1) / 12, 2: iv.mpf(1) / 240}


def gma(n):
    gn = gco.get(n, Z) if n % 2 == 1 else Z
    if n <= NA:
        return gn - acoef[n]
    ab = a_bound(n).b
    return gn + iv.mpf([-ab, ab])


def gma_abs(n):
    gn = (abs(gco[n]).b if n in gco else gtail_abs(n).b) if n % 2 == 1 else 0
    an = abs(acoef[n]).b if n <= NA else a_bound(n).b
    return iv.mpf(gn) + an


def _addtail(J, tail, rx, re):
    for k, (i, j) in enumerate(J.S.idx):
        sc = rx ** (-i) * (re ** (-j) if j else 1)
        J.c[k] = J.c[k] + iv.mpf([-1, 1]) * (tail * sc).b


def poch_tail(X, E, Nc, idx, N2extra=200):
    # far tail n > N2 uses |g_n - a_n| <= |g_n| + |a_n| <= (8.38/2^n + 16.76)/(n(n-1)) <= 34/n^2 (n >= 200; checked below)
    """dict (a,c) -> upper bounds (tS, tT) for the normalized coefficient (a,c) of the tails n > Nc of S and Tt."""
    X, E = iv.mpf(X).b, iv.mpf(E).b
    smax = max(a + c for (a, c) in idx) + 2
    N2 = Nc + N2extra
    assert N2 >= 200 and ((G_TAIL / iv.mpf(2) ** 200 + A_TAIL) * 200 * 200 / (200 * 199)).b < 34
    R = [(X + k * E) / (1 + k * E) for k in range(N2 + 1)]
    PR = {}                                        # PR[s][n] = prod_{k=s}^{n-1} R_k  (no divisions)
    for s0 in range(smax + 1):
        row = [ONE] * (N2 + 1)
        for n in range(s0 + 1, N2 + 1):
            row[n] = row[n - 1] * R[n - 1]
        PR[s0] = row
    def prodR(s, n):
        return PR[s][n] if n > s else ONE
    def B(a, c, n):
        return iv.mpf(n) ** (a + c) * iv.mpf(n + c) ** c * prodR(min(a + c, n), n)
    p = (1 - X) / E if E != 0 else None
    out = {}
    for (a, c) in idx:
        fa = ivfact(a) * ivfact(c)
        tS, tT = Z, Z
        for n in range(Nc + 1, N2 + 1):
            w = gma_abs(n)
            tS += w * B(a, c, n)
            tT += w * B(a + 1, c + 1, n) / ((a + 1) * (c + 1))
        for (aa, cc, sc, acc) in ((a, c, ONE, 'S'), (a + 1, c + 1, ONE / ((a + 1) * (c + 1)), 'T')):
            # sum_{n>N2} (34/n^2) n^(aa+cc) (n+cc)^cc prod R <= 34 2^cc prodR(aa+cc, N2) sum_{n>N2} n^q (...), q = aa + 2cc - 2;
            # for q < 0 use n^q <= 1 (q := 0): the bound n^q <= ((1 + nE)/E)^q used below holds only for q >= 0.
            q = max(aa + 2 * cc - 2, 0)
            if E == 0:      # R_k = X: geometric tail, ratio <= X (1 + 1/N2)^q < 1
                ratio = X * (1 + iv.mpf(1) / N2) ** q
                assert ratio.b < 1
                far = 34 * iv.mpf(2) ** cc * prodR(aa + cc, N2) * iv.mpf(N2) ** q * ratio / (1 - ratio) * sc
            else:
                assert p.a > q + 1
                far = 34 * iv.mpf(2) ** cc * prodR(aa + cc, N2) * E ** (-q - 1) * (1 + N2 * E) ** (q + 1) / (p - q - 1) * sc
            if acc == 'S':
                tS += far
            else:
                tT += far
        out[(a, c)] = (tS / fa, tT / fa)
    return out


def poch_sums(S2, xbox, ebox, Nc):
    """(S, Tt) as jets in S2 (variables x, eps; if S2.n1 == 0, eps is the constant interval ebox), tails included."""
    twod = S2.n1 > 0
    X = Jet.var(S2, 0, xbox)
    E = Jet.var(S2, 1, ebox) if twod else Jet.const(S2, ebox)
    P = Jet.const(S2, ONE)
    Qt = Jet(S2)
    Xp = Jet.const(S2, ONE)
    Sj = P * gma(0)
    Tj = Jet(S2)
    for n in range(0, Nc):
        rinv = (E * n + 1).recip()
        r = (X + E * n) * rinv
        if n >= 1:
            Qt = Qt * r - Xp * (X * (-1) + 1) * rinv * n
            Xp = Xp * X
        P = P * r
        c = gma(n + 1)
        Sj = Sj + P * c
        Tj = Tj + Qt * c
    idx = S2.idx if twod else [(i, 0) for (i, j) in S2.idx]
    tails = poch_tail(iv.mpf(xbox).b, iv.mpf(ebox).b, Nc, idx)
    for k, ij in enumerate(S2.idx):
        tS, tT = tails[ij if twod else (ij[0], 0)]
        Sj.c[k] = Sj.c[k] + iv.mpf([-1, 1]) * tS.b
        Tj.c[k] = Tj.c[k] + iv.mpf([-1, 1]) * tT.b
    return Sj, Tj


def _gx_part(S1, X, k, y, rho):
    """jet of g^(2k)(x)/x = sum_{i odd >= 2k+1} g_i (i)_2k x^(i-2k-1): terms i <= 201 exactly; the tail i >= 203 by its majorant
    M(y) = sum |g_i| (i)_2k y^(i-2k-1) (y = x_max + rho; normalized l-th derivative <= M(y)/rho^l, see _addtail), with the
    terms i < 2001 summed and i >= 2001 bounded geometrically (term ratio <= r < 1)."""
    A = Jet(S1)
    for i in range(201, 2 * k, -1):
        if i % 2 == 1:
            A = A * X + gco[i] * ivff(i, 2 * k)
        else:
            A = A * X
    term = lambda i: gtail_abs(i) * ivff(i, 2 * k) * y ** (i - 2 * k - 1)
    tail = sum((term(i) for i in range(203, 2001, 2)), Z)
    # ratio of consecutive odd terms i -> i+2 (i >= 2001): (1/4) y^2 (i+2)(i+1) i (i-1)/((i+2-2k)(i+1-2k)(i+2)(i+1)) <= r
    r = y ** 2 / 4 * (iv.mpf(2001) * 2000 / ((2001 - 2 * k) * (2000 - 2 * k)))
    assert r.b < 1
    tail = tail + term(2001) / (1 - r)
    _addtail(A, tail, rho, ONE)
    return A


def _g1mx_part(S1, X, k, y, rho):
    """jet of (g^(2k)(1-x) - g^(2k)(1))/x = sum_{n >= 2k+1} a_n (n)_2k x^(n-2k-1): n <= NA exactly, tail with |a_n| <= 16.76/(n(n-1))
    (terms NA < n < 3000 summed, n >= 3000 geometric with ratio y (n+1)/(n+1-2k) <= r < 1)."""
    Bj = Jet(S1)
    for n in range(NA, 2 * k, -1):
        Bj = Bj * X + acoef[n] * ivff(n, 2 * k)
    term = lambda n: a_bound(n) * ivff(n, 2 * k) * y ** (n - 2 * k - 1)
    tail = sum((term(n) for n in range(NA + 1, 3000)), Z)
    r = y * iv.mpf(3001) / (3001 - 2 * k)
    assert r.b < 1
    tail = tail + term(3000) / (1 - r)
    _addtail(Bj, tail, rho, ONE)
    return Bj


def _em_radius(X):
    xm = X.c[0].b
    rho = iv.mpf(min(0.1, (1 - float(xm)) / 4))      # any rho > 0 with x_max + rho < 1 is admissible (exact binary value)
    y = xm + rho
    assert y.b < 1
    return y, rho


def em_over_x(S1, X):
    """EM bracket parts as 1-D x-jets (functions of x only): returns {k: [g^(2k)(x)/x - (g^(2k)(1-x) - g^(2k)(1))/x - 2 g^(2k)(1)]}."""
    y, rho = _em_radius(X)
    out = {}
    for k in (1, 2):
        A = _gx_part(S1, X, k, y, rho)
        Bj = _g1mx_part(S1, X, k, y, rho)
        G1 = acoef[2 * k] * ivfact(2 * k)
        out[k] = A - Bj - G1 * 2
    return out


def poch_sums_g(S2, xbox, ebox, Nc):
    """m-side sums  Sg = sum_n g_n P_n = Gamma(x, eps),  Tg = sum_n g_n Qt_n  (for the slack W = b omega); tails as in poch_sums
    (|g_n| <= |g_n - a_n| + |a_n| is covered by the same majorant weights gma_abs)."""
    twod = S2.n1 > 0
    X = Jet.var(S2, 0, xbox)
    E = Jet.var(S2, 1, ebox) if twod else Jet.const(S2, ebox)
    P = Jet.const(S2, ONE)
    Qt = Jet(S2)
    Xp = Jet.const(S2, ONE)
    Sj = Jet(S2)
    Tj = Jet(S2)
    for n in range(0, Nc):
        rinv = (E * n + 1).recip()
        r = (X + E * n) * rinv
        if n >= 1:
            Qt = Qt * r - Xp * (X * (-1) + 1) * rinv * n
            Xp = Xp * X
        P = P * r
        if (n + 1) % 2 == 1:
            c = gco[n + 1]
            Sj = Sj + P * c
            Tj = Tj + Qt * c
    idx = S2.idx if twod else [(i, 0) for (i, j) in S2.idx]
    tails = poch_tail(iv.mpf(xbox).b, iv.mpf(ebox).b, Nc, idx)
    for k, ij in enumerate(S2.idx):
        tS, tT = tails[ij if twod else (ij[0], 0)]
        Sj.c[k] = Sj.c[k] + iv.mpf([-1, 1]) * tS.b
        Tj.c[k] = Tj.c[k] + iv.mpf([-1, 1]) * tT.b
    return Sj, Tj


def em_g_over_x(S1, X):
    """m-side EM parts: {k: g^(2k)(x)/x - g^(2k)(1)}  (Dlt_e/b = Tg + sum_k aEM_k eps^(2k-1) [g^(2k)(x)/x - g^(2k)(1)])."""
    y, rho = _em_radius(X)
    out = {}
    for k in (1, 2):
        A = _gx_part(S1, X, k, y, rho)
        G1 = acoef[2 * k] * ivfact(2 * k)
        out[k] = A - G1
    return out
