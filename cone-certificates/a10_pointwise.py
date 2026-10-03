"""a10: POINTWISE LEMMA  |Phi_*(m) - Phi_e(m)| <= dmax eps^2 for all 1 <= m < d/2, d >= 2001 (CONE_ALLD_PROOF.md s.8;
complete derivation of every constant: RIGOR_ALLD.md section 5).
Scaled exact equation (u = t/(eps m^2), multiply (D_m) by (pi/2)/m):
   F(u) := sum_{j<=7} Ch_j u^j + Rs(u) - tauh_m = 0,   Rs(u) := (pi/2) [R7(m,t) - R7(d-m,t)]/m  (order-16 Gaussian + truncation),
   tauh_m = tauh_e(m) + Es,  Es = (pi/2) [Pot(m) - Pot(d-m)]/m  (Euler-Maclaurin defect potential).
Model: sum_{j<=4} Ch_j u_e^j = tauh_e  =>  F(u_e) = sum_{j=5..7} Ch_j u_e^j + Rs(u_e) - Es.
If inf_{0 <= u <= Uu} F'(u) >= Fp > 0, |F(u_e)| <= num eps^4 and du := (num/Fp) eps^4 <= min(u_e, Uu - u_e), a root u_* exists with
|u_* - u_e| <= du (IVT); |Phi_* - Phi_e| = eps m^2 du.  Near x = 1/2 (x >= 0.45) everything is divided by (1 - 2x) (halfshift).
Every box also certifies that the model root is the UNIQUE root in (0,1); the boxes cover {(x, eps): 0 <= eps <= 1/2001,
x = eps b, b >= 1, x <= 0.501} (checked by audit_alld.py), which is every point at which a06/a07/a09/a11 evaluate the model.
Part A computes all analytic constants in interval arithmetic (exact integers, no float literals as bounds)."""
import sys, time, json, math
from fractions import Fraction as Fr
import mpmath
from mpmath import iv
from a02_jets import Jet, Space, Z, ONE, ivq, ivfact, ivbinom, lo_str, hi_str, thin_frac, grid_boxes
from a03_special import gco, gtail_abs, PI, G_TAIL, A_TAIL
from a05_model import model_jets, krawczyk_root, A0, root_free, _poly_iv

EPS1 = iv.mpf(1) / 2001
E1 = EPS1.b                       # thin upper end of 1/2001 (>= 1/2001)
U = ivq('0.7')                    # all u used below satisfy u <= Uu <= U.a (checked per box)
DU_MARGIN = ivq('0.001')
SQ2PI = iv.sqrt(2 * PI)


def phi(a):
    return iv.exp(-a * a / 2) / SQ2PI


def G2j(n, a):
    """E[xi^n; |xi| >= a] <= 2 a^(n-1) phi(a)/(1 - (n-1)/a^2) (n >= 2 even, a^2 > n-1); n = 0: 2 phi(a)/a.  Decreasing in a
    on the range used (a^2 > n + 1).  Proof: I_n = int_a^oo x^n phi = a^(n-1) phi(a) + (n-1) I_(n-2), I_(n-2) <= I_n/a^2."""
    if n == 0:
        return 2 * phi(a) / a
    assert (a * a).a > n + 1
    return 2 * a ** (n - 1) * phi(a) / (1 - iv.mpf(n - 1) / (a * a))


# ---------------- Part A1: |g_r^(n)(y)| <= n! MA/r^n on [0,1] (Cauchy, r = 9/10; |z| <= 19/10 on the circles)
RC = ivq(Fr(9, 10))
ZM = ivq(Fr(19, 10)).b
MA_SUM = abs(gco[1]) * ZM + sum((abs(gco[i]) * ZM ** i for i in range(3, 2400, 2)), Z)       # gco: odd i <= 2399
# tail i >= 2401 (odd): |g_i| ZM^i <= 8.38 (ZM/2)^i/(i(i-1)), consecutive ratio <= (ZM/2)^2 < 1  (the old code skipped i = 2401)
MA_SUM = MA_SUM + gtail_abs(2401) * ZM ** 2401 / (1 - (ZM / 2) ** 2)
MA = ivq('4.0032')
assert MA_SUM.b < MA.a


def gder_bound(n):
    return ivfact(n) * MA / RC ** n


# ---------------- Part A2: Euler-Maclaurin defect  |delta| <= Dd eps^6 for eps <= 1/2001 (all terms increase with eps)
def em_defect_coeff(e=E1):
    s = gder_bound(8) / 2880 + (2 / iv.mpf(720)) * (gder_bound(8) / 12 + e ** 2 * gder_bound(10) / 240)
    for l in range(4, 40):
        s += (2 * e ** (2 * l - 8) / ivfact(2 * l)) * (gder_bound(2 * l) + e ** 2 * gder_bound(2 * l + 2) / 12
                                                     + e ** 4 * gder_bound(2 * l + 4) / 240)
    # l >= 40: term <= 2 MA e^(2l-8) r^(-2l) * 3 (2l+4)^4/... <= 2 MA e^-8 q^l (2l+4)^4 * 3, q = (e/r)^2; ratio <= 2q < 1/2
    q = (e / RC) ** 2
    assert (2 * q).b < ONE / 2
    s += 2 * (2 * MA * e ** -8 * q ** 40 * iv.mpf(84) ** 4 * 3)
    return s.b


Dd = em_defect_coeff()
Es_n = (PI / 8 * Dd).b                 # |Es| <= Es_n eps^4/m           (|Pot| <= Dd eps^4/8, two potentials)
# divided (half boxes): |Pot(m) - Pot(d-m)| <= (d-2m)(d-1) Dd eps^6  =>  |Es|/(1-2x) <= (pi/2) Dd eps^5/x


# ---------------- Part A3: Gaussian remainder constants (RIGOR_ALLD.md s.5.3).  e = eps <= E1, t = eps m^2 u, u <= U.
F14, F16 = ivfact(14), ivfact(16)
KT = 16 * ivfact(14) + 16 * ivfact(15) / ivq(Fr(5, 4)) + ivfact(15) + ivfact(16) / 4   # (c+1)^15 |kappa_16(c)| <= KT (c >= 1/4)
FR16 = A_TAIL * F14                    # |F_r^(n)| <= 16.76 (n-2)! d^(2-n)
def K2j(j):                            # (c+1)^(2j-1) |kappa_2j(c)| <= K2j (c >= 1)
    return iv.mpf(2 * j * math.factorial(2 * j - 2) + j * math.factorial(2 * j - 1) + math.factorial(2 * j - 1)) + ivfact(2 * j) / 4
NEAR16, NEAR14 = iv.mpf(2027025), iv.mpf(135135)          # 15!!, 13!!
a_rho = 1 / (2 * iv.sqrt(E1 * U.b))     # m/(2 sqrt t) >= a_rho  (near window |z| <= m/2)
a_L = 3 / (4 * iv.sqrt(E1 * U.b))       # (3m/4)/sqrt t >= a_L     (truncation |z| < L = 3m/4)
a_rho, a_L = a_rho.a, a_L.a
c813 = (1 - 10 * iv.sqrt(E1 * U.b)).a   # outer: c + z >= m (1 - 10 sqrt(eps U)) on the window |z| <= 10 sqrt t
assert (10 * iv.sqrt(E1 * U.b)).b < 0.75 and c813 > 0.8

# F1(d) = sup_(0,d) |F'| <= (4d/pi)(H_d + 1) + d SG1,  SG1 >= sum_i i |g_i|  (H_d <= log d + 1)
SG1 = abs(gco[1]) + sum((abs(gco[i]) * i for i in range(3, 400, 2)), Z) + G_TAIL * 2 ** -400   # tail <= 8.38 sum 2^-i/(i-1)
SG1 = SG1.b


def trunc_terms(e, outer=False):
    """exp-small contributions (in units of eps^4) of the truncation |Z| >= L (both sides), the boundary terms of d/dt H and
    (inner version) the far window m/2 < |Z| < 3m/4.  Each is p(1/e) exp(-c/e) with p polynomial/log: increasing in e on (0, E1]
    (RIGOR_ALLD.md s.5.3), so the value at e = E1 bounds all d >= 2001."""
    e = iv.mpf(e)
    aL = 3 / (4 * iv.sqrt(e * U.b))
    rs, drs = Z, Z
    for j in range(1, 8):           # value: sum_j |F^(2j)(c)| t^j E[xi^2j; |xi| >= a_L]/(2j)!, both sides, times pi/(2m)
        rs += 2 * (4 * K2j(j) + PI * A_TAIL * ivfact(2 * j - 2) * iv.mpf(2) ** (1 - 2 * j)) * U.b ** j * e ** (j - 5) \
              * G2j(2 * j, aL) / ivfact(2 * j)
    for j in range(0, 7):           # derivative: (1/2) sum_{j<=6} |F^(2j+2)(c)| t^j E[...]/(2j)!, times (pi/2) eps m, both sides
        drs += (2 * K2j(j + 1) + PI / 2 * A_TAIL * ivfact(2 * j) * iv.mpf(2) ** (-2 * j - 1)) * U.b ** j * e ** (j - 4) \
               * G2j(2 * j, aL) / ivfact(2 * j)
    d_ = 1 / e
    F1 = 4 * d_ / PI * (iv.log(d_) + 2) + d_ * SG1
    drs += (4 * PI / 3) * e ** -3 * F1 * (aL ** 3 + aL) * phi(aL)              # boundary terms of d/dt H
    if not outer:                   # far window m/2 < |Z| < 3m/4: sup|F^(16)| over c + z >= m/4
        ar = 1 / (2 * iv.sqrt(e * U.b))
        rs += e ** 3 * (4 * KT * iv.mpf(4) ** 15 + PI * FR16 * iv.mpf(2) ** -15) * U.b ** 8 * G2j(16, ar) / F16
        drs += e ** 3 * (2 * KT * iv.mpf(4) ** 15 + PI / 2 * FR16 * iv.mpf(2) ** -15) * U.b ** 7 * G2j(14, ar) / F14
    return rs.b, drs.b


TR_I, DTR_I = trunc_terms(E1)
TR_O, DTR_O = trunc_terms(E1, outer=True)
# inner (near window m/2):  |Rs| <= Rs_n eps^4,  |dRs/du| <= dRs_n eps^4
Rs_n = (E1 ** 3 * (4 * KT * iv.mpf(2) ** 15 + PI * FR16 * iv.mpf(2) ** -15) * NEAR16 * U.b ** 8 / F16 + TR_I).b
dRs_n = (E1 ** 3 * (2 * KT * iv.mpf(2) ** 15 + PI / 2 * FR16 * iv.mpf(2) ** -15) * NEAR14 * U.b ** 7 / F14 + DTR_I).b
# outer (near window 10 sqrt t, far window |xi| > 10 not exp-small: explicit G16(10), G14(10))
TEN = iv.mpf(10)
Rs_nO = (E1 ** 3 * ((4 * KT * c813 ** -15 + PI * FR16 * iv.mpf(2) ** -15) * NEAR16
                    + (4 * KT * iv.mpf(4) ** 15 + PI * FR16 * iv.mpf(2) ** -15) * G2j(16, TEN)) * U.b ** 8 / F16 + TR_O).b
dRs_nO = (E1 ** 3 * ((2 * KT * c813 ** -15 + PI / 2 * FR16 * iv.mpf(2) ** -15) * NEAR14
                     + (2 * KT * iv.mpf(4) ** 15 + PI / 2 * FR16 * iv.mpf(2) ** -15) * G2j(14, TEN)) * U.b ** 7 / F14 + DTR_O).b
print(f"Part A: MA_sum = {mpmath.nstr(MA_SUM.b, 8)} <= 4.0032;  Dd = {mpmath.nstr(Dd, 8)};  Es_n = {mpmath.nstr(Es_n, 6)};  c813 = {mpmath.nstr(c813, 8)}")
print(f"        inner |Rs|/eps^4 <= {mpmath.nstr(Rs_n, 6)}, |dRs/du|/eps^4 <= {mpmath.nstr(dRs_n, 6)}  (exp-small parts {mpmath.nstr(TR_I, 3)}, {mpmath.nstr(DTR_I, 3)})")
print(f"        outer |Rs|/eps^4 <= {mpmath.nstr(Rs_nO, 6)}, |dRs/du|/eps^4 <= {mpmath.nstr(dRs_nO, 6)}  (exp-small parts {mpmath.nstr(TR_O, 3)}, {mpmath.nstr(DTR_O, 3)})", flush=True)


# ---------------- Part B: box scans (value enclosures; raw coefficients Ch_j' = Ch_j/eps^(j-1))
def box_values(xbox, wbox, ebox, half=False):
    """enclosures over a box: raw Ch'_1..Ch'_7, tauh, u_e (Krawczyk with Ch_1..Ch_4).  half=True: divided by (1-2x)
    (xbox must then contain 1/2, mean-value form A(x)/(1-2x) = -A'(xi)/2)."""
    if half:
        assert xbox.a <= 0.5 <= xbox.b
        T = Space(1, 0, 1)
        X = Jet.var(T, 0, xbox)
        E = Jet.const(T, ebox)
        W = E * X.recip()
        V = E * (X * (-1) + 1).recip()
        Cr, th = model_jets(T, X, W, E, V, 400, J=7, raw=True)
        Cr = [c.c[1] * (-ONE / 2) for c in Cr]
        th = th.c[1] * (-ONE / 2)
    else:
        T = Space(0, 0, 0)
        X, E, W = Jet.const(T, xbox), Jet.const(T, ebox), Jet.const(T, wbox)
        V = E * (X * (-1) + 1).recip()
        Cr, th = model_jets(T, X, W, E, V, 400, J=7, raw=True)
        Cr, th = [c.c[0] for c in Cr], th.c[0]
    C = [Cr[j] * ebox ** j for j in range(7)]           # Ch_j = eps^(j-1) Ch'_j
    R = krawczyk_root(C[:4], th, th / C[0])
    return Cr, C, R, th


def check_box(xbox, wbox, ebox, scale, half=False, outer=False, xlo_for_es=None):
    """scale: |Phi_* - Phi_e|/eps^2 <= K * scale with du = K eps^4 (scale = b_hi^2 E1^3 inner, x_hi^2 E1 outer).
    Returns a dict of interval results; every decision is an interval comparison."""
    Cr, C, R, th = box_values(xbox, wbox, ebox, half)
    # (U1)-(U3): P_e increasing on [0,1], P_e(0) < 0 < P_e(1) at every point of the box -> exactly one root u_e in (0,1);
    # (U4): u_e lies in the Krawczyk enclosure R (R inside (0,1), or P_e certainly nonzero on [0,1] \ R)
    uniq = bool((C[0] - 2 * abs(C[1]) - 3 * abs(C[2]) - 4 * abs(C[3])).a > 0 and th.a > 0
                and (C[0] + C[1] + C[2] + C[3] - th).a > 0)
    encl = bool((R.a > 0 and R.b < 1) or root_free(C[:4], th, R))
    uniq = uniq and encl
    Ub = R.b
    num = sum((abs(Cr[j]) * E1 ** (j - 4) * Ub ** (j + 1) for j in (4, 5, 6)), Z)   # j index 4..6 = Ch_5..Ch_7 (|.|/eps^4)
    if half:
        num += Rs_nO / E1 + PI / 2 * Dd * E1 / iv.mpf(xlo_for_es)        # |Rs|/(1-2x) <= d |Rs|;  |Es|/(1-2x) <= (pi/2) Dd eps^4 e/x
        dR = dRs_nO / E1
    elif outer:
        num += Rs_nO + Es_n * E1 / iv.mpf(xlo_for_es)                     # |Es| <= (pi/8) Dd eps^4 (eps/x)
        dR = dRs_nO
    else:
        num += Rs_n + Es_n
        dR = dRs_n
    Uu = Ub + DU_MARGIN
    Fp = C[0]
    for j in range(1, 7):
        Fp = Fp - (j + 1) * abs(C[j]) * Uu ** j
    Fp = Fp - dR * E1 ** 4
    Fp_lo = Fp.a
    okF = bool(Fp_lo > 0)
    K = (num / Fp_lo).b if okF else iv.mpf(mpmath.inf)
    du = K * E1 ** 4
    # Lemma B uses F' >= Fp on [u_e - du - rho_u, u_e + du + rho_u] with rho_u <= 1e-6 (audit): this interval must lie in [0, Uu].
    # Upper end: du + 1e-6 <= DU_MARGIN/2.  Lower end: u_e > du + 1e-6, i.e. du + 1e-6 < R.a, or P_e < 0 on [0, du + 1e-6]
    # (P_e is increasing on [0,1] with its root at u_e).
    dw = du + ivq(Fr(1, 10 ** 6))
    pos = (bool(dw.b < R.a) or bool(_poly_iv(C[:4], th, iv.mpf([0, dw.b])).b < 0)) if okF else False
    ok_u = bool(Uu.b <= U.a and dw.b <= (DU_MARGIN / 2).a and pos)
    ratio = (K * scale).b if okF else iv.mpf(mpmath.inf)           # |Phi_* - Phi_e| <= ratio * eps^2
    return dict(ok=bool(uniq and okF and ok_u), uniq=uniq, K=K, Fp=Fp_lo, R=R, ratio=ratio)


def box_plan():
    """(kind, xbox, wbox, ebox, scale, half, outer, xlo) for every box; the union covers the domain described in the docstring.
    All endpoints are exact rationals enclosed outward."""
    e = iv.mpf([0, E1])
    plan = []
    bgrid = grid_boxes('1', '2', 20) + grid_boxes('2', '10', 32) + grid_boxes('10', '30', 10)
    for (bl, bh) in bgrid:                 # inner b-boxes: b in [bl, bh], x <= E1 b
        plan.append(('b', iv.mpf([0, (E1 * bh).b]), iv.mpf([(1 / iv.mpf(bh)).a, (1 / iv.mpf(bl)).b]), e,
                     (iv.mpf(bh) ** 2 * E1 ** 3).b, False, False, None, (bl, bh)))
    for (wl, wh) in [('0', '0.001'), ('0.001', '1/300'), ('1/300', '0.01'), ('0.01', '1/30')]:   # b >= 30, x <= 0.015
        wb = iv.mpf([ivq(wl).a, ivq(wh).b])
        X015 = ivq('0.015').b
        plan.append(('w', iv.mpf([0, X015]), wb, e, (X015 ** 2 * E1).b, False, False, None, (wb.a, wb.b)))
    xgrid = grid_boxes('0.015', '0.45', 87)
    for (xl, xh) in xgrid:                 # outer x-boxes (b = x/eps >= 30), w = eps/x in [0, E1/xl]
        plan.append(('x', iv.mpf([xl, xh]), iv.mpf([0, (E1 / xl).b]), e, (xh ** 2 * E1).b, False, True, xl, (xl, xh)))
    for (xl, xh) in grid_boxes('0.45', '0.5', 5) + [(ivq('0.49').a, ivq('0.501').b)]:   # half boxes (divided by 1 - 2x)
        xr = iv.mpf([xl, max(xh, iv.mpf(0.5).b)])
        plan.append(('x*', xr, iv.mpf([0, (E1 / xl).b]), e, (xh ** 2 * E1).b, True, True, xl, (xl, xh)))
    return plan


if __name__ == '__main__':
    t0 = time.time()
    recs = []
    worst = None
    allok = True
    umax_b1 = None
    for (kind, xb, wb, eb, scale, half, outer, xl, span) in box_plan():
        r = check_box(xb, wb, eb, scale, half, outer, xl)
        allok &= r['ok']
        if worst is None or r['ratio'] > worst[0]:
            worst = (r['ratio'], kind, float(span[0]), float(span[1]))
        if kind == 'b' and thin_frac(span[0]) == 1:
            umax_b1 = r['R'].b
        recs.append(dict(kind=kind, lo=str(thin_frac(span[0])), hi=str(thin_frac(span[1])), ok=r['ok'], uniq=r['uniq'],
                         xr=[lo_str(xb), hi_str(xb)], wr=[lo_str(wb), hi_str(wb)], er=[lo_str(eb), hi_str(eb)],
                         Fp=lo_str(r['Fp']), R=[lo_str(r['R']), hi_str(r['R'])], ratio=hi_str(r['ratio']),
                         Fp_f=float(r['Fp']), ratio_f=float(r['ratio'])))
        if not r['ok']:
            print("FAIL", kind, float(span[0]), float(span[1]), r)
    print(f"boxes {len(recs)}: all ok = {allok};  worst ratio |Phi_*-Phi_e|/eps^2 <= {float(worst[0]):.4e} at {worst[1:]};"
          f"  min Fp = {min(r['Fp_f'] for r in recs):.5f}  [{time.time()-t0:.0f}s]")
    json.dump(dict(ok=bool(allok), dmax_rel=hi_str(worst[0]), dmax_rel_f=float(worst[0]), Dd=hi_str(Dd), Es_n=hi_str(Es_n),
                   Rs_n=hi_str(Rs_n), dRs_n=hi_str(dRs_n), Rs_nO=hi_str(Rs_nO), dRs_nO=hi_str(dRs_nO), U=str(Fr('0.7')),
                   du_margin='1/1000', u_max_b1=hi_str(umax_b1), eps_hi=hi_str(EPS1), iv_prec=iv.prec, boxes=recs),
              open('logs/alld/pointwise.json', 'w'), indent=0)
