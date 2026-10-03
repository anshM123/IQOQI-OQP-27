"""a11: SLACK certificate (CONE_ALLD_PROOF.md s.9).  W_e(b) := Dlt_e(b) - G_4(b, Phi_e(b)) = b omega(x, w),
   omega = Tg + sum_k aEM_k eps^(2k-1) [g^(2k)(x)/x - g^(2k)(1)] - (2/pi) sum_{j<=4} Ch+_j u_e^j,
   Ch+_j = eps^(j-1) { k_j B_2j(b) + (pi/2) x^(2j-1) Gamma^(2j)(x)/(2^j j!) }   (m-side parts; Ch_j = Ch+_j(x) - Ch+_j(1-x) side).
omega(0, w) = -(1 - 2/pi) exactly (Tg(0,0) = 0, Ch+_1 = B, u = A0/B), so with omega = omega0 + x omega1(w) + x^2 rho2:
   Delta^2 W_e(m)/eps = int L_W(x_s, w_s) M_2(s) ds  (m >= 2),  L_W = (1-D)(2-D) omega1(w) + x (th+2)(th+3) rho2  (inner, D = w d_w),
   Delta^2 W_e(m)/eps = int Q_W(x_s, eps) M_2(s) ds,  Q_W = d_x^2 [x omega] at fixed eps  (outer),
   m = 1:  Delta^2 W_e(1)/eps = -2 omega1(1) + 4 omega1(1/2) + eps [-2 rho2(eps,1) + 8 rho2(2 eps,1/2)].
Usage: python a11_slack.py inner b|w lo hi nb log  |  python a11_slack.py outer xlo xhi nb log  |  python a11_slack.py m1"""
import sys, time, json, math
import mpmath
from mpmath import iv
from a02_jets import Jet, Space, Z, ONE, compose2, ivq, ivbinom, ivff, grid_boxes, lo_str, hi_str, thin_frac
from a03_special import PI, binet_w, binet_near
from a04_regular import poch_sums_g, em_g_over_x, AEM
from a05_model import model_jets, implicit_root_jet, kj, is_const, J_ORDER, A0

EPS1 = iv.mpf(1) / 2001
XA = ivq('0.013')


def omega_jet(T, X, W, E, V, Nc, ne=None, half=False, xbox=None, ebox=None):
    """u_e and omega as jets in T.  half=True (box containing x = 1/2, outer 1-variable/2-variable (x, eps) spaces only):
    the antisymmetric model coefficients are computed one x-order higher and divided by (1-2x) via halfshift."""
    if half:
        from a06_zoneO import halfshift2
        Tb = Space(T.n0 + 1, T.n1, T.T + 1)
        Xb = Jet.var(Tb, 0, xbox)
        Eb = Jet.var(Tb, 1, ebox) if T.n1 else Jet.const(Tb, ebox)
        Cb, tb = model_jets(Tb, Xb, Eb * Xb.recip(), Eb, Eb * (Xb * (-1) + 1).recip(), Nc)
        C = [halfshift2(c, T) for c in Cb]
        tauh = halfshift2(tb, T)
    else:
        C, tauh = model_jets(T, X, W, E, V, Nc, ne=ne)
    n = T.T
    J = J_ORDER
    ne = n if ne is None else ne
    xb, eb = X.c[0], E.c[0]
    if is_const(E):
        S1 = Space(n + 2 * J, 0, n + 2 * J)
        Sg, Tg = poch_sums_g(S1, xb, eb, Nc)
        G = [X.compose1([Sg.c[2 * j + k] * ivff(2 * j + k, 2 * j) for k in range(n + 1)])
             for j in range(1, J + 1)]
        Tgc = X.compose1([Tg.c[k] for k in range(n + 1)])
    else:
        S2 = Space(n + 2 * J, ne, n + 2 * J)
        Sg, Tg = poch_sums_g(S2, xb, eb, Nc)
        SG = Space(n, ne, n)
        G = [compose2(Jet(SG, [Sg[(a + 2 * j, c)] * ivff(a + 2 * j, 2 * j) for (a, c) in SG.idx]), X, E)
             for j in range(1, J + 1)]
        Tgc = compose2(Jet(SG, [Tg[(a, c)] for (a, c) in SG.idx]), X, E)
    S1x = Space(n, 0, n)
    em = em_g_over_x(S1x, Jet.var(S1x, 0, xb))
    EMg = {k: X.compose1(em[k].c) for k in (1, 2)}
    u = implicit_root_jet(C, tauh)
    s = Jet(T)
    up = Jet.const(T, ONE)
    for j in range(1, J + 1):
        up = up * u
        Cp = (binet_w(j, W) * kj(j) + (X ** (2 * j - 1)) * G[j - 1] * (PI / 2 / iv.mpf(2 ** j * math.factorial(j)))) * (E ** (j - 1))
        s = s + Cp * up
    om = Tgc + EMg[1] * E * AEM[1] + EMg[2] * (E ** 3) * AEM[2] - s * (2 / PI)
    return u, om


# ------------------------------------------------------------------ outer: Q_W = d_x^2 [x omega]
HALF_THR = 0.4201                  # enlarge the remainder box to contain 1/2 when x_hi > 0.4201 (a numerical choice; any value is rigorous)


def yW(xbox, ebox, nx, ne, Nc):
    xbox, ebox = iv.mpf(xbox), iv.mpf(ebox)
    half = xbox.a <= 0.5 <= xbox.b
    T = Space(nx, ne, nx + ne)
    X = Jet.var(T, 0, xbox)
    E = Jet.var(T, 1, ebox) if ne else Jet.const(T, ebox)
    W = E * X.recip()
    V = E * (X * (-1) + 1).recip()
    u, om = omega_jet(T, X, W, E, V, Nc, half=half, xbox=xbox, ebox=ebox)
    return X * om


def qW_outer(xlo, xhi, elo=0, ehi=None, K=3):
    ehi = EPS1.b if ehi is None else ehi
    xb, eb = iv.mpf([xlo, xhi]), iv.mpf([elo, ehi])
    xc, ec = iv.mpf(xb.mid), iv.mpf(eb.mid)
    if xb.a <= 0.5 <= xb.b:
        xc = iv.mpf(0.5)
    xr = iv.mpf([xb.a, max(xb.b, mpmath.mpf(0.5))]) if xb.b > HALF_THR else xb
    Nc = int(80 + 700 * float(xr.b))
    ya = yW(xc, ec, 2 + K - 1, 1, Nc)
    yb = yW(xr, ec, 2 + K, 1, Nc)
    yc = yW(xr, eb, 2, 2, Nc)
    hx, he = xb - xc, eb - ec
    q = Z
    for k in (0, 1):
        t = Z
        for i in range(K):
            t += ivbinom(2 + i, i) * ya[(2 + i, k)] * hx ** i
        t += ivbinom(2 + K, K) * yb[(2 + K, k)] * hx ** K
        q += t * he ** k
    q += yc[(2, 2)] * he ** 2
    return q * 2


def qW_outer_split(xlo, xhi):
    from a06_zoneO import eps_pieces
    lo = hi = None
    for (e0, e1) in eps_pieces(float(xlo), EPS1.b):
        q = qW_outer(xlo, xhi, e0, e1)
        lo = q.a if lo is None else min(lo, q.a)
        hi = q.b if hi is None else max(hi, q.b)
    return iv.mpf([lo, hi])


# ------------------------------------------------------------------ inner: L_W = (1-D)(2-D) omega1 + x (th+2)(th+3) rho2
def om_jet_xw(xbox, wbox, nx, nw, tot, Nc=120, ne=None):
    T = Space(nx, nw, tot)
    X = Jet.var(T, 0, iv.mpf(xbox)); W = Jet.var(T, 1, iv.mpf(wbox)); E = X * W
    V = E * (X * (-1) + 1).recip()
    return omega_jet(T, X, W, E, V, Nc, ne=ne)[1]


def term1_W(wlo, whi, K=3):
    wb = iv.mpf([wlo, whi]); wc = iv.mpf(wb.mid); h = wb - wc
    LW = {0: 2, 1: -2, 2: 1}                       # (1-D)(2-D) g = 2g - 2w g' + w^2 g''
    def lamjet(wbox, order):
        O = om_jet_xw(iv.mpf(0), wbox, 1, 2 + order, 3 + order, ne=1)
        g = [O[(1, l)] for l in range(2 + order + 1)]
        out = []
        for k in range(order + 1):
            s = Z
            for l, cl in LW.items():
                for t in range(min(l, k) + 1):
                    gk = g[l + k - t] * iv.mpf(math.comb(l + k - t, l) * math.factorial(l))
                    s += cl * ivbinom(l, t) * wbox ** (l - t) * gk
            out.append(s)
        return out, O
    cen, Oc = lamjet(wc, K - 1)
    box, Ob = lamjet(wb, K)
    return sum((cen[k] * h ** k for k in range(K)), Z) + box[K] * h ** K, Oc


def term2_W(wlo, whi, Nc=120):
    from a07_zoneI import theta_coeffs
    wb = iv.mpf([wlo, whi])
    x1 = min(XA.b, (EPS1 / wb.a).b) if wb.a > 0 else XA.b
    xb = iv.mpf([0, x1])
    O = om_jet_xw(xb, wb, 4, 2, 4, Nc)
    s = Z
    for (i, l), c in theta_coeffs([2, 3]).items():
        s += c * xb ** i * wb ** l * O[(2 + i, l)] * iv.mpf(math.factorial(2 + i) * math.factorial(l))
    return xb * s / 2, x1


def qW_inner_w(wlo, whi):
    t1, Oc = term1_W(wlo, whi)
    t2, x1 = term2_W(wlo, whi)
    return t1 + t2, t1, t2, x1


def slack_m1():
    """Delta^2 W_e(1)/eps >= -2 omega1(1) + 4 omega1(1/2) - eps1 [2 |rho2(.,1)| + 8 |rho2(.,1/2)|], rho2 in (1/2) range d_x^2 omega."""
    val = Z
    for (w, cw, cr) in ((ONE, -2, -2), (ONE / 2, 4, 8)):
        O0 = om_jet_xw(iv.mpf(0), w, 1, 0, 1, ne=1)
        x1 = (EPS1 / w).b
        Ob = om_jet_xw(iv.mpf([0, x1]), w, 2, 0, 2)
        rho2 = Ob[(2, 0)]                              # (1/2) d_x^2 omega = omega[2,0]
        val += cw * O0[(1, 0)] + iv.mpf([-1, 1]) * abs(cr) * EPS1.b * abs(rho2).b
        print(f"   w={float(w.mid)}: omega0 = {mpmath.nstr(O0[(0,0)].mid, 12)} (exact -(1-2/pi) = {mpmath.nstr(-(1 - 2 / PI).mid, 12)}), omega1 = {mpmath.nstr(O0[(1,0)].mid, 10)}, |rho2| <= {mpmath.nstr(abs(rho2).b, 4)}")
    return val


if __name__ == '__main__':
    mode = sys.argv[1]
    t0 = time.time()
    if mode == 'm1':
        v = slack_m1()
        print(f"Delta^2 W_e(1)/eps in [{float(v.a):.5f}, {float(v.b):.5f}]  [{time.time()-t0:.0f}s]")
        json.dump(dict(m1_lo=lo_str(v), m1_hi=hi_str(v), m1_lo_f=float(v.a), eps_hi=hi_str(EPS1)),
                  open('logs/alld/slack_m1.json', 'w'), indent=0)
        sys.exit()
    kind, lo, hi, nb = sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
    log = sys.argv[6] if len(sys.argv) > 6 else None
    res = []; qmin = None
    for (a, b) in grid_boxes(lo, hi, nb):
        x1s = None
        if mode == 'outer':
            q = qW_outer_split(a, b); extra = ''
        else:
            wl, wh = (ONE / iv.mpf(b), ONE / iv.mpf(a)) if kind == 'b' else (iv.mpf(a), iv.mpf(b))
            q, t1, t2, x1 = qW_inner_w(wl.a, wh.b)
            x1s = str(thin_frac(x1))
            extra = f" (term1 [{float(t1.a):.4f},{float(t1.b):.4f}], term2 +-{float(abs(t2).b):.2e})"
        qmin = q.a if qmin is None or q.a < qmin else qmin
        res.append(dict(lo=str(thin_frac(a)), hi=str(thin_frac(b)), qlo=lo_str(q), qhi=hi_str(q), qlo_f=float(q.a), x1=x1s))
        print(f"{mode} {kind} [{float(a):.6g},{float(b):.6g}]: slack density in [{float(q.a):.4f}, {float(q.b):.4f}]{extra} [{time.time()-t0:.0f}s]", flush=True)
        if log:
            json.dump(dict(mode=mode, kind=kind, lo=lo, hi=hi, nb=nb, XA=hi_str(XA), eps_hi=hi_str(EPS1), iv_prec=iv.prec,
                           boxes=res, minq=lo_str(qmin), complete=len(res) == nb), open(log, 'w'), indent=0)
    print("min lower =", float(qmin), " exact:", lo_str(qmin))
