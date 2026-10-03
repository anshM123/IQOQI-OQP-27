"""a07: INNER ZONE certificate (CONE_ALLD_PROOF.md section 6).  Variables (x, w), w = 1/b, eps = x w; u_e(x, w) the model root.
Taylor in x at fixed w:  u_e = U0(w) + x U1(w) + x^2 U2(w) + x^3 R3(x,w),  R3 = int_0^1 (1-s)^2/2 d_x^3 u_e(sx, w) ds.
  eps b^2 U0 = eps phi_1(b), eps b^2 x U1 = eps^2 phi_2(b) (exact, QD2-L10), and with R2 = U2 + x R3,
  d_b^4 [b^4 R2] = Lambda(R2) = lam2(U2)(w) + x Lambda'(R3),  Lambda = (th+1)..(th+4), Lambda' = (th+2)..(th+5), th = x d_x - w d_w,
  lam2 = (1-D)(2-D)(3-D)(4-D), D = w d_w (th acting on functions of w alone).
So  D_B(m) = eps^2 A_2(m) + eps^3 int Lambda(R2)(x_s, w_s) M_4(s) ds  (+ F_A(d-b) term), for stencils in [1, inf) with x_s <= x_A.
Enclosure per w-box [w_lo, w_hi] (x in [0, x1], x1 = min(x_A, eps1/w_lo)):
  term1 = lam2(U2) on the w-box by an order-K Taylor model in w at thin x = 0;
  term2 = [0, x1] * (1/6) * range(Lambda'(d_x^3 u_e)) over the box (naive).
Usage: python a07_zoneI.py b_lo b_hi nbox [log]   (b-boxes; w = 1/b)"""
import sys, time, json, math
from functools import lru_cache
import mpmath
from mpmath import iv
from a02_jets import Jet, Space, Z, ONE, ivq, ivbinom, ivfact, grid_boxes, lo_str, hi_str, thin_frac
from a05_model import model_jets, implicit_root_jet, A0

EPS1 = iv.mpf(1) / 2001
XA = ivq('0.013')                 # inner zone: x <= XA.b (>= 13/1000 exactly)
K_TM = 3


@lru_cache(None)
def stirling2(n, k):
    """Stirling numbers of the second kind (exact integer recursion)."""
    if n == k:
        return 1
    if n <= 0 or k <= 0 or k > n:
        return 0
    return k * stirling2(n - 1, k) + stirling2(n - 1, k - 1)


def theta_coeffs(roots):
    """p(th) = prod (th + r), th = Dx - Dw  ->  {(i,l): c_il} with p(th) = sum c_il x^i w^l d_x^i d_w^l."""
    p = [1]
    for r in roots:
        q = [0] * (len(p) + 1)
        for k, v in enumerate(p):
            q[k + 1] += v
            q[k] += r * v
        p = q
    out = {}
    for k, pk in enumerate(p):
        for a in range(k + 1):
            b = k - a
            for i in range(a + 1):
                for l in range(b + 1):
                    v = pk * math.comb(k, a) * (-1) ** b * stirling2(a, i) * stirling2(b, l)
                    if v:
                        out[(i, l)] = out.get((i, l), 0) + v
    return {k: v for k, v in out.items() if v}


LAM = theta_coeffs([1, 2, 3, 4])          # Lambda
LAMP = theta_coeffs([2, 3, 4, 5])         # Lambda'
LAM2 = {l: v for (i, l), v in LAM.items() if i == 0}     # lam2 on functions of w only


def u_jet(xbox, wbox, nx, nw, Nc=120, ne=None, tot=None):
    T = Space(nx, nw, nx + nw if tot is None else tot)
    X = Jet.var(T, 0, iv.mpf(xbox))
    W = Jet.var(T, 1, iv.mpf(wbox))
    E = X * W
    V = E * (X * (-1) + 1).recip()
    C, tauh = model_jets(T, X, W, E, V, Nc, ne=ne)
    return implicit_root_jet(C, tauh)


def term1(wlo, whi, K=K_TM):
    """enclosure of lam2(U2)(w) over [wlo, whi] (U2 = coefficient (2,0) at x = 0)."""
    wb = iv.mpf([wlo, whi]); wc = iv.mpf(wb.mid); h = wb - wc
    def lamjet(wbox, order):
        U = u_jet(iv.mpf(0), wbox, 2, 4 + order, ne=2)
        g = [U[(2, l)] for l in range(4 + order + 1)]          # normalized w-coefficients of U2
        # [lam2 g]_k = sum_l c_l [w^l g^(l)]_k ;  g^(l) normalized coeffs: C(l+k', l) l! g_{l+k'}; w^l g^(l) as jet around wbox
        out = []
        for k in range(order + 1):
            s = Z
            for l, cl in LAM2.items():
                # coefficient k of w^l * G_l(w), G_l = g^(l): sum_{t} [w^l]_t [G_l]_{k-t}, [w^l]_t = C(l,t) w0^(l-t)
                for t in range(min(l, k) + 1):
                    gk = g[l + k - t] * iv.mpf(math.comb(l + k - t, l) * math.factorial(l))
                    s += cl * ivbinom(l, t) * wbox ** (l - t) * gk
            out.append(s)
        return out, U
    cen, Uc = lamjet(wc, K - 1)
    box, Ub = lamjet(wb, K)
    val = sum((cen[k] * h ** k for k in range(K)), Z) + box[K] * h ** K
    return val, Uc


def term2(wlo, whi, Nc=120):
    wb = iv.mpf([wlo, whi])
    x1 = min(XA.b, (EPS1 / wb.a).b) if wb.a > 0 else XA.b
    xb = iv.mpf([0, x1])
    U = u_jet(xb, wb, 7, 4, Nc, tot=7)
    s = Z
    for (i, l), c in LAMP.items():
        s += c * xb ** i * wb ** l * U[(3 + i, l)] * iv.mpf(math.factorial(3 + i) * math.factorial(l))
    return xb * s / 6, x1


def qI(blo, bhi):
    wlo = ONE / iv.mpf(bhi) if bhi != float('inf') else iv.mpf(0)
    whi = ONE / iv.mpf(blo)
    return qI_w(wlo.a, whi.b)


def qI_w(wlo, whi):
    t1, Uc = term1(wlo, whi)
    t2, x1 = term2(wlo, whi)
    return t1 + t2, t1, t2, x1


# sanity: Lambda = (th+1)(th+2)(th+3)(th+4) on x^p w^q equals prod (p - q + r): check the operator coefficients on monomials
for (p_, q_) in ((0, 0), (1, 0), (0, 2), (2, 3), (3, 1)):
    val = sum(c * math.perm(p_, i) * math.perm(q_, l) for (i, l), c in LAM.items())
    assert val == (p_ - q_ + 1) * (p_ - q_ + 2) * (p_ - q_ + 3) * (p_ - q_ + 4), (p_, q_)


if __name__ == '__main__':
    # usage: python a07_zoneI.py b|w lo hi nbox log   (uniform boxes in b, or in w = 1/b; lo, hi exact decimals)
    mode, lo, hi, nb = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    log = sys.argv[5] if len(sys.argv) > 5 else None
    t0 = time.time(); res = []; qmin = None
    for (a, b) in grid_boxes(lo, hi, nb):
        q, t1, t2, x1 = qI(a, b) if mode == 'b' else qI_w(a, b)
        qmin = q.a if qmin is None or q.a < qmin else qmin
        res.append(dict(lo=str(thin_frac(a)), hi=str(thin_frac(b)), qlo=lo_str(q), qhi=hi_str(q), qlo_f=float(q.a),
                        x1=str(thin_frac(x1))))
        print(f"{mode} in [{float(a):.6g},{float(b):.6g}]: Lambda(R2) in [{float(q.a):.4f}, {float(q.b):.4f}]  (term1 [{float(t1.a):.4f},{float(t1.b):.4f}], term2 +-{float(abs(t2).b):.3e}, x1 {float(x1):.4f}) [{time.time()-t0:.0f}s]", flush=True)
        if log:
            json.dump(dict(mode=mode, lo=lo, hi=hi, nb=nb, XA=hi_str(XA), eps_hi=hi_str(EPS1), iv_prec=iv.prec, boxes=res,
                           minq=lo_str(qmin), complete=len(res) == nb), open(log, 'w'), indent=0)
    print("min lower =", float(qmin), " exact:", lo_str(qmin))
