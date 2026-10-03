"""a06: OUTER ZONE certificate (CONE_ALLD_PROOF.md section 5).  For a box x in [x_lo, x_hi], eps in [e_lo, e_hi] encloses
   Q_O(x, eps) = d_x^4 [x^2 (u_e - A0/B(1/w))],  w = eps/x,
so that d^3 Delta^4[Phi_e - eps b^2 A0/B(b)](m) = int Q_O(x_s, eps) M_4(s) ds  (x_s = (m+s) eps).
Taylor-model enclosure in (x, eps): with y = x^2 (u_e - A0/B) and f = d_x^4 y,
   f(c+h) in sum_{i+k<K} d^(i,k) f(c) h^(i,k)/(i!k!) + sum_{i+k=K} d^(i,k) f(box) h^(i,k)/(i!k!),
where the centre jets are thin (tight) and only the order-K terms use the naive box jets.  A box containing x = 1/2 uses the exact
antisymmetry: Ch_j/(1-2x), tauh/(1-2x) via halfshift (coefficient shift).  Usage: python a06_zoneO.py x_lo x_hi nbox [log]"""
import sys, time, json
import mpmath
from mpmath import iv
from a02_jets import Jet, Space, Z, ONE, ivbinom, ivq, grid_boxes, lo_str, hi_str, thin_frac
from a03_special import binet_w
from a05_model import model_jets, newton_u, implicit_root_jet, A0

EPS1 = iv.mpf(1) / 2001
K_TM = 3
HALF_THR = 0.4201                  # enlarge the remainder box to contain 1/2 when x_hi > 0.4201 (a numerical choice; any value is rigorous)


def halfshift2(J, Tn):
    """A/(1-2x) on a box containing 1/2 (A(1/2, eps) = 0): coefficient (i,k) <- -(1/2) A[i+1,k]; result in space Tn."""
    return Jet(Tn, [J[(i + 1, k)] * (-ONE / 2) for (i, k) in Tn.idx])


def yjet(xbox, ebox, nx, ne, Nc):
    """jet of y = x^2 (u_e - A0/B) in (x, eps) (x-order nx, eps-order ne; ne = 0: eps is the constant interval ebox)."""
    xbox, ebox = iv.mpf(xbox), iv.mpf(ebox)
    half = xbox.a <= 0.5 <= xbox.b
    Tn = Space(nx, ne, nx + ne)
    T = Space(nx + 1, ne, nx + 1 + ne) if half else Tn
    X = Jet.var(T, 0, xbox)
    E = Jet.var(T, 1, ebox) if ne else Jet.const(T, ebox)
    W = E * X.recip()
    V = E * (X * (-1) + 1).recip()
    C, tauh = model_jets(T, X, W, E, V, Nc)
    if half:
        C = [halfshift2(c, Tn) for c in C]
        tauh = halfshift2(tauh, Tn)
        X = Jet.var(Tn, 0, xbox)
        E = Jet.var(Tn, 1, ebox) if ne else Jet.const(Tn, ebox)
        W = E * X.recip()
    u = implicit_root_jet(C, tauh)
    B = binet_w(1, W)
    return (X * X) * (u - B.recip() * A0), u


def ncut(xhi):
    return int(80 + 700 * float(xhi))


def eps_pieces(xlo, ehi, ratio=1.5):
    """[0, ehi] split geometrically for small x (w = eps/x then varies little on each piece).  The cut points are thin
    120-bit values shared by adjacent pieces (no rounding to 53 bits: the top piece must reach ehi >= 1/2001 exactly)."""
    ehi = iv.mpf(ehi).b
    if xlo >= 0.03:
        return [(iv.mpf(0).a, ehi)]
    cuts = [ehi]
    while cuts[-1] > xlo / 400:
        cuts.append((cuts[-1] / iv.mpf(ratio)).a)
    cuts.append(iv.mpf(0).a)
    return [(cuts[k + 1], cuts[k]) for k in range(len(cuts) - 1)]


def qO_split(xlo, xhi):
    lo, hi, u0 = None, None, None
    for (e0, e1) in eps_pieces(float(xlo), EPS1.b):
        q, u = qO(xlo, xhi, e0, e1)
        lo = q.a if lo is None else min(lo, q.a)
        hi = q.b if hi is None else max(hi, q.b)
        u0 = u
    return iv.mpf([lo, hi]), u0


def qO(xlo, xhi, elo=0, ehi=None, K=K_TM):
    """mixed Taylor model: f(x,eps) = f(x,eps_c) + d_eps f(x,eps_c) h_e + (1/2) d_eps^2 f(x, xi) h_e^2, the first two by order-K Taylor
    models in x (thin centre), the last from the full box.  For x_hi > HALF_THR = 0.42 the remainder jets use the box enlarged to contain 1/2."""
    ehi = EPS1.b if ehi is None else ehi
    xb, eb = iv.mpf([xlo, xhi]), iv.mpf([elo, ehi])
    xc, ec = iv.mpf(xb.mid), iv.mpf(eb.mid)
    if xb.a <= 0.5 <= xb.b:
        xc = iv.mpf(0.5)
    xr = iv.mpf([xb.a, max(xb.b, mpmath.mpf(0.5))]) if xb.b > HALF_THR else xb      # remainder box
    Nc = ncut(xr.b)
    ya, ua = yjet(xc, ec, 4 + K - 1, 1, Nc)       # thin centre, eps-order 1
    yb, ub = yjet(xr, ec, 4 + K, 1, Nc)           # x-remainder box, eps frozen at eps_c
    yc, uc = yjet(xr, eb, 4, 2, Nc)               # full box, eps^2 remainder
    hx, he = xb - xc, eb - ec
    q = Z
    for k in (0, 1):
        t = Z
        for i in range(K):
            t += ivbinom(4 + i, i) * ya[(4 + i, k)] * hx ** i
        t += ivbinom(4 + K, K) * yb[(4 + K, k)] * hx ** K
        q += t * he ** k
    q += yc[(4, 2)] * he ** 2
    return q * 24, ua.c[0]


if __name__ == '__main__':
    # usage: python a06_zoneO.py x_lo x_hi nbox log   (x_lo, x_hi exact decimals; boxes from grid_boxes)
    xlo, xhi, nb = sys.argv[1], sys.argv[2], int(sys.argv[3])
    log = sys.argv[4] if len(sys.argv) > 4 else None
    t0 = time.time()
    res = []
    qmin = None
    for (a, b) in grid_boxes(xlo, xhi, nb):
        q, u0 = qO_split(a, b)
        qmin = q.a if qmin is None or q.a < qmin else qmin
        res.append(dict(xlo=str(thin_frac(a)), xhi=str(thin_frac(b)), qlo=lo_str(q), qhi=hi_str(q), qlo_f=float(q.a)))
        print(f"x in [{float(a):.5f},{float(b):.5f}]: Q_O in [{float(q.a):.4f}, {float(q.b):.4f}]  u(c) {float(u0.mid):.6f} [{time.time()-t0:.0f}s]", flush=True)
        if log:
            json.dump(dict(xlo=xlo, xhi=xhi, nb=nb, eps_hi=hi_str(EPS1), K=K_TM, iv_prec=iv.prec, boxes=res,
                           minq=lo_str(qmin), complete=len(res) == nb), open(log, 'w'), indent=0)
    print("min Q_O lower =", float(qmin), " exact:", lo_str(qmin))
