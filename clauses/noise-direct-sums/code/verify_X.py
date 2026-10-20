"""verify_X.py -- RIGOROUS (float interval arithmetic, ia.py) verification of construction X for given n.

For each n it encloses all quantities of the explicit interior kernel (see ../PROOF_PHI.md) and checks
  (P0) a > 0;  (P1) U(y) > 0 for 1 <= y <= L-1;  (P2) Q(s) = 4U(s-1) - 2s(s-1)Deff(s) >= 0 for 2 <= s <= L
       (so kappa(s) = Q(s)/((s-1)s(s+1)) >= 0);
  (CL) lower capacity  mL(y) <= phi(y), 1 <= y <= L;  (CU) upper capacity mU(s) <= phi(S-s), 2 <= s <= L;
  (CM) S even: m(S/2) <= phi(S/2);  (Z) 2 phi(0) > 1.
(C1) holds identically by construction (algebraic identity, see ../PROOF_PHI.md); for n <= 80 a brute-force float check of
(C1) and of the closed-form marginals from the explicit cell matrix is also run (option --brute).
Output per n: PASS/FAIL and margins: max mL/phi, max mU/phi, min U*(y(y+1))..., etc.
usage: python verify_X.py n0 n1 [step] [--brute]
"""
import sys
import numpy as np
from fractions import Fraction
from ia import IA, PI, sin_ia, dn, up

K = Fraction(1, 50)


def enclosures(n):
    S = n - 1; L = (S - 1) // 2
    j = np.arange(n, dtype=np.int64)
    z = 4 * j + 1
    zr = np.where(z > 2 * n, 4 * n - z, z)
    th = PI * IA.exact(zr.astype(float)) / IA.exact(float(4 * n))
    s = sin_ia(th)
    G = IA.exact(1.0) / (IA.exact(float(2 * n * n)) * s.sq())
    sumjG = (IA.exact(j.astype(float)) * G).sum()
    kap = IA.exact(2.0) - IA.exact(4.0) * sumjG / IA.exact(float(S))
    tk = IA.exact(2.0) - kap
    return S, L, G, kap, tk


def rho_ia(L, ymax):
    """rho(y) for y = 0..ymax (rho(0) = 0): min(3,y) (L-2y-1)_+ / (150 L y (y+1)) * (K*50) ; K = 1/50."""
    y = np.arange(ymax + 1, dtype=np.int64)
    num = np.minimum(3, y) * np.maximum(0, L - 2 * y - 1)
    num[0] = 0
    yy = np.maximum(y, 1)
    den = IA.exact(float(150 * L)) * IA.exact((yy * (yy + 1)).astype(float))
    r = IA.exact(num.astype(float)) / den
    return r


def verify(n):
    S, L, G, kap, tk = enclosures(n)
    out = dict(n=n, S=S, L=L)
    phi = G / tk                                      # phi(j) for j >= 1 (index 0 entry unused)
    phi0 = (G[0] - kap + IA.exact(1.0)) / tk
    out['Z'] = bool((IA.exact(2.0) * phi0).lo > 1.0)
    if L < 1:
        out['pass'] = False; out['why'] = 'L<1'; return out
    ys = np.arange(1, L + 1)
    D = (G[ys] - G[S - ys]) / tk                       # D(y), y = 1..L  (index y-1)
    r = rho_ia(L, L + 1)                                # r[y] = rho(y)
    half = ys // 2
    AFX = IA.exact(3.0) * r[ys] + r[ys - 1] - r[half]
    # E1(t) = R3(S-t) + (S-t-1)/(2 (S-t)^3),  R3(m) = sum_{s=L+1}^m s^-3
    sv = np.arange(L + 1, S, dtype=np.int64)          # s = L+1..S-1
    sI = IA.exact(sv.astype(float))
    inv3 = IA.exact(1.0) / (sI * sI * sI)
    R3c = inv3.cumsum()                                 # R3c[i] = sum_{s=L+1}^{L+1+i} s^-3
    def R3(m):                                          # m array in [L+1, S-1]
        return R3c[np.asarray(m) - (L + 1)]
    St = S - ys                                         # in [S-L, S-1]
    StI = IA.exact(St.astype(float))
    E1 = R3(St) + IA.exact((St - 1).astype(float)) / (IA.exact(2.0) * StI * StI * StI)
    tI = IA.exact(ys.astype(float))
    num_a = (tI * (D - AFX)).sum(); den_a = (tI * E1).sum()
    a = num_a / den_a
    out['a'] = (float(a.lo), float(a.hi))
    P0 = bool(a.lo > 0)
    Deff = D - AFX - a * E1
    tD = tI * Deff
    Uf = tD.cumsum()                                     # U(y) forward, y = 1..L
    rc = tD.rcumsum()                                    # rc[i] = sum_{t >= i+1} t Deff(t)
    Ub = IA(np.concatenate([-rc.hi[1:], [0.0]]), np.concatenate([-rc.lo[1:], [0.0]]))   # U(y) = -sum_{t>y}
    Uu = Uf.meet(Ub)
    P1 = bool(np.all(Uu.lo[:-1] > 0)) if L >= 2 else True
    # Q(s) = 4U(s-1) - 2 s (s-1) Deff(s), s = 2..L
    if L >= 2:
        sQ = np.arange(2, L + 1)
        Q = IA.exact(4.0) * Uu[sQ - 2] - IA.exact((2 * sQ * (sQ - 1)).astype(float)) * Deff[sQ - 1]
        P2 = bool(np.all(Q.lo >= 0))
        out['Qmin_rel'] = float(np.min(Q.lo / np.maximum(Uu.hi[sQ - 2], 1e-300)))
    else:
        P2 = True
    T = IA.exact(2.0) * Uu / IA.exact((ys * (ys + 1)).astype(float))
    ZL = R3c[-1:]                                        # sum_{s=L+1}^{S-1} s^-3  (scalar IA)
    ZL = IA(ZL.lo[0], ZL.hi[0])
    two3 = IA.frac(Fraction(2, 3)); one3 = IA.frac(Fraction(1, 3))
    endL = (a * one3) * (IA.exact(2.0) * ZL + IA.exact((S - 1 - ys).astype(float)) / (StI * StI * StI))
    mL = two3 * T + IA.exact(2.0) * r[ys] + two3 * r[ys - 1] + endL
    phiL = phi[ys]
    CL = bool(np.all(mL.hi <= phiL.lo))
    out['maxL'] = float(np.max(mL.hi / phiL.lo))
    out['argL'] = int(ys[np.argmax(mL.hi / phiL.lo)])
    if L >= 2:
        sQ = np.arange(2, L + 1)
        W = IA(ZL.lo, ZL.hi) - R3(S - sQ)              # sum_{s'=S-s+1}^{S-1} s'^-3
        mU = Q / (IA.exact(3.0) * IA.exact((sQ * (sQ + 1)).astype(float))) + two3 * r[sQ // 2] + \
            IA.frac(Fraction(2, 3)) * a * W
        phiU = phi[S - sQ]
        CU = bool(np.all(mU.hi <= phiU.lo))
        out['maxU'] = float(np.max(mU.hi / phiU.lo)); out['argU'] = int(sQ[np.argmax(mU.hi / phiU.lo)])
    else:
        CU = True; out['maxU'] = 0.0
    CM = True
    if S % 2 == 0:
        h = S // 2
        sm = (IA(ZL.lo, ZL.hi) - R3(np.array([h])))     # sum_{s=h+1}^{S-1} s^-3   (L+1 = h for S even)
        hI = IA.exact(float(h))
        mM = (a * one3) * (IA.exact(2.0) * sm + IA.exact(float(h - 1)) / (hI * hI * hI))
        CM = bool(mM.hi[0] <= phi[h].lo)
        out['ratioM'] = float(mM.hi[0] / phi[h].lo)
    out.update(P0=P0, P1=P1, P2=P2, CL=CL, CU=CU, CM=CM)
    out['pass'] = all([P0, P1, P2, CL, CU, CM, out['Z']])
    return out


def brute(n):
    """float brute force: explicit cell matrix -> (C1) residual and closed-form marginal check."""
    from constrX import build
    from ukern2 import check
    c = build(n)
    S, L = c['S'], c['L']
    P = np.zeros((S + 1, S + 1))
    for p in range(1, S):
        for q in range(1, S - p):
            P[p, q] = c['h'][p + q] + c['beta'][p] + c['beta'][q]
    for (p, q), w in c['cells'].items():
        P[p, q] += w
        if p != q: P[q, p] += w
    m = P.sum(axis=1)
    R = np.array([sum(P[p, y - p] for p in range(0, y + 1)) for y in range(S + 1)])
    F = m - R / 2
    ys = np.arange(1, L + 1)
    AF = F[ys] - F[S - ys]
    return float(np.abs(AF - c['D'][1:]).max()), float(np.abs(m - check(c)['m']).max()), float(P.min())


if __name__ == '__main__':
    n0, n1 = int(sys.argv[1]), int(sys.argv[2])
    step = int(sys.argv[3]) if len(sys.argv) > 3 and not sys.argv[3].startswith('--') else 1
    do_brute = '--brute' in sys.argv
    allpass = True; worst = 0.0
    for n in range(n0, n1 + 1, step):
        o = verify(n)
        allpass &= o['pass']
        w = max(o.get('maxL', 0), o.get('maxU', 0), o.get('ratioM', 0))
        worst = max(worst, w)
        line = (f"n={n:6d} {'PASS' if o['pass'] else 'FAIL'} maxL={o.get('maxL',0):.4f}@{o.get('argL',0)} "
                f"maxU={o.get('maxU',0):.4f}@{o.get('argU',0)} mid={o.get('ratioM',0):.4f} a=[{o['a'][0]:.6f},{o['a'][1]:.6f}] "
                f"Qmin_rel={o.get('Qmin_rel',0):.3e} " +
                ' '.join(f"{k}={int(o[k])}" for k in ('P0', 'P1', 'P2', 'CL', 'CU', 'CM', 'Z') if k in o))
        if do_brute and n <= 80:
            e1, e2, pm = brute(n)
            line += f" | brute C1err={e1:.1e} m-err={e2:.1e} minP={pm:+.1e}"
        print(line, flush=True)
    print(f"RANGE {n0}..{n1} step {step}: {'ALL PASS' if allpass else 'SOME FAIL'}; worst ratio {worst:.4f}", flush=True)
