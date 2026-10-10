"""
GLOBAL_fam3COR.py -- Theorem F3 for the correlated-settings strength: within the Fourier-shift family F3,
S^COR <= S(DKZ_3) (hence also S^UC <= S^UNI... no: S^UNI <= S^UC <= S^COR <= S0), equality only at the DKZ copies.
Ansh Mishra, Aryan Senthilkumar, 2026-10-10.  Uses the ball-arithmetic helpers of GLOBAL_fam3BB.py.

Upper bound.  S^COR(q) = max_sigma min_p sum_l sigma_l D(q_l || p_l) <= min_p max_l D(q_l || p_l) (weak duality),
and for F3 (shift-invariant) every sub-probability w on the 27 reduced strategies gives a dominated local model, so
S^COR(z) <= max_l D(Q_l(z) || P_l(w(z))).  A box is certified if max_l sup_box D_l < S0.
Models: w(z) = w_c + M (z - c) + (1/2) sum_lambda (z - c)^T N_lambda (z - c) e_lambda.
 * generic boxes: w_c = minimax (COR-optimal) weights at the centre (mirror ascent on sigma + weighted EM), M fitted
   so that every link gradient vanishes at c (least squares), N = 0; bounds: per-link Taylor (complete per-cell
   derivatives, now including -Q d2P/P), and the separable per-link bound with the constant model w_c;
 * copy boxes: exact KKT weights w*, M = the arb-ball solution of the 4 link-gradient equations (exact: the true
   M lies in the ball; the mass equation sum M = 0 follows from criticality), N dyadic with exactly zero sum chosen so
   that the four link Hessians are (approximately) equal to their negative-definite average.  At the copy every link
   has D_l = S0 and grad D_l = 0 exactly, so a negative-definite Hessian enclosure on a cube gives D_l < S0 on the
   punctured cube for every link.
usage: python GLOBAL_fam3COR.py cubes | run
"""
import sys
import json
import math
import time
import itertools
import heapq
from fractions import Fraction
import numpy as np
from flint import arb, arb_mat
import GLOBAL_fam3BB as B

A = B.A
S0 = B.S0
LV = B.LV
HIT = B.HIT
E27 = B.E27
QMIN = B.QMIN
PI = B.PI


# ------------------------------------------------------------------------------------------ models (float)
def D_links(Q, w):
    P = (w @ E27).reshape(4, 3)
    with np.errstate(divide="ignore", invalid="ignore"):
        t = np.where(Q > 0, Q * np.log(Q / np.maximum(P, 1e-300)), 0.0)
    return t.sum(axis=1)


def cor_weights(Q, w0=None, iters=80, inner=20):
    """approximate minimax weights: min_w max_l D_l(w) (mirror ascent on sigma, weighted EM on w)."""
    sig = np.full(4, 0.25)
    w = np.full(27, 1 / 27) if w0 is None else np.maximum(w0, 1e-12) / np.maximum(w0, 1e-12).sum()
    best_w, best_v = w.copy(), np.inf
    for it in range(iters):
        for _ in range(inner):
            P = np.maximum(w @ E27, 1e-300).reshape(4, 3)
            ratio = (sig[:, None] * Q / P).reshape(-1)
            g = E27 @ ratio
            w = w * g
            w /= w.sum()
        Dl = D_links(Q, w)
        if Dl.max() < best_v:
            best_v, best_w = Dl.max(), w.copy()
        sig = sig * np.exp(30 * (Dl - Dl.max()))
        sig = np.maximum(sig, 1e-12)                  # avoid underflow of every setting weight (0/0)
        sig /= sig.sum()
    return best_w


_CVX = {}


def cor_weights_cvx(Q):
    """minimax weights min_w max_l D(Q_l || P_l(w)) by a convex program (cvxpy, Clarabel; parametrised, DPP).
    Only the quality of the model depends on the solver; every model is checked rigorously afterwards."""
    import cvxpy as cp
    if not _CVX:
        Qp = cp.Parameter((4, 3), nonneg=True)
        wv = cp.Variable(27, nonneg=True)
        tt = cp.Variable()
        P = E27.T @ wv
        cons = [cp.sum(wv) == 1] + [cp.sum(cp.rel_entr(Qp[l], P[3 * l:3 * l + 3])) <= tt for l in range(4)]
        _CVX.update(Qp=Qp, wv=wv, prob=cp.Problem(cp.Minimize(tt), cons))
    _CVX["Qp"].value = np.maximum(Q, 0.0)
    try:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            _CVX["prob"].solve(solver="CLARABEL")
        w = np.maximum(np.asarray(_CVX["wv"].value, float), 0.0)
        if not np.isfinite(w).all() or w.sum() <= 0:
            raise ValueError
        return w / w.sum()
    except Exception:
        return cor_weights(Q)


def cor_model_at(c, h, w0=None, eps=1e-7, weights=None):
    """weights: None -> minimax weights (cor_weights); 'uni' -> S^UNI-optimal EM weights (cheaper); any model is
    valid for the bound (only its quality depends on the choice)."""
    Q = B.Qf(c)
    if weights == "uni":
        w = B.em(Q, w0)
    else:
        w = cor_weights_cvx(Q)                            # exact minimax weights (convex program)
    P = (w @ E27).reshape(4, 3)
    dQ = B.gradQf(c)
    supp = np.nonzero(w > 1e-9 * w.max())[0]
    M = np.zeros((27, 3))
    if len(supp) >= 2:
        k = len(supp)
        # per direction i: the four link gradients sum_m [dQ_l(m) (log(Q/P) + 1) - Q/P dP_l(m)] are made EQUAL (to a
        # free common value tau_i, approximately the derivative of S^COR), with sum of the weight slopes = 0;
        # unknowns (x on the support, tau_i), minimum-norm least squares
        Cl = np.zeros((5, k + 1))
        for a, lam in enumerate(supp):
            for l in range(4):
                m = HIT[lam, l]
                Cl[l, a] += Q[l, m] / P[l, m] if P[l, m] > 0 else 0.0
            Cl[4, a] = 1.0
        Cl[:4, k] = 1.0
        for i in range(3):
            rhs = np.array([np.sum(dQ[i, l] * (np.log(np.maximum(Q[l], 1e-300) / np.maximum(P[l], 1e-300)) + 1))
                            for l in range(4)] + [0.0])
            x = np.linalg.lstsq(Cl, rhs, rcond=None)[0]
            M[supp, i] = x[:k]
    need = np.abs(M) @ h
    with np.errstate(divide="ignore", invalid="ignore"):
        s = np.min(np.where(need > 0, 0.8 * w / need, np.inf))
    if s < 1:
        M = M * s
    w = (1 - eps) * w + eps / 27
    M = (1 - eps) * M
    return w * (1 - 1e-12), M


# ------------------------------------------------------------------------------------------ arb bounds per link
def model_q(wa, Ma, Na, h, exact_mass):
    """P at the centre, gradient at the centre, constant Hessian, enclosures of P and of grad P over the box."""
    hb = [arb(0, float(h[i])) for i in range(3)]
    Pc = [[arb(0) for _ in range(3)] for _ in range(4)]
    Pg = [[[arb(0)] * 3 for _ in range(3)] for _ in range(4)]
    PH = [[[[arb(0)] * 3 for _ in range(3)] for _ in range(3)] for _ in range(4)]
    for lam in range(27):
        for l in range(4):
            m = int(HIT[lam, l])
            Pc[l][m] += wa[lam]
            for i in range(3):
                Pg[l][m][i] += Ma[lam][i]
                if Na is not None:
                    for j in range(3):
                        PH[l][m][i][j] += Na[lam][i][j]
    Pb, dPb = [], []
    for l in range(4):
        rowb, rowd = [], []
        for m in range(3):
            v = Pc[l][m] + sum((Pg[l][m][i] * hb[i] for i in range(3)), arb(0))
            if Na is not None:
                v += sum((PH[l][m][i][j] * hb[i] * hb[j] for i in range(3) for j in range(3)), arb(0)) / 2
            rowb.append(v)
            rowd.append([Pg[l][m][i] + (sum((PH[l][m][i][j] * hb[j] for j in range(3)), arb(0)) if Na is not None
                                        else arb(0)) for i in range(3)])
        Pb.append(rowb)
        dPb.append(rowd)
    ok = True
    for lam in range(27):
        lo = wa[lam] - sum((abs(Ma[lam][i]) * A(h[i]) for i in range(3)), arb(0))
        if Na is not None:
            lo -= sum((abs(Na[lam][i][j]) * A(h[i]) * A(h[j]) for i in range(3) for j in range(3)), arb(0)) / 2
        if not lo >= 0:
            ok = False
    if not exact_mass:
        tot = sum(wa, arb(0)) + sum((abs(sum((Ma[lam][i] for lam in range(27)), arb(0))) * A(h[i]) for i in range(3)),
                                    arb(0))
        if Na is not None:
            tot += sum((abs(sum((Na[lam][i][j] for lam in range(27)), arb(0))) * A(h[i]) * A(h[j])
                        for i in range(3) for j in range(3)), arb(0)) / 2
        if not tot <= 1:
            ok = False
    return Pc, Pg, PH, Pb, dPb, ok


def links_taylor(zc, h, wa, Ma, Na=None, exact_mass=False, require_all_good=False):
    """per link l: (D_l(c) over good cells, g_l, H_l enclosure, crude_l); None if the model is invalid."""
    Pc, Pg, PH, Pb, dPb, ok = model_q(wa, Ma, Na, h, exact_mass)
    if not ok:
        return None
    out = []
    for l in range(4):
        Lv = [int(x) for x in LV[l]]
        phi_c = sum((Lv[i] * zc[i] for i in range(3)), arb(0))
        rad = sum(abs(Lv[i]) * float(h[i]) for i in range(3)) * (1 + 1e-12)
        dc, db = B.link_data(phi_c, rad)
        Fc = arb(0)
        g = [arb(0)] * 3
        H = [[arb(0)] * 3 for _ in range(3)]
        crude = arb(0)
        for m in range(3):
            Qc, dKc = dc[m]
            Qb, dKb, d2Kb = db[m]
            good = (Qb > QMIN) and (Pb[l][m] > QMIN)
            if not good:
                if require_all_good or not Pb[l][m] > 0:
                    return None
                plo = Pb[l][m].lower()
                lo = Qb.lower(); hi = Qb.upper()
                if lo < 0:
                    lo = arb(0)
                if hi > 1:
                    hi = arb(1)
                fl = arb(0) if lo == 0 else lo * (lo.log() - plo.log())
                fh = arb(0) if hi == 0 else hi * (hi.log() - plo.log())
                crude += fl.upper() if fl.upper() > fh.upper() else fh.upper()
                continue
            lr_c = Qc.log() - Pc[l][m].log()
            Fc += Qc * lr_c
            for i in range(3):
                g[i] += dKc * Lv[i] * (lr_c + 1) - Qc * Pg[l][m][i] / Pc[l][m]
            lr_b = Qb.log() - Pb[l][m].log()
            a = [dKb * Lv[i] / Qb - dPb[l][m][i] / Pb[l][m] for i in range(3)]
            for i in range(3):
                for j in range(i, 3):
                    v = d2Kb * Lv[i] * Lv[j] * (lr_b + 1) + Qb * a[i] * a[j]
                    if Na is not None:
                        v -= Qb * PH[l][m][i][j] / Pb[l][m]
                    H[i][j] += v
        for i in range(3):
            for j in range(i + 1, 3):
                H[j][i] = H[i][j]
        out.append((Fc, g, H, crude))
    return out


def link_bound(T, h):
    Fc, g, H, crude = T
    gm = [float(x.mid()) for x in g]
    Hm = [[float(H[i][j].mid()) for j in range(3)] for i in range(3)]
    gerr = sum((abs(g[i] - A(gm[i])).upper() * A(h[i]) for i in range(3)), arb(0))
    herr = sum((abs(H[i][j] - A(Hm[i][j])).upper() * A(h[i]) * A(h[j]) for i in range(3) for j in range(3)),
               arb(0)) / 2
    return Fc + B.quad_max(gm, Hm, np.asarray(h, float)) + gerr + herr + crude


def cor_taylor_ub(c, h, w, M):
    zc = [A(x) for x in c]
    wa = [A(x) for x in w]
    Ma = [[A(M[lam, i]) for i in range(3)] for lam in range(27)]
    T = links_taylor(zc, h, wa, Ma)
    if T is None:
        return None
    return max((link_bound(t, h) for t in T), key=lambda x: float(x.upper()))


def cor_separable_ub(c, h, w, piece=0.004):
    """constant model: max_l sup_{phi in I_l} D(Q(phi) || P_l) (same per-link sup as GLOBAL_fam3BB.separable_ub)."""
    wa = [A(x) for x in w]
    if not sum(wa, arb(0)) <= 1 or any(not x >= 0 for x in wa):
        return None
    P = [[arb(0) for _ in range(3)] for _ in range(4)]
    for lam in range(27):
        for l in range(4):
            P[l][int(HIT[lam, l])] += wa[lam]
    best_all = None
    for l in range(4):
        if any(not P[l][m] > 0 for m in range(3)):
            return None
        Lv = [int(x) for x in LV[l]]
        phc = sum(Lv[i] * float(c[i]) for i in range(3))                      # exact (dyadic centres)
        r = sum(abs(Lv[i]) * float(h[i]) for i in range(3))
        npc = max(1, int(math.ceil(2 * r / piece)))
        lo_end = A(phc) - A(r) * (1 + 1e-12) - 1e-15
        step = (2 * A(r) * (1 + 1e-12) + 2e-15) / npc
        plog = [P[l][m].log() for m in range(3)]
        best = None
        for k in range(npc):
            mid = lo_end + k * step + step / 2
            J = mid + arb(0, float((step / 2).upper()) * (1 + 1e-12))
            s = arb(0)
            for m in range(3):
                Kb = B.K_arb(J + 2 * PI * m / 3)
                klo, khi = Kb.lower(), Kb.upper()
                if klo < 0:
                    klo = arb(0)
                if khi > 1:
                    khi = arb(1)
                fl = arb(0) if klo == 0 else klo * (klo.log() - plog[m])
                fh = arb(0) if khi == 0 else khi * (khi.log() - plog[m])
                s += fl.upper() if fl.upper() > fh.upper() else fh.upper()
            if best is None or s.upper() > best.upper():
                best = s
        if best_all is None or best.upper() > best_all.upper():
            best_all = best
    return best_all


# ------------------------------------------------------------------------------------------ copy models
def copy_cor_models():
    copies = B.load_copies()
    D = json.load(open("GLOBAL_fam3_copies.json"))
    out = []
    for cp, cj in zip(copies, D["copies"]):
        lev = np.array(cj["levels"])
        facet = cj["facet"]
        nf = len(facet)
        zf = cp["z_f"]
        za = cp["z_arb"]
        Q = B.Qf(zf)
        dQ = B.gradQf(zf)
        rk = np.array([float(B.RLEV[k].mid()) for k in range(3)])
        r = rk[lev]
        q = Q.reshape(-1)
        rr = r.reshape(-1)
        Ef = np.zeros((12, nf))
        for a, lam in enumerate(facet):
            for l in range(4):
                Ef[3 * l + HIT[lam, l], a] = 1
        Bm = rr[:, None] * Ef
        Mexact = [[None] * 3 for _ in range(27)]
        for lam in range(27):
            for i in range(3):
                Mexact[lam][i] = arb(0)
        Mf = np.zeros((27, 3))
        # exact link-gradient equations: C x = d, C[l, a] = r*_l(hit_l(lambda_a)) (arb), d_l = sum_m dQ_l(m)_i log r*
        Carb = [[B.RLEV[int(lev[l, HIT[lam, l]])] for lam in facet] for l in range(4)]
        for i in range(3):
            dq = dQ[i].reshape(-1)
            W = np.diag(1 / q)
            Cc = np.array([[float(Carb[l][a].mid()) for a in range(nf)] for l in range(4)])
            dc = np.array([np.sum(dQ[i, l] * np.log(r[l])) for l in range(4)])
            K = np.block([[2 * Bm.T @ W @ Bm, Cc.T], [Cc, np.zeros((4, 4))]])
            sol = np.linalg.lstsq(K, np.concatenate([2 * Bm.T @ W @ dq, dc]), rcond=None)[0]
            xf = sol[:nf]
            # exact projection onto {C x = d} in ball arithmetic: x = xf + C^T (C C^T)^{-1} (d - C xf)
            d_arb = []
            for l in range(4):
                Lv = [int(t) for t in LV[l]]
                phi = sum((Lv[t] * za[t] for t in range(3)), arb(0))
                s = arb(0)
                for m in range(3):
                    s += B.dK_arb(phi + 2 * PI * m / 3) * Lv[i] * B.RLEV[int(lev[l, m])].log()
                d_arb.append(s)
            Cm = arb_mat([[Carb[l][a] for a in range(nf)] for l in range(4)])
            res = arb_mat([[d_arb[l] - sum((Carb[l][a] * A(xf[a]) for a in range(nf)), arb(0))] for l in range(4)])
            G = Cm * Cm.transpose()
            y = G.solve(res)
            corr = Cm.transpose() * y
            for a, lam in enumerate(facet):
                Mexact[lam][i] = A(xf[a]) + corr[a, 0]
                Mf[lam, i] = xf[a]
        # per-link Hessians at the copy with Mf (float) and the equalising quadratic N (dyadic, exact zero sum)
        P = Q / r
        dP = np.zeros((3, 4, 3))
        for lam in range(27):
            for l in range(4):
                dP[:, l, HIT[lam, l]] += Mf[lam]
        ph = LV @ zf
        Hl = []
        for l in range(4):
            H = np.zeros((3, 3))
            for m in range(3):
                psi = ph[l] + 2 * math.pi * m / 3
                d2 = (-4 * np.cos(psi) - 8 * np.cos(2 * psi)) / 9 * np.outer(LV[l], LV[l])
                a = dQ[:, l, m] / Q[l, m] - dP[:, l, m] / P[l, m]
                H += d2 * (np.log(Q[l, m] / P[l, m]) + 1) + Q[l, m] * np.outer(a, a)
            Hl.append(H)
        Hbar = sum(Hl) / 4
        idx = [(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2)]
        rows, rhs = [], []
        for l in range(4):
            for e, (i, j) in enumerate(idx):
                row = np.zeros(nf * 6)
                for a, lam in enumerate(facet):
                    row[a * 6 + e] = -r[l, HIT[lam, l]]
                rows.append(row)
                rhs.append(Hbar[i, j] - Hl[l][i, j])
        for e in range(6):
            row = np.zeros(nf * 6)
            row[[a * 6 + e for a in range(nf)]] = 1
            rows.append(row)
            rhs.append(0.0)
        sol = np.linalg.lstsq(np.array(rows), np.array(rhs), rcond=None)[0]
        Nd = np.zeros((27, 3, 3))
        for e, (i, j) in enumerate(idx):
            col = np.array([sol[a * 6 + e] for a in range(nf)])
            col = np.round(col * 2 ** 30) / 2 ** 30
            col[-1] = -np.sum(col[:-1])
            assert Fraction(float(np.sum(col))) == 0
            for a, lam in enumerate(facet):
                Nd[lam, i, j] = col[a]
                Nd[lam, j, i] = col[a]
        Na = [[[A(Nd[lam, i, j]) for j in range(3)] for i in range(3)] for lam in range(27)]
        out.append(dict(p=cp["p"], z_arb=za, z_f=zf, wa=cp["wa"], Ma=Mexact, Mf=Mf, Na=Na, Nd=Nd,
                        Hbar_eig=np.linalg.eigvalsh(Hbar)))
    return out


def copy_cor_ub(cm, c, h):
    """per-link Taylor bound on the box c +- h with the copy COR model, expanded at the box centre."""
    zc = [A(x) for x in c]
    d0 = [zc[i] - cm["z_arb"][i] for i in range(3)]
    wa = []
    Mc = []
    for lam in range(27):
        v = cm["wa"][lam] + sum((cm["Ma"][lam][i] * d0[i] for i in range(3)), arb(0)) + \
            sum((cm["Na"][lam][i][j] * d0[i] * d0[j] for i in range(3) for j in range(3)), arb(0)) / 2
        wa.append(v)
        Mc.append([cm["Ma"][lam][i] + sum((cm["Na"][lam][i][j] * d0[j] for j in range(3)), arb(0)) for i in range(3)])
    T = links_taylor(zc, h, wa, Mc, cm["Na"], exact_mass=True)
    if T is None:
        return None
    return max((link_bound(t, h) for t in T), key=lambda x: float(x.upper()))


def certify_cor_cube(cm, rho):
    h = np.full(3, rho)
    T = links_taylor(cm["z_arb"], h, cm["wa"], cm["Ma"], cm["Na"], exact_mass=True, require_all_good=True)
    if T is None:
        return False
    for (Fc, g, H, crude) in T:
        assert abs(float((Fc - S0).mid())) < 1e-25 and all(abs(float(x.mid())) < 1e-20 for x in g)
        if B.chol([[-H[i][j] for j in range(3)] for i in range(3)]) is None:
            return False
    return True


# ------------------------------------------------------------------------------------------ branch and bound
def run(max_boxes=4_000_000, min_h=1e-7, part=0, nparts=1):
    cms = copy_cor_models()
    cubes = []
    for cm in cms:
        rho = None
        for r in (0.01, 0.005, 0.003, 0.002, 0.001, 5e-4, 2e-4, 1e-4):
            if certify_cor_cube(cm, r):
                rho = r
                break
        assert rho is not None, "no COR cube"
        cubes.append(([(cm["z_arb"][i] - rho).upper() for i in range(3)],
                      [(cm["z_arb"][i] + rho).lower() for i in range(3)], rho))
        print(f"COR cube at {cm['p']}: rho = {rho}; averaged Hessian eigenvalues {np.round(cm['Hbar_eig'], 5)}",
              flush=True)
    T0 = time.time()
    hw = 0.125
    side = 9 * 2 * hw
    heap, cnt = [], 0
    nroot = 0
    for flat, idx in enumerate(itertools.product(range(9), repeat=3)):
        if flat % nparts != part:                        # root boxes of this part only (parts are disjoint)
            continue
        heapq.heappush(heap, (-hw, cnt, np.array([(2 * k + 1) * hw for k in idx]), np.full(3, hw), None))
        cnt += 1
        nroot += 1
    side = side * (nroot / 729) ** (1 / 3)
    rows, models = [], []
    n_proc = 0
    vol = 0.0
    used = {}
    worst = math.inf
    while heap:
        _, _, c, h, w0 = heapq.heappop(heap)
        n_proc += 1
        if n_proc > max_boxes:
            print("ABORT: box budget exhausted", flush=True)
            return False
        if any(all((arb(float(c[i])) - arb(float(h[i]))) >= lo[i] and (arb(float(c[i])) + arb(float(h[i]))) <= hi[i]
                   for i in range(3)) for (lo, hi, _) in cubes):
            rows.append(list(c) + list(h) + [0, 0.0, -1]); models.append(np.zeros(27 + 81))
            vol += float(np.prod(2 * h))
            continue
        rec = None
        w = None
        for k, cm in enumerate(cms):
            if np.max(np.abs(c - cm["z_f"])) < 0.12:
                ub = copy_cor_ub(cm, c, h)
                if ub is not None and ub < S0:
                    rec = (1, 0.0, k, np.zeros(27 + 81))
                    break
        if rec is None:
            for wmode in ("minimax", "uni"):                  # exact minimax weights first, EM weights second
                wb, Mb = cor_model_at(c, h, w0, 0.0, weights=("uni" if wmode == "uni" else None))
                for eps in (1e-7, 1e-3, 1e-2):
                    w = (1 - eps) * wb + eps / 27 * (1 - 1e-12)
                    M = (1 - eps) * Mb
                    ub = cor_taylor_ub(c, h, w, M)
                    if ub is not None and ub < S0:
                        rec = (2, eps, -1, np.concatenate([w, M.reshape(-1)]))
                        break
                    ub = cor_separable_ub(c, h, w)
                    if ub is not None and ub < S0:
                        rec = (3, eps, -1, np.concatenate([w, np.zeros(81)]))
                        break
                if rec is not None:
                    break
        if rec is not None:
            rows.append(list(c) + list(h) + [rec[0], rec[1], rec[2]]); models.append(rec[3])
            used[(rec[0], rec[1])] = used.get((rec[0], rec[1]), 0) + 1
            vol += float(np.prod(2 * h))
            worst = min(worst, float((S0 - ub).lower()))
            continue
        if h.max() < min_h:
            print(f"FAIL: box at {c} half-width {h} not certified (ub {ub})", flush=True)
            return False
        i = int(np.argmax(h))
        h2 = h.copy(); h2[i] /= 2
        for s in (-1, 1):
            c2 = c.copy(); c2[i] += s * h2[i]
            assert c2[i] - s * h2[i] == c[i]
            heapq.heappush(heap, (-float(h2.max()), cnt, c2, h2, w)); cnt += 1
        if n_proc % 5000 == 0:
            print(f"  processed {n_proc}, pending {len(heap)} (largest half-width {-heap[0][0]:.2e}), certified "
                  f"{len(rows)}, volume fraction {vol / side ** 3:.6f}, methods {used}  [{time.time() - T0:.0f}s]",
                  flush=True)
    print(f"DONE: [0, 9/4]^3 covered exactly by {len(rows)} certified boxes ({sum(1 for r in rows if r[6] == 0)} in the "
          f"COR cubes); processed {n_proc}; volume fraction {vol / side ** 3:.12f}; smallest gap S0 - UB {worst:.3e} "
          f"nats; methods {used}  [{time.time() - T0:.0f}s]", flush=True)
    fname = "GLOBAL_fam3COR_cert.npz" if nparts == 1 else f"GLOBAL_fam3COR_cert_part{part}of{nparts}.npz"
    np.savez_compressed(fname, rows=np.array(rows), models=np.array(models),
                        cubes=np.array([[cb[2]] for cb in cubes]))
    print(f"certificate written: {fname}", flush=True)
    return True


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "cubes"
    if cmd == "cubes":
        for cm in copy_cor_models():
            print(cm["p"], "Hbar eig", np.round(cm["Hbar_eig"], 5),
                  [(r, certify_cor_cube(cm, r)) for r in (0.01, 0.003, 0.001, 3e-4)])
    elif cmd == "run":
        part = int(sys.argv[2]) if len(sys.argv) > 2 else 0
        nparts = int(sys.argv[3]) if len(sys.argv) > 3 else 1
        print("PART VERIFIED (COR)" if run(part=part, nparts=nparts) else "NOT VERIFIED")
