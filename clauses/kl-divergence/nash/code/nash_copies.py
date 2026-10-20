"""The global maximisers of B -> Phi(A*, B; mu*) in the B&B domain: images of DKZ_3's two Bob bases under the
symmetries of Phi(A*, .; mu*) (left multiplication by Z^j, Z = diag(1, w, w^2); column permutations; complex
conjugation.  NOTE: the cyclic shift X is NOT a symmetry: alpha_0 = 1/2 makes X^H |a>_0 leave the basis A_0), their exact CKM coordinates, exact KKT kernels and dyadic first-order kernel slopes; and the star bound.

Exactness at a copy x_c (used by the star bound):
  K(y) = Kc + M (y - x_c),  Kc = relabelled K*_y (Prop K3 facet decomposition), M dyadic, zero b-sums, supported on
  supp Kc.  Then g(x_c) = S0 (relabelling invariance of D, Prop K3) and grad g(x_c) = 0 (criticality of the level
  probabilities, Theorem 3, plus KKT: r_0(a0, b) + r_1(a1, b) is constant on supp Kc(. | a0, a1)).
Star bound: if the Hessian enclosure of g over the hull of {x_c} and a box is negative definite, then
  g(y) = S0 + (1/2)(y - x_c)^T H(xi) (y - x_c) <= S0 on the box, with equality only at y = x_c.
"""
import itertools
import math
import numpy as np
from mpmath import iv, mp

import nash_iv as V
from nash_iv import IV
import nash_core as C

PI12 = math.pi / 12
DOM_LO = np.zeros(6)
DOM_HI = np.array([math.pi / 2, math.pi / 2, math.pi / 2, math.pi, 2 * math.pi / 3, 2 * math.pi])


def dkz_bob():
    """DKZ_3 Bob steered bases Bt*_y: columns 3^{-1/2} (w^{k(b + beta_y)})_k, beta = (1/4, -1/4)."""
    w = np.exp(2j * np.pi / 3)
    beta = (0.25, -0.25)
    return [np.array([[w ** (k * (b + beta[y])) for b in range(3)] for k in range(3)]) / np.sqrt(3) for y in range(2)]


def base_check():
    """q of the base bases must be the DKZ link laws: q_xy(a, b) = Q_{level}/3."""
    Bt = dkz_bob()
    Q = np.array([2 * (2 + math.sqrt(3)) / 9, 2 * (2 - math.sqrt(3)) / 9, 1 / 9])
    err = 0.0
    for y in range(2):
        q = C.q_float(Bt[y][None])[0]
        for x in range(2):
            err = max(err, np.abs(q[x] - Q[C.GLEV[x, y]] / 3).max())
    return err


def orbit():
    """all images (Bt, y, j, 0, sigma, conj) with Bt' = conj^c (Z^j Bt*_y P_sigma)."""
    w = np.exp(2j * np.pi / 3)
    Z = np.diag([1, w, w * w])
    out = []
    for y, B in enumerate(dkz_bob()):
        for j in range(3):
            for sig in itertools.permutations(range(3)):
                for cj in range(2):
                    M = np.linalg.matrix_power(Z, j) @ B[:, list(sig)]
                    if cj:
                        M = M.conj()
                    out.append((M, y, j, 0, sig, cj))
    return out


def grid_coords(Bt, tol=1e-9):
    """CKM coordinates of a copy: t12 = t23 = pi/4, t13 = asin(3^{-1/2}), (d, f1, f2) in (pi/12) Z^3; all solutions
    in [0, 2 pi)^3 matching Bt up to column phases."""
    t = np.array([math.pi / 4, math.asin(1 / math.sqrt(3)), math.pi / 4])
    ks = np.arange(24)
    D, F1, F2 = np.meshgrid(ks, ks, ks, indexing="ij")
    X = np.column_stack([np.repeat(t[None], D.size, 0), D.ravel() * PI12, F1.ravel() * PI12, F2.ravel() * PI12])
    B = C.ckm_float(X)
    ov = np.abs(np.einsum("nkb,kb->nb", B.conj(), Bt))       # |<B_b, Bt_b>| = 1 iff the columns agree up to phase
    good = np.all(ov > 1 - tol, axis=1)
    return [(int(D.ravel()[i]), int(F1.ravel()[i]), int(F2.ravel()[i])) for i in np.nonzero(good)[0]]


def relabelling(qc):
    """find (y, j, cj, sigma) with q_c[x, a, b] = q*_xy[tau_x(a), sigma(b)], tau = joint shift by -j composed with the
    conjugation map (a0 -> -a0 - 1, a1 -> -a1) if cj.  Returns the first match."""
    Q = np.array([2 * (2 + math.sqrt(3)) / 9, 2 * (2 - math.sqrt(3)) / 9, 1 / 9])
    for y in range(2):
        qs = np.array([Q[C.GLEV[x, y]] / 3 for x in range(2)])
        for cj in range(2):
            for j in range(3):
                for sig in itertools.permutations(range(3)):
                    def tau(x, a):
                        a2 = (a - j) % 3
                        if cj:
                            a2 = (-a2 - 1) % 3 if x == 0 else (-a2) % 3
                        return a2
                    err = max(abs(qc[x, a, b] - qs[x, tau(x, a), sig[b]]) for x in range(2) for a in range(3)
                              for b in range(3))
                    if err < 1e-12:
                        return y, j, cj, sig, tau
    return None


def kstar_exact(y):
    """K*_y(b | a0, a1) = P*_y(a0, a1, b) / mu*(a0, a1) as mpmath intervals, [a0][a1][b]."""
    P = [[[iv.mpf(0)] * 3 for _ in range(3)] for _ in range(3)]
    for lam, w in C.FACETS.items():
        P[lam[0]][lam[1]][lam[2 + y]] += w
    return [[[P[a0][a1][b] / C.MU_I[a0][a1] for b in range(3)] for a1 in range(3)] for a0 in range(3)]


def build(margin=0.6):
    """the copies whose coordinates lie within `margin` of the domain D (periodic translates by 2 pi included)."""
    copies = []
    seen = set()
    for (Bt, y, j, k, sig, cj) in orbit():
        for (dk, f1k, f2k) in grid_coords(Bt):
            for sd in (-24, 0, 24):
                for s1 in (-24, 0, 24):
                    for s2 in (-24, 0, 24):
                        key = (dk + sd, f1k + s1, f2k + s2)
                        xc = np.array([math.pi / 4, math.asin(1 / math.sqrt(3)), math.pi / 4,
                                       key[0] * PI12, key[1] * PI12, key[2] * PI12])
                        if np.any(xc < DOM_LO - margin) or np.any(xc > DOM_HI + margin):
                            continue
                        if key in seen:
                            continue
                        seen.add(key)
                        copies.append(key)
    return sorted(copies)


def _t13_interval():
    """rigorous interval for asin(3^{-1/2}): sin is increasing on [0, pi/2]; check sin at both ends with iv.sin."""
    m = mp.asin(1 / mp.sqrt(3))
    a, b = m - mp.mpf(10) ** -45, m + mp.mpf(10) ** -45
    t = 1 / iv.sqrt(3)
    assert iv.sin(iv.mpf(a)).b < t.a and iv.sin(iv.mpf(b)).a > t.b
    return iv.mpf([a, b])


T13 = _t13_interval()


class Copy:
    """exact data of one copy (key = (d, f1, f2) in units of pi/12)."""

    def __init__(self, key):
        self.key = key
        t13 = T13
        vals = [iv.pi / 4, t13, iv.pi / 4] + [iv.pi * kk / 12 for kk in key]
        self.x = IV(np.array([V._arb_iv(v)[0] for v in vals]), np.array([V._arb_iv(v)[1] for v in vals]))
        self.xf = self.x.mid()
        Bt = C.ckm_float(self.xf[None])[0]
        qc = C.q_float(Bt[None])[0]
        rel = relabelling(qc)
        if rel is None:
            raise RuntimeError(f"copy {key}: no relabelling found")
        y, j, cj, sig, tau = rel
        Ks = kstar_exact(y)
        lo = np.zeros((3, 3, 3))
        hi = np.zeros((3, 3, 3))
        for a0 in range(3):
            for a1 in range(3):
                for b in range(3):
                    v = Ks[tau(0, a0)][tau(1, a1)][sig[b]]
                    lo[a0, a1, b], hi[a0, a1, b] = V._arb_iv(v)
                    if v.b == 0:
                        lo[a0, a1, b] = hi[a0, a1, b] = 0.0
        self.K = IV(lo, hi)
        self.supp = hi > 0
        Kf = 0.5 * (lo + hi)
        # slope: weighted least squares on the support (float), then dyadic with exact zero b-sums
        qv, qg, _ = C.q_jets(C.bt_jets(self.xf[None], self.xf[None], point=True, hess=False))
        M = C.kernel_slope(qv.mid(), qg.mid(), Kf[None], supp_tol=0.0)
        Mq = np.round(M[0] / 2.0 ** -30) * 2.0 ** -30
        Mq = Mq.reshape(9, 3, 6)
        Mq[~self.supp.reshape(9, 3)] = 0.0
        for blk in range(9):
            sb = np.nonzero(self.supp.reshape(9, 3)[blk])[0]
            if len(sb):
                ref = sb[0]
                Mq[blk, ref] = -(Mq[blk].sum(axis=0) - Mq[blk, ref])
        assert np.all(Mq.sum(axis=1) == 0.0)
        self.M = Mq.reshape(27, 6)
        self.rel = (y, j, cj, sig)

    def check_float(self):
        """numerical sanity: g(x_c) - S0 and |grad g(x_c)| with the exact-kernel model (floats)."""
        qc = C.q_float(C.ckm_float(self.xf[None]))
        g0 = C.g_float(qc, self.K.mid()[None])[0]
        gr = []
        for i in range(6):
            e = np.zeros(6)
            e[i] = 1e-6
            vals = []
            for s in (1, -1):
                y = self.xf + s * e
                Ky = self.K.mid() + (self.M @ (s * e)).reshape(3, 3, 3)
                vals.append(C.g_float(C.q_float(C.ckm_float(y[None])), Ky[None])[0])
            gr.append((vals[0] - vals[1]) / 2e-6)
        return g0 - C.S0.mid(), np.abs(gr).max()


def star_certify(cp, lo, hi):
    """True where the star bound proves g <= S0 on the box [lo, hi] (N x 6) for the copy cp."""
    N = lo.shape[0]
    hl = np.minimum(lo, cp.x.lo[None])
    hh = np.maximum(hi, cp.x.hi[None])
    qb, _, c, h = C.box_jets(hl, hh, centre=False)
    # kernel over the hull: Kc + M (y - x_c); p at the hull centre (interval) and slopes
    off = IV(c) - IV(np.repeat(cp.x.lo[None], N, 0), np.repeat(cp.x.hi[None], N, 0))     # c - x_c
    Kc = IV(np.repeat(cp.K.lo.reshape(1, 27), N, 0), np.repeat(cp.K.hi.reshape(1, 27), N, 0))
    Mi = IV(np.repeat(cp.M[None], N, 0))
    Kcen = Kc + V.isum(Mi * off[:, None, :], axis=2)
    # nonnegativity of the kernel over the hull (supported entries; off-support entries are exactly 0)
    span = V.isum(Mi * IV(-h, h)[:, None, :], axis=2)
    Kmin = (Kcen + span).lo
    ok = np.all((Kmin >= 0) | ~cp.supp.reshape(1, 27), axis=1)
    p_c, dp = C.p_model(Kcen.reshape(N, 3, 3, 3), np.repeat(cp.M[None], N, 0))
    p_b = p_c + V.isum(dp * IV(-h, h)[:, None, :], axis=2)
    qv = qb[0]
    allgood = np.all(qv.lo > 0, axis=1) & np.all(p_b.lo > 0, axis=1)
    ok &= allgood
    mask = np.ones((N, 18), dtype=bool)
    Hs = C.hessian_enclosure(qb, IV(np.where(p_b.lo > 0, p_b.lo, 1.0), np.where(p_b.lo > 0, p_b.hi, 1.0)), dp, mask)
    negH_lo = np.zeros((N, 6, 6))
    negH_hi = np.zeros((N, 6, 6))
    negH_lo[:, C.TI, C.TJ] = -Hs.hi
    negH_hi[:, C.TI, C.TJ] = -Hs.lo
    negH_lo[:, C.TJ, C.TI] = -Hs.hi
    negH_hi[:, C.TJ, C.TI] = -Hs.lo
    ok &= V.chol_pd(IV(negH_lo, negH_hi))
    return ok


if __name__ == "__main__":
    print("base q check (max error):", base_check())
    keys = build()
    print(f"{len(keys)} copies within the margin of D; keys (d, f1, f2) in units of pi/12:")
    print(keys)
    for key in keys[:6]:
        cp = Copy(key)
        e0, eg = cp.check_float()
        print(f"copy {key}: rel {cp.rel}; g(x_c) - S0 = {e0:+.2e}, |grad g| = {eg:.2e}; supp size {cp.supp.sum()}")


def star3(cp, rho):
    """certified radius r <= rho (sup norm in CKM coordinates) such that g < S0 on 0 < |y - x_c|_inf <= r.
    Uses g(x_c) = S0, grad g(x_c) = 0 (exact), Hessian at x_c (interval), third derivatives over the cube:
      g(x_c + t) <= S0 - (lam/2)|t|^2 + K |t|_inf^3,  K = (1/6) sum_{ordered ijk} |D3g_ijk|,
    with lam a certified lower bound for the smallest eigenvalue of -H(x_c).  Returns (r, lam, K, checks)."""
    import nash_core3 as T3
    # Hessian (and value, gradient as sanity checks) at the exact centre (an interval of width ~1e-16)
    xl, xh = cp.x.lo[None], cp.x.hi[None]
    Kc = IV(cp.K.lo.reshape(1, 3, 3, 3), cp.K.hi.reshape(1, 3, 3, 3))
    ub, parts = T3.box_bound3(xl, xh, None, cp.M[None], Kint=Kc, return_parts=True)
    H = T3.full_from_packed(parts["H"])
    F, G = parts["F"], parts["G"]
    checks = dict(F_contains_S0=bool(F.lo[0] <= C.S0.hi and C.S0.lo <= F.hi[0]),
                  G_max_abs=float(G.mag().max()), good=int(parts["good"][0]))
    lam_f = np.linalg.eigvalsh(-H.mid()[0])[0]
    lam = 0.98 * lam_f
    A = IV(-H.hi, -H.lo)
    dd = np.arange(6)
    A.lo[:, dd, dd] = V.dn(-H.hi[:, dd, dd] - lam)
    A.hi[:, dd, dd] = V.up(-H.lo[:, dd, dd] - lam)
    ok, _ = T3.chol(A)
    if not ok[0]:
        return 0.0, lam, np.inf, checks
    # third derivatives over the cube, kernel model anchored at x_c
    lo = cp.x.lo[None] - rho
    hi = cp.x.hi[None] + rho
    c, h = C.box_geometry(lo, hi)
    off = IV(c) - IV(cp.x.lo[None], cp.x.hi[None])
    Kcen = IV(cp.K.lo.reshape(1, 27), cp.K.hi.reshape(1, 27)) + V.isum(IV(cp.M[None]) * off[:, None, :], axis=2)
    span = V.isum(IV(cp.M[None]) * IV(-h, h)[:, None, :], axis=2)
    knn = bool(np.all(((Kcen + span).lo >= 0) | ~cp.supp.reshape(1, 27)))
    ub2, p2 = T3.box_bound3(lo, hi, None, cp.M[None], Kint=Kcen.reshape(1, 3, 3, 3), return_parts=True)
    if p2["good"][0] < 18 or not knn:
        return 0.0, lam, np.inf, checks
    Kc3 = float(V.isum(IV(p2["T"].mag()) * IV(T3.MULT / 6.0), axis=1).hi[0])
    r = min(rho, 0.999 * lam / (2 * Kc3))
    return r, lam, Kc3, checks
