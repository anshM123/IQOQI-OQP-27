"""
competitor.py -- exact critical visibility of the competitor strategies for ALL d (Theorem 1 of THEOREM.md).

Reduction (Lemma R): the competitor's behaviour p (on Z_d x Z_d) only uses outcomes {0,1}; under Gill's noise u the
outcomes 2..d-1 are uniformly distributed given everything else.  Hence v p + (1-v) u is local in L(2,2,d) iff its
coarse-graining {0, 1, R = {2..d-1}} is local in L(2,2,3).  The coarse-grained noise is the product behaviour n_t with
marginals (t, t, 1 - 2t), t = 1/d, and the coarse-grained quantum part is
    even d (on Phi_d = Phi_2 (x) Phi_{d/2}):           q = CHSH  (supported on {0,1}^2),
    odd d  (block construction on Phi_d):              q = (1 - t) CHSH + t delta_{0000},
    any d  (Phi_2 or Phi_{2k}, used for d = 3):        q = CHSH.
For every facet F of L(2,2,3) (facets223.py, 1116 facets, written f(x) >= 0) let
    G_F(t) = f_c(n_t) f(q_t) - f(n_t) f_c(q_t),
where f_c is the coarse-grained CHSH facet (partition {0}|{1,R} for every measurement, signs (+,+,+,-)).
With v* = f_c(n)/(f_c(n) - f_c(q)) one has f(v* q + (1-v*) n) = G_F / (f_c(n) - f_c(q)); so the point at v* is local
iff G_F >= 0 for all F.  We certify G_F(t) >= 0 on the whole interval t in [0, 1/3] (resp. [0, 1/4]) exactly
(Bernstein coefficients in Q(sqrt2)), and that f_c(q) < 0 < f_c(n) there.  Then v_c = v* exactly, and v* equals
    v_even(d) = 4(d-1)/((sqrt2-1) d^2 + 4(d-1)),     v_odd(d) = 4/((sqrt2-1) d + 4).

usage: python competitor.py
"""
import sys
from fractions import Fraction as Fr

from exact import Q2, Poly, certify_nonneg
from facets223 import IDX, NCG, ineq_from_full, zero_beta

HALF_SQRT2 = Q2(0, Fr(1, 2))         # 1/sqrt2
S = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}


def load_facets(fn="facets223.txt"):
    H, cls = [], []
    for line in open(fn):
        if line.startswith("#"):
            continue
        a, c = line.split(";")
        H.append(tuple(int(t) for t in a.split()))
        cls.append(c.strip())
    return H, cls


# ------------------------------------------------------------------------------------------------------------------
# 3-outcome behaviours with Poly entries (variable t = 1/d)
# ------------------------------------------------------------------------------------------------------------------
def behaviour_zero():
    return {(x, y, a, b): Poly.const(0) for x in range(2) for y in range(2) for a in range(3) for b in range(3)}


def chsh_behaviour():
    p = behaviour_zero()
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    p[(x, y, a, b)] = Poly.const((Q2(1) + (1 if (a + b) % 2 == 0 else -1) * S[(x, y)] * HALF_SQRT2)
                                                 * Fr(1, 4))
    return p


def det_behaviour(c):
    p = behaviour_zero()
    for x in range(2):
        for y in range(2):
            p[(x, y, c[x], c[2 + y])] = Poly.const(1)
    return p


def noise_behaviour():
    t = Poly.t()
    m = [t, t, Poly.const(1) - 2 * t]
    p = behaviour_zero()
    for x in range(2):
        for y in range(2):
            for a in range(3):
                for b in range(3):
                    p[(x, y, a, b)] = m[a] * m[b]
    return p


def mix(p, q, wp, wq):
    return {k: wp * p[k] + wq * q[k] for k in p}


def cg(p):
    v = [None] * NCG
    for x in range(2):
        for a in range(2):
            v[IDX[("A", x, a)]] = p[(x, 0, a, 0)] + p[(x, 0, a, 1)] + p[(x, 0, a, 2)]
    for y in range(2):
        for b in range(2):
            v[IDX[("B", y, b)]] = p[(0, y, 0, b)] + p[(0, y, 1, b)] + p[(0, y, 2, b)]
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    v[IDX[("AB", x, y, a, b)]] = p[(x, y, a, b)]
    return v


def facet_value(h, X):
    r = Poly.const(h[0])
    for hi, xi in zip(h[1:], X):
        if hi:
            r = r + hi * xi
    return r


def check_behaviour(p):
    """exact sanity: normalisation and no-signalling of a Poly-valued behaviour."""
    for x in range(2):
        for y in range(2):
            tot = Poly.const(0)
            for a in range(3):
                for b in range(3):
                    tot = tot + p[(x, y, a, b)]
            assert (tot - 1).is_zero()
    for x in range(2):
        for a in range(3):
            m0 = sum((p[(x, 0, a, b)] for b in range(3)), Poly.const(0))
            m1 = sum((p[(x, 1, a, b)] for b in range(3)), Poly.const(0))
            assert (m0 - m1).is_zero()
    for y in range(2):
        for b in range(3):
            m0 = sum((p[(0, y, a, b)] for a in range(3)), Poly.const(0))
            m1 = sum((p[(1, y, a, b)] for a in range(3)), Poly.const(0))
            assert (m0 - m1).is_zero()


def chsh_facet():
    """coarse-grained CHSH: A_x = +1 on outcome 0, -1 on {1, R}; sum s_xy E_xy <= 2."""
    beta = zero_beta()
    for x in range(2):
        for y in range(2):
            for a in range(3):
                for b in range(3):
                    beta[x][y][a][b] += S[(x, y)] * (1 if a == 0 else -1) * (1 if b == 0 else -1)
    return ineq_from_full(beta, 2)


def run(verbose=True):
    H, cls = load_facets()
    hc = chsh_facet()
    assert hc in H and cls[H.index(hc)] == "CHSH", "coarse-grained CHSH must be one of the facets"
    t = Poly.t()
    chsh = chsh_behaviour()
    n = noise_behaviour()
    cases = {
        "even d on Phi_d (and any d on Phi_2k): q = CHSH": (chsh, Fr(1, 3)),
        "odd d on Phi_d: q = (1-t) CHSH + t delta_0000": (mix(chsh, det_behaviour((0, 0, 0, 0)), 1 - t, t), Fr(1, 3)),
        "odd d on Phi_d: q = (1-t) CHSH + t delta_1111": (mix(chsh, det_behaviour((1, 1, 1, 1)), 1 - t, t), Fr(1, 3)),
    }
    ok_all = True
    for name, (q, tmax) in cases.items():
        check_behaviour(q)
        check_behaviour(n)
        Xq, Xn = cg(q), cg(n)
        fcq = facet_value(hc, Xq)
        fcn = facet_value(hc, Xn)
        # f_c(n) = k * 8 t (1 - t) with k > 0 (the facet is stored as a primitive integer vector, i.e. scaled
        # by a positive constant k relative to 2 - CHSH);  f_c(q) < 0 on [0, tmax]
        k = fcn.c[1] / 8
        assert k.sign() > 0 and (fcn - k * (8 * t - 8 * t * t)).is_zero()
        ok_neg, _ = certify_nonneg(-fcq - Poly.const(Fr(1, 10 ** 6)), 0, tmax)
        assert ok_neg, "f_c(q) < 0"
        # closed form of v* = fcn / (fcn - fcq)
        if "Phi_d: q = (1-t)" in name:
            # v_odd = 4 t / ((sqrt2 - 1) + 4 t)
            lhs = fcn * (Poly.const(Q2(-1, 1)) + 4 * t)
            rhs = 4 * t * (fcn - fcq)
        else:
            # v_even = 4 (t - t^2) / ((sqrt2 - 1) + 4 (t - t^2))
            lhs = fcn * (Poly.const(Q2(-1, 1)) + 4 * (t - t * t))
            rhs = 4 * (t - t * t) * (fcn - fcq)
        assert (lhs - rhs).is_zero(), "closed form of the threshold"
        nboxes = 0
        nzero = 0
        tight_classes = set()
        for h, c in zip(H, cls):
            fq = facet_value(h, Xq)
            fn = facet_value(h, Xn)
            G = fcn * fq - fn * fcq
            if G.is_zero():
                nzero += 1
                tight_classes.add(c)
                continue
            ok, nb = certify_nonneg(G, 0, tmax)
            nboxes += nb
            if not ok:
                ok_all = False
                print(f"   FAIL facet {h} ({c})")
        if verbose:
            print(f"[{name}] t in [0, {tmax}]: all 1116 G_F >= 0 certified ({nboxes} Bernstein boxes); "
                  f"G_F == 0 identically for {nzero} facets (classes {sorted(tight_classes)})", flush=True)
    return ok_all


def per_d_check(dmax=16):
    """direct exact check at each d: the noisy behaviour at v* satisfies every facet, the CHSH facet with equality."""
    H, cls = load_facets()
    hc = chsh_facet()
    ok = True
    for d in range(3, dmax + 1):
        t = Fr(1, d)
        n = {k: v(t) for k, v in noise_behaviour().items()}
        if d % 2 == 0:
            qs = [("even", {k: v(t) for k, v in chsh_behaviour().items()})]
        else:
            qd = mix(chsh_behaviour(), det_behaviour((0, 0, 0, 0)), Poly.const(1) - Poly.t(), Poly.t())
            qs = [("odd", {k: v(t) for k, v in qd.items()}), ("Phi_2", {k: v(t) for k, v in chsh_behaviour().items()})]
        for lab, q in qs:
            Xq = cg({k: Poly.const(v) for k, v in q.items()})
            Xn = cg({k: Poly.const(v) for k, v in n.items()})
            fcq = facet_value(hc, Xq)(0)
            fcn = facet_value(hc, Xn)(0)
            vstar = fcn / (fcn - fcq)
            vals = []
            for h in H:
                fq = facet_value(h, Xq)(0)
                fn = facet_value(h, Xn)(0)
                vals.append(vstar * fq + (1 - vstar) * fn)
            mn = min(vals)
            tight = sum(1 for v in vals if v == Q2(0))
            good = mn.sign() >= 0 and facet_value(hc, Xq)(0) * vstar + (1 - vstar) * fcn == Q2(0)
            ok &= good
            print(f"  d={d:2d} [{lab:5s}] v* = {float(vstar):.12f}: min facet value {float(mn):.3e}, "
                  f"{tight} tight facets  {'OK' if good else 'FAIL'}")
    return ok


if __name__ == "__main__":
    ok1 = run()
    ok2 = per_d_check()
    print("RESULT:", "PASS" if ok1 and ok2 else "FAIL")
    sys.exit(0 if ok1 and ok2 else 1)
