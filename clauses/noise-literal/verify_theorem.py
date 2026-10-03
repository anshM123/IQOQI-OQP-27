"""
verify_theorem.py -- single entry point that re-checks every computational step of THEOREM.md.
All decisions use exact rational / Q(sqrt2) / sympy-radical arithmetic or rigorous rational interval enclosures;
items marked [sanity] use floating point and are informational only (never used in a proof).

Core theorem (Theorem 1):
  C1  L(2,2,3): exact double description -> 1116 facets = 36 positivity + 648 lifted CHSH + 432 CGLMP_3 (orbit)
  C2  competitor PVMs on Phi_d (d = 4..9): exact projectors, ranks, behaviour = closed form
  C3  coarse-grained CHSH: local bound 2 (all deterministic strategies, d = 4..9); exact witness thresholds;
      symbolic derivation of v_even(d), v_odd(d)
  C4  reduction Lemma R: p_v = kappa(a) kappa(b) q_v(pi a, pi b) exactly (d = 4..9, symbolic v)
  C5  competitor's exact critical visibility for all d >= 3: Bernstein certificates G_F(t) >= 0 on [0,1/3] for all
      1116 facets (Q(sqrt2)), + per-d exact re-check d = 3..12
  C5b facet-free cross-check of C5: explicit 17-strategy local models (exact, d = 2..40 / 3..16)
  C6  1/2-lemma: explicit two-model construction checked exactly on random rational behaviours (d = 2..5)
  C7  [sanity] DKZ closed form vs explicit bases; CGLMP value I_ME(d)
  C8  DKZ local-model certificates d = 3..20 (exact rationals + rigorous sin enclosures + absorption lemma)
  C8b tightness 2/I_ME(d) - v0(d) < 1.02e-7, d = 3..20 (rigorous enclosure of I_ME)
  C9  comparison: v_comp(d) < 1/2 for even d >= 10 / odd d >= 11 (exact, all real d beyond 9 resp. 10);
      for d = 4..9: v_comp(d) < explicit rational r(d) <= v0(d) (exact)
  C10 [sanity] full (2,2,d) LP critical visibilities (HiGHS) for competitor d = 4,5,6 and DKZ d = 4,5
  C11 exact v_c(DKZ_d) = 2/I_ME(d) for d = 3, 4, 5 (dkz_exact.py)
Supplements:
  S1  Theorem 3 (d = 3 on Phi_3, all PVMs): exact facet-class data, thresholds, I_3(DKZ_3) in radicals (phi3.py)
  S2  Phi_2 counterexample for d = 3 (exact value and comparison)
  S3  POVM version with full-rank effects, all d >= 4 (exact); PVMs on Phi_D using all outcomes (povm.py)
  S4  [numerical] ledger B1 search summary (logs/white_d*_D*.log)

usage: python verify_theorem.py            (about 3 minutes)
"""
import itertools
import json
import os
import random
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.chdir(HERE)

from exact import Q2, Poly  # noqa: E402

RESULTS = []


def item(name, ok, info=""):
    RESULTS.append((name, bool(ok)))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  -- {info}" if info else ""), flush=True)


SQ2 = Q2(0, 1)


def v_even(d):
    return Q2(4 * (d - 1)) / ((SQ2 - 1) * (d * d) + 4 * (d - 1))


def v_odd(d):
    return Q2(4) / ((SQ2 - 1) * d + 4)


def v_comp(d):
    return v_even(d) if d % 2 == 0 else v_odd(d)


# ------------------------------------------------------------------------------------------------------------------
def c1():
    import facets223 as F
    t0 = time.time()
    V = [F.cg_vertex(s) for s in F.strategies()]
    A = [[1] + v for v in V]
    ok_dim = F.int_rank(A) == F.NCG + 1
    rays = F.double_description(A, verbose=False)
    Fs = set(F.normalise(list(r)) for r in rays)
    ok_facets = all(F.check_facet(h, V)[0] for h in Fs)
    # second, independent run with a different (reversed) insertion order must give the same set
    rays2 = F.double_description(A, order=list(range(len(A)))[::-1], verbose=False)
    Fs2 = set(F.normalise(list(r)) for r in rays2)
    pos, chsh, cgl = F.positivity_ineqs(), F.chsh_lifted_ineqs(), F.cglmp_orbit()
    U = pos | chsh | cgl
    stored = set()
    for line in open("facets223.txt"):
        if not line.startswith("#"):
            stored.add(tuple(int(t) for t in line.split(";")[0].split()))
    ok = ok_dim and ok_facets and Fs == Fs2 == U == stored and len(Fs) == 1116
    item("C1 L(2,2,3) complete facet list (exact double description, two insertion orders)", ok,
         f"{len(Fs)} facets = {len(pos)} positivity + {len(chsh)} lifted CHSH + {len(cgl)} CGLMP; "
         f"matches facets223.txt: {Fs == stored}; {time.time() - t0:.1f}s")


# ------------------------------------------------------------------------------------------------------------------
def competitor_pvms(d):
    """exact sympy matrices: P[x][a], Q[y][b] (d x d)."""
    import sympy as sp
    sz = sp.Matrix([[1, 0], [0, -1]])
    sx = sp.Matrix([[0, 1], [1, 0]])
    I2 = sp.eye(2)
    A = [sz, sx]
    B = [(sz + sx) / sp.sqrt(2), (sz - sx) / sp.sqrt(2)]
    Z = sp.zeros(d, d)

    def lift(M, extra):
        if d % 2 == 0:
            return sp.kronecker_product(M, sp.eye(d // 2))
        k = (d - 1) // 2
        R = sp.zeros(d, d)
        for j in range(k):
            R[2 * j:2 * j + 2, 2 * j:2 * j + 2] = M
        R[d - 1, d - 1] = extra
        return R
    P = [[lift((I2 + A[x]) / 2, 1), lift((I2 - A[x]) / 2, 0)] + [Z] * (d - 2) for x in range(2)]
    Q = [[lift((I2 + B[y]) / 2, 1), lift((I2 - B[y]) / 2, 0)] + [Z] * (d - 2) for y in range(2)]
    return P, Q


def phi_d_matrix_lift(d):
    """for even d the tensor identification C^2 (x) C^{d/2} = C^d via |i>|j> -> |i d/2 + j> keeps Phi_d =
    Phi_2 (x) Phi_{d/2} (both are sum_k |kk>/sqrt d); kronecker_product uses exactly this ordering."""
    return True


def c2():
    import sympy as sp
    ok = True
    info = []
    for d in range(4, 10):
        P, Q = competitor_pvms(d)
        for M in (P, Q):
            for x in range(2):
                S = sp.zeros(d, d)
                for a in range(d):
                    Pa = M[x][a]
                    ok &= sp.simplify(Pa * Pa - Pa) == sp.zeros(d, d) and Pa.T.conjugate() == Pa
                    S += Pa
                ok &= sp.simplify(S - sp.eye(d)) == sp.zeros(d, d)
                ranks = [M[x][a].rank(simplify=True) for a in range(d)]
                want = [d // 2, d // 2] + [0] * (d - 2) if d % 2 == 0 else [(d + 1) // 2, (d - 1) // 2] + [0] * (d - 2)
                ok &= ranks == want
        s = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
        for x in range(2):
            for y in range(2):
                for a in range(d):
                    for b in range(d):
                        val = sp.nsimplify(sp.simplify((P[x][a].T * Q[y][b]).trace() / d))
                        chsh = (1 + (1 if a == b else -1) * s[(x, y)] / sp.sqrt(2)) / 4 if a < 2 and b < 2 else 0
                        if d % 2 == 0:
                            want = chsh
                        else:
                            want = sp.Rational(d - 1, d) * chsh + (sp.Rational(1, d) if a == 0 and b == 0 else 0)
                        ok &= sp.simplify(val - want) == 0
        info.append(str(d))
    item("C2 competitor PVMs on Phi_d: projectors, ranks, exact behaviour (d = " + ",".join(info) + ")", ok,
         "even: CHSH on {0,1}^2; odd: (d-1)/d CHSH + (1/d) delta_{a=b=0}")


# ------------------------------------------------------------------------------------------------------------------
def c3():
    import sympy as sp
    ok = True
    s = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    # local bound 2 of the coarse-grained CHSH: any deterministic strategy gives A_x, B_y in {+-1}
    for d in range(4, 10):
        mx = max(sum(s[(x, y)] * (1 if st[x] == 0 else -1) * (1 if st[2 + y] == 0 else -1)
                     for x in range(2) for y in range(2)) for st in itertools.product(range(d), repeat=4))
        ok &= mx == 2
    # values and thresholds, symbolic in d
    dd = sp.symbols("d", positive=True)
    r2 = sp.sqrt(2)
    e = (2 - dd) / dd                                   # mean of the binarised uniform outcome
    chsh_u = 2 * e ** 2                                 # (1 + 1 + 1 - 1) e^2
    chsh_even = 2 * r2
    chsh_odd = (dd - 1) / dd * 2 * r2 + 2 / dd          # deterministic part contributes 2
    ve = sp.simplify((2 - chsh_u) / (chsh_even - chsh_u) - 4 * (dd - 1) / ((r2 - 1) * dd ** 2 + 4 * (dd - 1)))
    vo = sp.simplify((2 - chsh_u) / (chsh_odd - chsh_u) - 4 / ((r2 - 1) * dd + 4))
    ok &= ve == 0 and vo == 0
    # exact CHSH value of the competitor behaviours from C2's closed form, d = 4..9
    for d in range(4, 10):
        tot = 0
        for x in range(2):
            for y in range(2):
                for a in range(2):
                    for b in range(2):
                        pr = (1 + (1 if a == b else -1) * s[(x, y)] / r2) / 4
                        if d % 2:
                            pr = sp.Rational(d - 1, d) * pr + (sp.Rational(1, d) if a == b == 0 else 0)
                        tot += s[(x, y)] * (1 if a == 0 else -1) * (1 if b == 0 else -1) * pr
                # outcomes >= 2 have probability 0 in the competitor
        want = chsh_even if d % 2 == 0 else chsh_odd.subs(dd, d)
        ok &= sp.simplify(tot - want) == 0
    item("C3 coarse-grained CHSH: local bound 2; CHSH(comp) = 2sqrt2 (even), (d-1)/d 2sqrt2 + 2/d (odd); "
         "CHSH(u) = 2(d-2)^2/d^2; thresholds = v_even, v_odd (symbolic)", ok)


# ------------------------------------------------------------------------------------------------------------------
def c4():
    import sympy as sp
    v = sp.symbols("v")
    ok = True
    s = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    for d in range(4, 10):
        def p(a, b, x, y):
            if a >= 2 or b >= 2:
                return 0
            pr = (1 + (1 if a == b else -1) * s[(x, y)] / sp.sqrt(2)) / 4
            if d % 2:
                pr = sp.Rational(d - 1, d) * pr + (sp.Rational(1, d) if a == b == 0 else 0)
            return pr

        def pv(a, b, x, y):
            return v * p(a, b, x, y) + (1 - v) / d ** 2
        pi = lambda a: a if a < 2 else 2
        kap = lambda a: 1 if a < 2 else sp.Rational(1, d - 2)
        for x in range(2):
            for y in range(2):
                q = {}
                for a in range(d):
                    for b in range(d):
                        q[(pi(a), pi(b))] = q.get((pi(a), pi(b)), 0) + pv(a, b, x, y)
                for a in range(d):
                    for b in range(d):
                        ok &= sp.expand(pv(a, b, x, y) - kap(a) * kap(b) * q[(pi(a), pi(b))]) == 0
                # coarse-grained noise = product of (1/d, 1/d, (d-2)/d)
                m = [sp.Rational(1, d), sp.Rational(1, d), sp.Rational(d - 2, d)]
                for al in range(3):
                    for be in range(3):
                        qa = q[(al, be)]
                        pq = sum(p(a, b, x, y) for a in range(d) for b in range(d) if pi(a) == al and pi(b) == be)
                        ok &= sp.expand(qa - v * pq - (1 - v) * m[al] * m[be]) == 0
    item("C4 reduction Lemma R: p_v(a,b|x,y) = kappa(a) kappa(b) q_v(pi a, pi b|x,y), q_v = v q + (1-v) n_{1/d} "
         "(exact, symbolic v, d = 4..9)", ok)


# ------------------------------------------------------------------------------------------------------------------
def c5():
    import io
    import contextlib
    import competitor
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        ok1 = competitor.run(verbose=True)
        ok2 = competitor.per_d_check(12)
    lines = [l for l in buf.getvalue().splitlines() if l.startswith("[")]
    for l in lines:
        print("      " + l)
    item("C5 competitor critical visibility = v_even(d) / v_odd(d) EXACTLY for all d >= 3 (all 1116 G_F >= 0 on "
         "t in [0,1/3], Bernstein in Q(sqrt2)); per-d exact re-check d = 3..12", ok1 and ok2)


def c5b():
    """facet-free cross-checks of Proposition 5: (i) the explicit 17-strategy flag model of REF_noise_B sec. 2.4 at
    v = T(1/d) = v_even(d), exact for d = 2..40; (ii) exact LP-vertex local models in Q(sqrt2) at v* for both
    constructions, d = 3..16."""
    import io
    import contextlib
    import competitor_model as CM
    ok1 = CM.check_flag_model(40)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        ok2 = all(CM.run(d) for d in range(3, 17))
    item("C5b facet-free check of Prop. 5: explicit flag model (REF_noise_B 2.4) exact for d = 2..40; exact "
         "Q(sqrt2) local models at v* for d = 3..16 (17 strategies)", ok1 and ok2)


# ------------------------------------------------------------------------------------------------------------------
def c6():
    """1/2-lemma: P1 = p_00 (x) p_11 (independent), P2 = p_01 (x) p_10; (P1+P2)/2 has link marginals (p+u)/2."""
    rng = random.Random(7)
    ok = True
    for d in range(2, 6):
        for trial in range(3):
            # random behaviour with uniform marginals: each link = (1/d) * random doubly stochastic matrix
            # (rational convex combination of permutation matrices; Birkhoff)
            p = {}
            for x in range(2):
                for y in range(2):
                    M = [[Fr(0)] * d for _ in range(d)]
                    ws = [Fr(rng.randint(1, 9)) for _ in range(4)]
                    tot = sum(ws)
                    for w in ws:
                        perm = list(range(d))
                        rng.shuffle(perm)
                        for a in range(d):
                            M[a][perm[a]] += w / tot / d
                    p[(x, y)] = M
            J = {}
            for a0, a1, b0, b1 in itertools.product(range(d), repeat=4):
                J[(a0, a1, b0, b1)] = (p[(0, 0)][a0][b0] * p[(1, 1)][a1][b1] + p[(0, 1)][a0][b1] * p[(1, 0)][a1][b0]) / 2
            ok &= sum(J.values()) == 1 and min(J.values()) >= 0
            for x in range(2):
                for y in range(2):
                    for a in range(d):
                        for b in range(d):
                            m = sum(w for k, w in J.items() if k[x] == a and k[2 + y] == b)
                            ok &= m == (p[(x, y)][a][b] + Fr(1, d * d)) / 2
    item("C6 1/2-lemma: explicit local model of (p+u)/2 verified exactly on random rational behaviours with uniform "
         "marginals (d = 2..5)", ok)


# ------------------------------------------------------------------------------------------------------------------
def c7():
    import numpy as np
    sys.path.insert(0, HERE)
    from facets223 import cglmp_beta
    ok = True
    info = []
    for d in range(4, 10):
        k = np.arange(d)
        w = np.exp(2j * np.pi / d)
        al, be = [0, 0.5], [-0.25, 0.25]
        A = [np.array([w ** (k * (a + al[x])) / np.sqrt(d) for a in range(d)]).T for x in range(2)]
        B = [np.array([w ** (-k * (b + be[y])) / np.sqrt(d) for b in range(d)]).T for y in range(2)]
        delta = {(0, 0): 0.25, (0, 1): -0.25, (1, 0): 0.75, (1, 1): 0.25}
        err = 0
        p = np.zeros((2, 2, d, d))
        for x in range(2):
            for y in range(2):
                p[x, y] = np.abs(A[x].T @ B[y]) ** 2 / d
                for a in range(d):
                    for b in range(d):
                        err = max(err, abs(p[x, y, a, b] - 1 / (2 * d ** 3 * np.sin(np.pi * (b - a - delta[(x, y)]) / d) ** 2)))
        bt = cglmp_beta(d)
        I = sum(float(bt[x][y][a][b]) * p[x, y, a, b] for x in range(2) for y in range(2) for a in range(d) for b in range(d))
        j = np.arange(1, d)
        ime = 4 / (d * (d - 1)) * np.sum((d - j) / np.cos(np.pi * j / (2 * d)))
        ok &= err < 1e-12 and abs(I - ime) < 1e-12
        info.append(f"d={d}: |closed form - bases| {err:.1e}, I - I_ME {I - ime:.1e}")
    item("C7 [sanity] DKZ closed form p = 1/(2d^3 sin^2(pi(b-a-delta_xy)/d)) and CGLMP value I_ME(d) (float)", ok,
         "; ".join(info[:2]) + " ...")


# ------------------------------------------------------------------------------------------------------------------
def c8():
    import dkz_cert
    ok = True
    vals = {}
    for d in range(3, 21):
        good, v0 = dkz_cert.check(d, verbose=True)
        ok &= good
        vals[d] = v0
    item("C8 DKZ local-model certificates d = 3..20 (exact rationals, rigorous sin enclosures, absorption lemma): "
         "v_c(DKZ_d) >= v0(d)  [Theorem 1 uses d = 4..9]", ok)
    return vals


def c8b():
    """tightness: 2/I_ME(d) - v0(d) < 1.02e-7 for d = 3..20, with a rigorous enclosure of I_ME(d)
    (sec(pi j/(2d)) = 1/cos, cos(pi r) = sin(pi(1/2 - r)) enclosed as in exact.py)."""
    from exact import cos_pi_frac_bounds
    ok = True
    worst = Fr(0)
    for d in range(3, 21):
        lo = hi = Fr(0)
        for j in range(1, d):
            c_lo, c_hi = cos_pi_frac_bounds(Fr(j, 2 * d))
            lo += (d - j) / c_hi
            hi += (d - j) / c_lo
        ime_lo, ime_hi = Fr(4, d * (d - 1)) * lo, Fr(4, d * (d - 1)) * hi
        v0 = Fr(*json.load(open(os.path.join(HERE, "certificates", f"dkz_d{d}.json")))["v0"])
        gap_hi = 2 / ime_lo - v0
        ok &= gap_hi < Fr(102, 10 ** 9) and v0 < 2 / ime_lo
        worst = max(worst, gap_hi)
    item("C8b tightness: v0(d) <= v_c(DKZ_d) <= 2/I_ME(d) with 2/I_ME(d) - v0(d) < 1.02e-7 for d = 3..20 "
         "(rigorous enclosure of I_ME)", ok,
         f"max gap {float(worst):.4e}")


# ------------------------------------------------------------------------------------------------------------------
R_D = {4: Fr(69, 100), 5: Fr(687, 1000), 6: Fr(684, 1000), 7: Fr(683, 1000), 8: Fr(682, 1000), 9: Fr(681, 1000)}


def c9(v0s):
    ok = True
    # (i) v_even(d) < 1/2  <=>  (sqrt2 - 1) d^2 - 4 d + 4 > 0 : holds at d = 9 and the left side increases for d >= 5
    f = lambda d: (SQ2 - 1) * (d * d) - 4 * d + 4
    ok &= f(9).sign() > 0 and f(8).sign() < 0 and ((SQ2 - 1) * 2 * 5 - 4).sign() > 0
    # v_odd(d) < 1/2  <=>  (sqrt2 - 1) d > 4 : holds at d = 10 (hence all d >= 10), fails at d = 9
    g = lambda d: (SQ2 - 1) * d - 4
    ok &= g(10).sign() > 0 and g(9).sign() < 0
    # direct exact evaluation for the record
    ok &= all(v_even(d) < Q2(Fr(1, 2)) for d in range(10, 41, 2)) and all(v_odd(d) < Q2(Fr(1, 2)) for d in range(11, 41, 2))
    ok &= v_even(8) > Q2(Fr(1, 2)) and v_odd(9) > Q2(Fr(1, 2))
    # (ii) d = 4..9 : v_comp(d) < r(d) <= v0(d)
    lines = []
    for d in range(4, 10):
        good = v_comp(d) < Q2(R_D[d]) and R_D[d] <= v0s[d]
        ok &= good
        lines.append(f"d={d}: v_comp = {float(v_comp(d)):.6f} < r = {R_D[d]} <= v0 = {float(v0s[d]):.9f}")
    for l in lines:
        print("      " + l)
    item("C9 comparison: competitor threshold < 1/2 <= v_c(DKZ) for even d >= 10 and odd d >= 11 (exact; fails at "
         "d = 8, 9 as stated); d = 4..9: v_comp(d) < r(d) <= v0(d) (exact)", ok)


# ------------------------------------------------------------------------------------------------------------------
def c10():
    import numpy as np
    from scipy.optimize import linprog

    def lp_vc(p):
        d = p.shape[2]
        S = list(itertools.product(range(d), repeat=4))
        E = np.zeros((len(S), 4 * d * d))
        for i, s in enumerate(S):
            for x in range(2):
                for y in range(2):
                    E[i, ((x * 2 + y) * d + s[x]) * d + s[2 + y]] = 1
        pf = p.reshape(-1)
        nf = np.full_like(pf, 1 / d ** 2)
        Aeq = np.hstack([E.T, -(pf - nf)[:, None]])
        c = np.zeros(len(S) + 1)
        c[-1] = -1
        r = linprog(c, A_eq=Aeq, b_eq=nf, bounds=[(0, None)] * len(S) + [(None, None)], method="highs")
        return r.x[-1]
    ok = True
    info = []
    s = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    for d in (4, 5, 6):
        p = np.zeros((2, 2, d, d))
        for x in range(2):
            for y in range(2):
                for a in range(2):
                    for b in range(2):
                        p[x, y, a, b] = (1 + (1 if a == b else -1) * s[(x, y)] / np.sqrt(2)) / 4
                if d % 2:
                    p[x, y] *= (d - 1) / d
                    p[x, y, 0, 0] += 1 / d
        v = lp_vc(p)
        ok &= abs(v - float(v_comp(d))) < 1e-7
        info.append(f"comp d={d}: LP {v:.9f} vs {float(v_comp(d)):.9f}")
    for d in (4, 5):
        delta = {(0, 0): 0.25, (0, 1): -0.25, (1, 0): 0.75, (1, 1): 0.25}
        p = np.zeros((2, 2, d, d))
        for x in range(2):
            for y in range(2):
                for a in range(d):
                    for b in range(d):
                        p[x, y, a, b] = 1 / (2 * d ** 3 * np.sin(np.pi * (b - a - delta[(x, y)]) / d) ** 2)
        v = lp_vc(p)
        j = np.arange(1, d)
        ime = 4 / (d * (d - 1)) * np.sum((d - j) / np.cos(np.pi * j / (2 * d)))
        ok &= abs(v - 2 / ime) < 1e-7
        info.append(f"DKZ d={d}: LP {v:.9f} vs 2/I_ME {2 / ime:.9f}")
    item("C10 [sanity] full (2,2,d) LP critical visibilities (float, informational)", ok, "; ".join(info))


def c11():
    import io
    import contextlib
    import dkz_exact
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        ok = all(dkz_exact.run(d) for d in (3, 4, 5))
    for l in buf.getvalue().splitlines():
        print("      " + l.strip()[:150])
    item("C11 Proposition 11: v_c(DKZ_d) = 2/I_ME(d) EXACTLY for d = 3, 4, 5 (exact facets of K_d; arithmetic in "
         "Q(cos(pi/4d)))", ok)


# ------------------------------------------------------------------------------------------------------------------
# Supplements
# ------------------------------------------------------------------------------------------------------------------
def s1_s2():
    import io
    import contextlib
    import phi3
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        ok = phi3.run()
    for l in buf.getvalue().splitlines():
        print("      " + l)
    item("S1 Theorem 3 (d = 3 on Phi_3): facet classes, CHSH_F(u) = +-2/9, I_F(u) = 0, 2/I_ME(3) = 3sqrt3 - 9/2 < "
         "4/(3sqrt2+1), I_3(DKZ_3) = (12+8sqrt3)/9 (radicals)", ok)
    # S2: Phi_2 value 8/(9 sqrt2 - 1) = v_even-formula at d = 3 and it is the exact v_c (C5 covers q = CH at t = 1/3)
    ok2 = v_even(3) == Q2(8) / (9 * SQ2 - 1)
    r2lo, r3lo = Fr(14142135623, 10 ** 10), Fr(17320508075, 10 ** 10)
    ok2 &= (Fr(8) / (9 * r2lo - 1)) < 3 * r3lo - Fr(9, 2)
    item("S2 Phi_2, d = 3: v_c = 8/(9 sqrt2 - 1) = 0.682133 (exact, = Prop. 5 at t = 1/3) < 2/I_ME(3); odd D >= 17 "
         "block bound (in S1 output)", ok and ok2)


def s3():
    import io
    import contextlib
    import povm
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        ok = povm.run()
        res = povm.pvm_all_outcomes()
    for l in buf.getvalue().splitlines():
        print("      " + l)
    ok &= sorted(res) == list(range(4, 10))
    print("      PVMs on Phi_D using all outcomes beat v0(DKZ_d) at (d, D) = " +
          ", ".join(f"({d}, {res[d][1]})" for d in sorted(res)))
    item("S3 POVMs M = (1-eps)P + (eps/d)1, 0 < eps <= 1/100 (all effects full rank): v_c < v_c(DKZ_d) for all "
         "d >= 4 (exact); Remark S3c (PVMs on Phi_D, all outcomes used) for d = 4..9", ok)


def s4():
    """B1 is NUMERICAL: summarise the search logs (informational)."""
    import glob
    import re
    worst = -1.0
    n = 0
    for fn in sorted(glob.glob(os.path.join(HERE, "logs", "white_d*_D*.log"))):
        for line in open(fn):
            m = re.match(r"RESULT d=(\d+) D=(\d+): max F over survivors = ([0-9.]+)", line)
            if m:
                n += 1
                worst = max(worst, float(m.group(3)))
    ok = n > 0 and worst < 2
    item("S4 [numerical] ledger B1: no rank pattern with F = v* I + (1-v*) I(n) > 2 in the search logs", ok,
         f"{n} (d, D) cases, largest F = {worst:.6f}")


if __name__ == "__main__":
    t0 = time.time()
    c1()
    c2()
    c3()
    c4()
    c5()
    c5b()
    c6()
    c7()
    v0s = c8()
    c8b()
    c9(v0s)
    c10()
    c11()
    s1_s2()
    s3()
    s4()
    print("-" * 100)
    n_fail = sum(1 for _, ok in RESULTS if not ok)
    print(f"{len(RESULTS)} items, {n_fail} failures, {time.time() - t0:.0f}s")
    print("OVERALL:", "PASS" if n_fail == 0 else "FAIL")
    sys.exit(0 if n_fail == 0 else 1)
