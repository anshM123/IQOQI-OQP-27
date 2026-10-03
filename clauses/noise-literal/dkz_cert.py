"""
dkz_cert.py -- rigorous LOWER bounds on the critical visibility of the DKZ strategy against the whole local polytope
(Gill noise u), Theorem 2 of THEOREM.md.

DKZ_d on Phi_d (alpha = (0, 1/2), beta = (-1/4, 1/4)):  p(a,b|x,y) = h_xy(b - a)/d,
    h_xy(m) = 1 / (2 d^2 sin^2(pi (m - delta_xy)/d)),   delta = (delta00, delta01, delta10, delta11) = (1/4, -1/4, 3/4, 1/4),
which maximises the CGLMP expression of the mathematical paper (papers/math, eq. (1)) (I = I_ME(d)).  Gill noise: T^v_xy(m) = v h_xy(m) + (1 - v)/d.

Covariant lemma: a Z_d-covariant behaviour P_xy(b-a)/d is local if there is a probability mu on
    {(m00, m01, m10, m11) in Z_d^4 : m00 - m01 - m10 + m11 = 0 mod d}
whose four one-dimensional marginals are P_00, P_01, P_10, P_11.
Absorption lemma: if Q is such a (rational, exactly local) marginal family and, for some 0 < v0 < v1,
    |Q_xy(m) - T^{v1}_xy(m)| <= (v1 - v0) / (2 d v0)      for all x, y, m,
then T^{v0} is local (T^{v0} = (v0/v1) Q + (1 - v0/v1) (S + U)/2 with S = U + 2 kappa (T^{v1} - Q) >= 0,
kappa = v0/(v1 - v0), and (S + U)/2 local by the 1/2-lemma).

Modes:
  python dkz_cert.py make  d1 d2 ...     LP (HiGHS) + rational rounding -> certificates/dkz_d{d}.json
  python dkz_cert.py check d1 d2 ...     exact verification (Fractions + rigorous sin enclosures), no floats
"""
import json
import os
import sys
from fractions import Fraction as Fr

from exact import sin2_pi_bounds

DELTA = {(0, 0): Fr(1, 4), (0, 1): Fr(-1, 4), (1, 0): Fr(3, 4), (1, 1): Fr(1, 4)}
LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
CERT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certificates")


def strategies(d):
    """index set of the covariant LP: (m00, m01, m10) -> m11 = m01 + m10 - m00 mod d."""
    out = []
    for m00 in range(d):
        for m01 in range(d):
            for m10 in range(d):
                out.append((m00, m01, m10, (m01 + m10 - m00) % d))
    return out


# ------------------------------------------------------------------------------------------------------------------
# certificate generation (floating point LP; output is checked exactly afterwards)
# ------------------------------------------------------------------------------------------------------------------
def make(d, gap_v1=Fr(1, 10 ** 7), digits=16):
    import numpy as np
    from scipy.optimize import linprog

    def h(xy, m):
        return 1.0 / (2 * d * d * np.sin(np.pi * (m - float(DELTA[xy])) / d) ** 2)

    St = strategies(d)
    n = len(St)
    rows = []
    for li, xy in enumerate(LINKS):
        for m in range(d):
            rows.append([1.0 if s[li] == m else 0.0 for s in St])
    A = np.array(rows)
    hv = np.array([h(xy, m) for xy in LINKS for m in range(d)])
    print(f"d={d}: sum_m h_xy(m) - 1 = {[float(hv[i*d:(i+1)*d].sum() - 1) for i in range(4)]}")
    # maximise v : A mu - v (h - 1/d) = 1/d
    Aeq = np.hstack([A, -(hv - 1.0 / d)[:, None]])
    beq = np.full(4 * d, 1.0 / d)
    c = np.zeros(n + 1)
    c[-1] = -1
    opts = dict(primal_feasibility_tolerance=1e-10, dual_feasibility_tolerance=1e-10)
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * n + [(None, None)], method="highs", options=opts)
    vmax = res.x[-1]
    k = np.arange(1, d)
    ime = 4.0 / (d * (d - 1)) * np.sum((d - k) / np.cos(np.pi * k / (2 * d)))
    print(f"   LP max visibility {vmax:.12f}   2/I_ME = {2 / ime:.12f}")
    v1 = Fr(int((vmax - float(gap_v1)) * 10 ** 9), 10 ** 9)
    T = float(v1) * hv + (1 - float(v1)) / d
    res2 = linprog(np.zeros(n), A_eq=A, b_eq=T, bounds=[(0, None)] * n, method="highs", options=opts)
    assert res2.status == 0
    mu = np.maximum(res2.x, 0)
    # polish on the support
    S = np.nonzero(mu > 1e-13)[0]
    sol, *_ = np.linalg.lstsq(A[:, S], T, rcond=None)
    if sol.min() >= 0:
        mu = np.zeros(n)
        mu[S] = sol
    den = 10 ** digits
    num = [int(round(x * den)) for x in mu]
    tot = sum(num)
    # exact renormalisation: put the rounding defect on the largest entry
    imax = max(range(n), key=lambda i: num[i])
    num[imax] += den - tot
    assert min(num) >= 0
    err = np.abs(A @ (np.array(num, float) / den) - T).max()
    # choose v0 with comfortable margin: need err <= (v1 - v0)/(2 d v0)
    need = 2 * d * float(v1) * err
    delta_v = Fr(max(int(need * 1e12 * 20) + 1, 1), 10 ** 12)
    v0 = v1 - delta_v
    cert = dict(d=d, v1=[v1.numerator, v1.denominator], v0=[v0.numerator, v0.denominator], den=den,
                support=[[list(St[i][:3]), num[i]] for i in range(n) if num[i] > 0],
                note="mu(m00,m01,m10) = numerator/den, m11 = m01 + m10 - m00 mod d")
    os.makedirs(CERT_DIR, exist_ok=True)
    with open(os.path.join(CERT_DIR, f"dkz_d{d}.json"), "w") as f:
        json.dump(cert, f)
    print(f"   v1 = {float(v1):.12f}, float marginal error {err:.2e}, v0 = {float(v0):.12f} "
          f"(2/I_ME - v0 = {2 / ime - float(v0):.2e}); support {len(cert['support'])}")


# ------------------------------------------------------------------------------------------------------------------
# exact verification
# ------------------------------------------------------------------------------------------------------------------
def h_bounds(d, xy, m):
    """rigorous [lo, hi] for h_xy(m) = 1/(2 d^2 sin^2(pi (m - delta)/d))."""
    s_lo, s_hi = sin2_pi_bounds((Fr(m) - DELTA[xy]) / d)
    assert s_lo > 0
    return 1 / (2 * d * d * s_hi), 1 / (2 * d * d * s_lo)


def check(d, verbose=True):
    with open(os.path.join(CERT_DIR, f"dkz_d{d}.json")) as f:
        cert = json.load(f)
    assert cert["d"] == d
    v1 = Fr(*cert["v1"])
    v0 = Fr(*cert["v0"])
    den = cert["den"]
    assert 0 < v0 < v1 < 1
    Q = {xy: [Fr(0)] * d for xy in LINKS}
    tot = 0
    seen = set()
    for (m00, m01, m10), num in cert["support"]:
        assert num > 0 and 0 <= m00 < d and 0 <= m01 < d and 0 <= m10 < d
        assert (m00, m01, m10) not in seen
        seen.add((m00, m01, m10))
        m11 = (m01 + m10 - m00) % d
        w = Fr(num, den)
        tot += num
        for xy, m in zip(LINKS, (m00, m01, m10, m11)):
            Q[xy][m] += w
    assert tot == den, "mu must be a probability distribution"
    tol = (v1 - v0) / (2 * d * v0)
    worst = Fr(0)
    for xy in LINKS:
        for m in range(d):
            lo, hi = h_bounds(d, xy, m)
            Tlo = v1 * lo + (1 - v1) / d
            Thi = v1 * hi + (1 - v1) / d
            e = max(abs(Q[xy][m] - Tlo), abs(Q[xy][m] - Thi))
            worst = max(worst, e)
    ok = worst <= tol
    if verbose:
        print(f"  d={d}: mu >= 0, sum mu = 1 (support {len(seen)}); max |Q - T^v1| <= {float(worst):.3e} "
              f"<= (v1 - v0)/(2 d v0) = {float(tol):.3e}: {'OK' if ok else 'FAIL'}  =>  v_c(DKZ_{d}) >= v0 = "
              f"{float(v0):.12f}")
    return ok, v0


if __name__ == "__main__":
    mode = sys.argv[1]
    ds = [int(t) for t in sys.argv[2:]]
    if mode == "make":
        for d in ds:
            make(d)
    else:
        allok = True
        for d in ds:
            ok, _ = check(d)
            allok &= ok
        print("RESULT:", "PASS" if allok else "FAIL")
