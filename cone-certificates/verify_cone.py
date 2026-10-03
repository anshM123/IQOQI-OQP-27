"""Rigorous (interval-arithmetic) verification of CONE_d:  v in cone{u^ell : ell rational cells}.

Statement verified for a given d (QD2-R1):  there are rational cell vectors ell^(1..K) (ell_r = n_r/q, n_r >= 1, sum_r n_r = d q) and
lambda_k > 0 with  sum_k lambda_k u^{ell^(k)} = v,  u^ell_m = Delta^2_m (1/d) sum_r Ghat(S_r(m)),  v_m = 2 csc(pi m/2d)  (m = 1..d-1).

Rigour: every Clausen value Cl2(pi k/Kg) (Kg = 2 d q) is enclosed by the series
     Cl2(t) = t - t log t + sum_{n=1}^{n0} c_n t^{2n+1} + tail,   c_n = |B_2n| / (2n (2n+1)!)  (exact rationals),
     0 <= tail <= t (pi^2/6) 4^{-(n0+1)} / ((1 - 1/4)(n0+1)(2n0+3))    for 0 < t <= pi
(c_n = zeta(2n) / (n (2n+1) (2 pi)^{2n}) <= zeta(2)/(n(2n+1)(2pi)^{2n}), and (t/2pi)^{2n} <= 4^{-n}); all arithmetic in mpmath.iv
(outward rounding).  Ghat(j/q) = -(N^2/2pi^2)[Cl2(pi j/Kg) + Cl2(pi (Kg-j)/Kg)], N = 4d.  The linear system is solved approximately,
then the exact solution is enclosed by the standard residual bound |lam - lam~|_inf <= |R res|_inf / (1 - |I - R U|_inf).
Usage:  python verify_cone.py d q ncols seed  [--save]
"""
import sys, time, json
import numpy as np
from fractions import Fraction
import mpmath
from mpmath import iv, mp
from scipy.optimize import linprog

PREC = 160
iv.prec = PREC
mp.prec = PREC


def bern_coeffs(n0):
    cs = []
    fact = Fraction(1)
    for n in range(1, n0 + 1):
        p, qq = mpmath.bernfrac(2 * n)
        B = Fraction(int(p), int(qq))
        f = Fraction(1)
        for k in range(2, 2 * n + 2):
            f *= k                                   # (2n+1)!
        cs.append(abs(B) / (2 * n * f))
    return cs


N0 = 70
CN = bern_coeffs(N0)
CN_IV = [iv.mpf(c.numerator) / iv.mpf(c.denominator) for c in CN]


def cl2_iv(t):
    """enclosure of Cl2(t) for an interval 0 < t <= pi."""
    t2 = t * t
    s = t - t * iv.log(t)
    pw = t * t2
    for c in CN_IV:
        s += c * pw
        pw *= t2
    tail_hi = t * (iv.pi ** 2 / 6) * iv.mpf(4) ** (-(N0 + 1)) / (iv.mpf(3) / 4 * (N0 + 1) * (2 * N0 + 3))
    return s + iv.mpf([0, 1]) * tail_hi


def cl2_grid(Kg):
    out = [iv.mpf(0)]
    for k in range(1, Kg):
        out.append(cl2_iv(iv.pi * k / Kg))
    out.append(iv.mpf(0))                            # Cl2(pi) = 0 exactly
    return out


def ghat_grid(d, q):
    Kg = 2 * d * q
    N = 4 * d
    cl = cl2_grid(Kg)
    pref = -(iv.mpf(N) ** 2) / (2 * iv.pi ** 2)
    return [pref * (cl[j] + cl[Kg - j]) for j in range(d * q + 1)]


# ------------------------------------------------------------------ float side (column search)
def cl2_float(t):
    from scipy.special import spence
    z = np.exp(1j * np.asarray(t, float))
    return np.imag(spence(1 - z))


def ghat_float_grid(d, q):
    Kg = 2 * d * q
    N = 4 * d
    k = np.arange(Kg + 1)
    cl = cl2_float(np.pi * k / Kg)
    cl[0] = 0.0
    cl[-1] = 0.0
    j = np.arange(d * q + 1)
    return -(N ** 2 / (2 * np.pi ** 2)) * (cl[j] + cl[Kg - j])


def window_index(nvec):
    d = len(nvec)
    ext = np.concatenate([nvec, nvec])
    cs = np.concatenate([[0], np.cumsum(ext)])
    r = np.arange(d)[:, None]
    m = np.arange(d + 1)[None, :]
    return cs[r + m] - cs[r]                          # J_r(m), integers in [0, d q]


def u_float(nvec, gg):
    J = window_index(nvec)
    P = gg[J].mean(axis=0)
    return P[2:] - 2 * P[1:-1] + P[:-2]


def u_iv(nvec, giv):
    d = len(nvec)
    J = window_index(nvec)
    P = []
    for m in range(d + 1):
        s = iv.mpf(0)
        for r in range(d):
            s += giv[int(J[r, m])]
        P.append(s / d)
    return [P[m + 1] - 2 * P[m] + P[m - 1] for m in range(1, d)]


def v_iv(d):
    return [2 / iv.sin(iv.pi * m / (2 * d)) for m in range(1, d)]


def random_cells(d, q, rng, alpha):
    ell = rng.dirichlet(np.ones(d) * alpha) * d
    n = np.maximum(1, np.round(ell * q).astype(int))
    diff = d * q - n.sum()
    while diff != 0:                                  # fix the sum, keep n >= 1
        i = int(rng.integers(d))
        if diff > 0:
            n[i] += 1; diff -= 1
        elif n[i] > 1:
            n[i] -= 1; diff += 1
    return n


def find_columns(d, q, ncols, rng, gg, v):
    cols, ns = [], []
    for k in range(ncols):
        alpha = 1.0 if k % 4 else float(np.exp(rng.uniform(np.log(0.3), np.log(3))))
        n = random_cells(d, q, rng, alpha)
        ns.append(n)
        cols.append(u_float(n, gg))
    U = np.array(cols).T
    sc = 1 / v
    A = U * sc[:, None]
    b = v * sc
    K = U.shape[1]
    res = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K, method='highs')
    if res.status != 0:
        return None
    # maximise the minimal weight on the support of a few vertex solutions
    supp = set(np.where(res.x > 1e-12)[0])
    for t in range(6):
        cvec = rng.uniform(0, 1, K)
        r2 = linprog(cvec, A_eq=A, b_eq=b, bounds=[(0, None)] * K, method='highs')
        if r2.status == 0:
            supp |= set(np.where(r2.x > 1e-12)[0])
    S = sorted(supp)
    AS = A[:, S]
    nS = len(S)
    # variables (lam_S, t): max t  s.t. AS lam = b, lam_k - t * (b-scale) >= 0
    c = np.zeros(nS + 1); c[-1] = -1
    Aub = np.hstack([-np.eye(nS), np.ones((nS, 1))])
    r3 = linprog(c, A_ub=Aub, b_ub=np.zeros(nS), A_eq=np.hstack([AS, np.zeros((d - 1, 1))]), b_eq=b,
                 bounds=[(0, None)] * nS + [(0, None)], method='highs')
    lam = r3.x[:nS]
    return [ns[i] for i in S], lam, r3.x[-1]


def verify(d, nlist, lam_f, giv):
    """interval verification: v = U lam with lam > 0, U columns = u^{ell} (ell = n/q).  Uses the minimum-norm correction
    lam = lam~ + U^T y, (U U^T) y = res, res = v - U lam~."""
    K = len(nlist)
    Ucols = [u_iv(n, giv) for n in nlist]
    V = v_iv(d)
    lam_t = [iv.mpf(mpmath.mpf(float(x))) for x in lam_f]
    # residual res = v - U lam~ (intervals)
    res = []
    for m in range(d - 1):
        s = V[m]
        for k in range(K):
            s -= Ucols[k][m] * lam_t[k]
        res.append(s)
    # W = U U^T (interval), solve W y = res with approximate inverse
    W = iv.matrix(d - 1, d - 1)
    for i in range(d - 1):
        for j in range(i, d - 1):
            s = iv.mpf(0)
            for k in range(K):
                s += Ucols[k][i] * Ucols[k][j]
            W[i, j] = s
            W[j, i] = s
    Wmid = mp.matrix(d - 1, d - 1)
    for i in range(d - 1):
        for j in range(d - 1):
            Wmid[i, j] = W[i, j].mid
    R = mp.inverse(Wmid)
    Riv = iv.matrix(R.tolist())
    E = iv.eye(d - 1) - Riv * W
    # upper bound of |I - R W|_inf (all sums done in interval arithmetic, upper endpoints taken)
    normE = max((sum((abs(E[i, j]) for j in range(d - 1)), iv.mpf(0))).b for i in range(d - 1))
    if not (normE < 1):
        return False, f"|I - RW| = {flo(normE):.3e} >= 1"
    resv = iv.matrix([[x] for x in res])
    Rr = Riv * resv
    bound_y = (max(abs(Rr[i, 0]).b for i in range(d - 1)) / (1 - normE)).b
    # lam = lam~ + U^T y ; |U^T y|_k <= sum_m |U_mk| |y|_inf
    worst = None
    for k in range(K):
        colabs = sum((abs(Ucols[k][m]) for m in range(d - 1)), iv.mpf(0)).b
        lo = (lam_t[k] - colabs * bound_y).a
        worst = lo if worst is None else min(worst, lo)
    return bool(worst > 0), f"min certified lambda >= {flo(worst):.4e} (|y| <= {flo(bound_y):.2e}, |I-RW| <= {flo(normE):.2e}, K = {K})"


def flo(p):
    """float of a point interval (or the lower endpoint of an interval)."""
    return float(mpmath.mpf(p.a))


if __name__ == "__main__":
    d = int(sys.argv[1]); q = int(sys.argv[2]); ncols = int(sys.argv[3]); seed = int(sys.argv[4])
    save = '--save' in sys.argv
    rng = np.random.default_rng(seed)
    t0 = time.time()
    gg = ghat_float_grid(d, q)
    v = np.array([2 / np.sin(np.pi * m / (2 * d)) for m in range(1, d)])
    out = find_columns(d, q, ncols, rng, gg, v)
    if out is None:
        print(f"d={d}: float LP infeasible with {ncols} columns"); sys.exit(1)
    nlist, lam_f, tmin = out
    print(f"d={d} q={q}: float LP: support {len(nlist)}, min lambda (scaled) {tmin:.3e} [{time.time()-t0:.0f}s]", flush=True)
    giv = ghat_grid(d, q)
    # consistency of the interval grid with the float grid
    dev = max(abs(float(giv[j].mid) - gg[j]) for j in range(0, d * q + 1, max(1, d * q // 50)))
    print(f"   interval vs float Ghat grid: max |mid - float| = {dev:.2e}; max width = {max(float(x.delta) for x in giv):.2e} [{time.time()-t0:.0f}s]", flush=True)
    # rescale lambda from the row-scaled LP to the true system: LP solved A lam = b with A = U/v, b = 1 -> same lam
    ok, msg = verify(d, nlist, lam_f, giv)
    print(f"   VERIFIED: {ok}  {msg}  [{time.time()-t0:.0f}s]", flush=True)
    if save and ok:
        with open(f"cert_d{d}.json", "w") as fh:
            json.dump(dict(d=d, q=q, cells=[[int(x) for x in n] for n in nlist], lam=[float(x) for x in lam_f]), fh)
