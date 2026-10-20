"""certify_pa2.py -- rigorous (computer-assisted) upper bound for Lemma PA2 at a given k.

PA2(k): for orthonormal k-families {alpha_{x,a}}, {phi_{y,b}} (x, y in {0,1}) in any Hilbert space,
    S = sum c_k[x,y,a,b] |<alpha_{x,a}|phi_{y,b}>|^2 <= k I_ME(k).
Method (see dual_sdp.py): level-2 trace relaxation over the words {letters} u {A_x B_y, B_y A_x}, reduced by the global
outcome shift into k Hermitian sectors M_s(y) = C_s + sum_c y_c E_{s,c}.  Every PA2 configuration gives (after
averaging over shifts and complex conjugation, which keeps S) moments y with M_s(y) >= 0, |y_c| <= 1 (traces of products
of rank-one projections) and sum_s Tr M_s(y) <= k n (n = 4 + 8k words per sector).  For ANY Hermitian Z_s with
Z_s + mu I >= 0:
    S = b.y = D(Z) + r.y - sum_s Re Tr(Z_s M_s(y)) <= D(Z) + sum_c |r_c| + mu k n,
D(Z) = sum_s Re Tr(Z_s C_s),  r_c = b_c + sum_s Re Tr(Z_s E_{s,c}).
Z_s = numerical dual rounded to dyadics (exact); D, r in mpmath interval arithmetic (cyclotomic phases); Z_s + mu I >= 0
by interval Cholesky of the real embedding.  Output: rigorous S_max <= bound, compared with k I_ME(k) (interval).
usage: python certify_pa2.py k [mu]"""
import sys, os, time, itertools
from fractions import Fraction
import numpy as np
import mpmath
from mpmath import iv
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import dual_sdp as DS
from trace_sdp import cglmp_tensor, reduce_cyc
from trace_sdp_sym import canon_shift

iv.prec = 200


def ime_iv(k):
    """I_ME(k) = 4/(k(k-1)) sum_{j=1}^{k-1} (k-j)/cos(pi j/(2k)), in interval arithmetic."""
    s = iv.mpf(0)
    for j in range(1, k):
        s += iv.mpf(k - j) / iv.cos(iv.pi * j / (2 * k))
    return 4 * s / (k * (k - 1))


def interval_cholesky_ok(A):
    """A: list of lists of iv.mpf (symmetric).  Returns True if the interval Cholesky succeeds (=> A positive definite)."""
    n = len(A); L = [[iv.mpf(0)] * n for _ in range(n)]
    for j in range(n):
        s = A[j][j]
        for p in range(j):
            s -= L[j][p] * L[j][p]
        if not (s.a > 0):
            return False, j
        L[j][j] = iv.sqrt(s)
        for i in range(j + 1, n):
            t = A[i][j]
            for p in range(j):
                t -= L[i][p] * L[j][p]
            L[i][j] = t / L[j][j]
    return True, n


def main(k, mu_exp=-26, grid=40, clip=False, tight=False, scs=False, scs_iters=100000):
    t0 = time.time()
    opts = dict(tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11, max_iter=400) if tight else None
    if scs:
        opts = dict(solver='SCS', eps_abs=1e-10, eps_rel=1e-10, max_iters=scs_iters, acceleration_lookback=20)
    reps, Zs, cls, code = DS.solve(k, opts=opts)
    if clip:
        cl = []
        for Z in Zs:
            Z = np.array(Z, dtype=complex); Z = (Z + Z.conj().T) / 2
            w, V = np.linalg.eigh(Z); cl.append((V * np.maximum(w, 0)) @ V.conj().T)
        Zs = cl
    n = len(reps); ncls = len(cls)
    Cr = cglmp_tensor(k)
    # exact CGLMP coefficients (rationals with denominator k-1)
    b = [Fraction(0)] * ncls
    for x, y, a, bb in itertools.product(range(2), range(2), range(k), range(k)):
        c = Fraction(round(Cr[x, y, a, bb] * (k - 1)), k - 1)
        b[cls[canon_shift(reduce_cyc(((x, a), (2 + y, bb))), k)]] += c
    scale = 2 ** grid
    # rounded dyadic duals (exactly Hermitian)
    Zq = []
    for Z in Zs:
        Z = np.array(Z, dtype=complex); Z = (Z + Z.conj().T) / 2
        Re = np.round(Z.real * scale).astype(np.int64); Im = np.round(Z.imag * scale).astype(np.int64)
        # exact symmetry / antisymmetry: take the lower triangle and reflect it (no integer-division asymmetry)
        Re = np.tril(Re) + np.tril(Re, -1).T
        Im = np.tril(Im, -1); Im = Im - Im.T
        assert (Re == Re.T).all() and (Im == -Im.T).all()
        Zq.append((Re, Im))
    om = [[(iv.cos(2 * iv.pi * s * r / k), iv.sin(2 * iv.pi * s * r / k)) for r in range(k)] for s in range(k)]
    # D(Z) and residuals: Re Tr(Z E) = sum_{i,j,r: code[i,j,r]=c} Re(Z[j,i] om^{s r})
    D = iv.mpf(0); res = [iv.mpf(b[c].numerator) / b[c].denominator for c in range(ncls)]
    for s in range(k):
        Re, Im = Zq[s]
        for i in range(n):
            for j in range(n):
                zr = Re[j, i]; zi = Im[j, i]
                if zr == 0 and zi == 0: continue
                for r in range(k):
                    c = code[i, j, r]
                    if c == -1: continue
                    cr, sr = om[s][r]
                    val = (iv.mpf(int(zr)) * cr - iv.mpf(int(zi)) * sr) / scale
                    if c == -2: D += val
                    else: res[c] += val
    rsum = iv.mpf(0)
    for c in range(ncls):
        rsum += abs(res[c])
    # PSD of Z_s + mu I via interval Cholesky of the real embedding [[Re, -Im],[Im, Re]]; try mu = 2^mu_exp, then
    # larger mu (factor 2^4 each step) until every sector passes
    for mexp in range(mu_exp, -9, 4):
        mu = iv.mpf(2) ** mexp
        ok_all = True
        for s in range(k):
            Re, Im = Zq[s]
            R = np.block([[Re, -Im], [Im, Re]])
            A = [[iv.mpf(int(R[i, j])) / scale + (mu if i == j else 0) for j in range(2 * n)] for i in range(2 * n)]
            ok, piv = interval_cholesky_ok(A)
            if not ok:
                print(f"k={k}: sector {s}: interval Cholesky failed at pivot {piv} with mu = 2^{mexp}; trying larger mu",
                      flush=True)
                ok_all = False
                break
        if ok_all:
            mu_exp = mexp
            break
    else:
        print(f"k={k}: FAILED for every mu"); return None
    bound = D + rsum + mu * k * n
    target = k * ime_iv(k)
    f = lambda z: mpmath.nstr(mpmath.mpf(z), 15)
    print(f"k={k}: RIGOROUS  S <= {f(bound.b)}   (D(Z) <= {f(D.b)}, sum|r| <= {mpmath.nstr(mpmath.mpf(rsum.b), 3)}, "
          f"mu = 2^{mu_exp}, mu k n = {mpmath.nstr(mpmath.mpf((mu * k * n).b), 3)});  k I_ME(k) >= {f(target.a)};  "
          f"excess <= {mpmath.nstr(mpmath.mpf((bound - target).b), 3)}   ({time.time() - t0:.0f}s)", flush=True)
    return bound, target


if __name__ == '__main__':
    k = int(sys.argv[1]); mu_exp = int(sys.argv[2]) if len(sys.argv) > 2 else -26
    flags = sys.argv[3] if len(sys.argv) > 3 else ''
    main(k, mu_exp, clip='clip' in flags, tight='tight' in flags, scs='scs' in flags,
         scs_iters=int(sys.argv[4]) if len(sys.argv) > 4 else 100000)
