"""
verify_sdp_exact.py -- independent, fully exact re-certification of the tracial max-ent bounds of d4_ratios.py.

For a facet class: solve the level-2 tracial SDP (SCS), round the real-embedded dual Zr to dyadic rationals Z'
(denominator 2^K), choose a dyadic shift s, and verify EXACTLY:
  (1) Z' + s I is positive definite: fraction-free Bareiss elimination on the integer matrix 2^K (Z' + s I);
      positive definite iff every leading principal minor is > 0;
  (2) residuals r_t = <Z', Emb(F_t)> + c_t (exact rationals);
  bound:  beta_ME <= c0 + tr(Z') + sum_t |r_t| + 2 N s     (|t_r| <= 1 for traces of unitary words).
No floating-point quantity enters the final inequality.
usage: python verify_sdp_exact.py classes_pickle class_index[,index...] [K=36] [eps=1e-6] [max_iters=20000]
"""
import sys
import time
import pickle
from fractions import Fraction
import numpy as np
from facet_lib import Scenario, Facet
from sdp_tracial import TracialSDP, objective_from_full
from core import i_me


def bareiss_pd(M):
    """M: list of lists of python ints (symmetric).  True iff all leading principal minors > 0."""
    n = len(M)
    A = [row[:] for row in M]
    prev = 1
    for k in range(n):
        piv = A[k][k]
        if piv <= 0:
            return False, k
        for i in range(k + 1, n):
            Ai = A[i]
            Ak = A[k]
            aik = Ai[k]
            for j in range(k + 1, n):
                Ai[j] = (Ai[j] * piv - aik * Ak[j]) // prev
        prev = piv
    return True, n


def run_one(fvec, ci, K, eps, maxit):
    d = 4
    sc = Scenario(d)
    F = Facet(sc, fvec)
    C, h0 = sc.full_coeffs(F.f)
    Cint = np.array(C, dtype=object)
    bu = Fraction(int(sum(Cint.reshape(-1))), d * d)
    gap = Fraction(h0) - bu
    S = TracialSDP(d, level=2)
    hd = objective_from_full(Cint, d)
    t0 = time.time()
    val, tt, Zr, st = S.solve(hd, eps=eps, max_iters=maxit)
    N = S.N
    N2 = 2 * N
    Zs = (Zr + Zr.T) / 2
    scale = 2 ** K
    Zi = np.round(Zs * scale).astype(object)          # integer matrix = 2^K Z'
    Zi = [[int(Zi[i, j]) for j in range(N2)] for i in range(N2)]
    for i in range(N2):                                 # enforce exact symmetry
        for j in range(i):
            Zi[i][j] = Zi[j][i]
    lam_min = float(np.linalg.eigvalsh(Zs).min())
    # dyadic shift, generous: covers -lambda_min(Zs) and the rounding of Zs to the 2^-K grid (<= N2 2^-K)
    s = Fraction(int((max(-lam_min, 0) * 4 + 1e-8) * scale) + 4 * N2, scale)
    Mi = [row[:] for row in Zi]
    for i in range(N2):
        Mi[i][i] += int(s * scale)
    t1 = time.time()
    pd, k = bareiss_pd(Mi)
    t2 = time.time()
    # exact residuals with Z' = Zi / 2^K
    c0, c = S.objective_vector(hd)
    c0 = Fraction(c0)
    c = [Fraction(x) for x in c]
    acc = [Fraction(0)] * len(S.rvars)
    tr = Fraction(0)
    for i in range(N):
        for j in range(N):
            cst, terms = S.entry_terms(i, j)
            zre = Fraction(Zi[i][j] + Zi[N + i][N + j], scale)
            zim = Fraction(Zi[N + i][j] - Zi[i][N + j], scale)
            if cst != 0:
                tr += zre * Fraction(np.real(cst))
            for (t, cf) in terms:
                acc[t] += zre * Fraction(np.real(cf)) + zim * Fraction(np.imag(cf))
    resid = sum(abs(acc[t] + c[t]) for t in range(len(S.rvars)))
    ub = c0 + tr + resid + 2 * N * s
    ratio_ub = (ub - bu) / gap
    kappa = i_me(d) / 2
    kappa_lo = Fraction(1448121609, 10 ** 9)      # rigorous lower bound: kappa_4 = 1.44812160922935...
    print(f"class {ci}: SDP value {val:.10f} ({st}); exact PD check of Z'+sI: {pd} (shift s = {float(s):.3e}, "
          f"Bareiss {t2 - t1:.0f}s); residual sum {float(resid):.3e}; exact UB = {float(ub):.10f}; "
          f"ratio UB = {float(ratio_ub):.10f} vs kappa_4 = {kappa:.10f} -> "
          f"{'BELOW kappa_4' if pd and ratio_ub < kappa_lo else 'not below'}", flush=True)


if __name__ == "__main__":
    path = sys.argv[1]
    cis = [int(x) for x in sys.argv[2].split(",")]
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 36
    eps = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-6
    maxit = int(sys.argv[5]) if len(sys.argv) > 5 else 20000
    data = pickle.load(open(path, "rb"))
    flist = data["f"] if isinstance(data, dict) else [c["f"] for c in data]
    for ci in cis:
        run_one(flist[ci], ci, K, eps, maxit)

