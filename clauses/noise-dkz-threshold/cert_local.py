"""
cert_local.py -- rigorous certificate that the DKZ critical point lies in the relative interior of the CGLMP facet
of L(2,2,d) (=> local optimality of DKZ for the full white-noise clause, see STATUS.md, Theorem LOC).

Mathematics (proof in STATUS.md):
  adapted link variables of a deterministic point (a0,a1,b0,b1):  n1 = b0-a0, n2 = a0-b1, n3 = a1-b0,
  n4 = b1-a1+d-1  (mod d, representatives in {0..d-1});  n1+n2+n3+n4 = d-1 (mod d).
  beta(p) := sum_i E_p[n_i] >= d-1 on L  (a relabelled CGLMP: I' = 4 - 2 beta/(d-1)), tight set = compositions.
  DKZ (core.dkz convention): every adapted link law equals G(n) = 1/(2 d^2 sin^2(pi(4n+1)/(4d))), n = 0..d-1.
  kappa := I(DKZ)/2 with I(DKZ) = 4 - 8 mean(G)/(d-1)  (= I_ME(d)),  Q := (1/kappa) G + (1 - 1/kappa) U.
  CLAIM_d: Q = sum_{partitions pi of d-1 into <= 4 parts} w_pi * (1/4) sum_i delta_{pi_i}  with all w_pi > 0.
  CLAIM_d  =>  q* = u + (p_DKZ - u)/kappa is a positive combination of ALL tight vertices of the CGLMP facet.

Certificate: float LP (max min-weight) -> rational weights w~ for the non-basic partitions -> exact rational
inverse of the basic (d-1)x(d-1) block (rows m = 1..d-1) -> basic weights in mpmath interval arithmetic
(outward rounding) -> check every basic weight interval is > 0.  Row m = 0 then holds exactly because
sum_m (m - (d-1)/4) (1/4) sum_i delta_{pi_i}(m) = 0 for every partition and sum_m (m-(d-1)/4) Q(m) = 0 exactly
(mean(Q) = (d-1)/4 by the definition of kappa; sum G = 1 exactly).
usage: python cert_local.py d_min d_max
"""
import sys
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
import mpmath
from mpmath import iv

iv.prec = 160
mpmath.mp.prec = 160


def ivq(F):
    """rigorous interval enclosure of a Fraction."""
    F = Fraction(F)
    return iv.mpf(F.numerator) / iv.mpf(F.denominator)


def partitions4(total):
    """multisets {n1>=n2>=n3>=n4>=0} with sum total."""
    out = []
    for a in range(total, -1, -1):
        for b in range(min(a, total - a), -1, -1):
            for c in range(min(b, total - a - b), -1, -1):
                e = total - a - b - c
                if 0 <= e <= c:
                    out.append((a, b, c, e))
    return out


def Q_interval(d):
    pi = iv.pi
    G = [1 / (2 * d * d * iv.sin(pi * (4 * n + 1) / (4 * d)) ** 2) for n in range(d)]
    mG = sum(n * G[n] for n in range(d))
    I = 4 - 8 * mG / (d - 1)
    kappa = I / 2
    Q = [G[n] / kappa + (1 - 1 / kappa) / d for n in range(d)]
    sumG = sum(G)
    return Q, I, sumG


def Q_float(d):
    n = np.arange(d)
    G = 1.0 / (2 * d * d * np.sin(np.pi * (4 * n + 1) / (4 * d)) ** 2)
    I = 4 - 8 * (n @ G) / (d - 1)
    kappa = I / 2
    return G / kappa + (1 - 1 / kappa) / d, I


def exact_inverse(M):
    n = len(M)
    A = [[Fraction(x) for x in row] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            raise ValueError("singular")
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]


def certify(d, verbose=True):
    parts = partitions4(d - 1)
    k = len(parts)
    Gm = np.zeros((d, k))
    for j, p in enumerate(parts):
        for t in p:
            Gm[t, j] += 0.25
    Qf, If = Q_float(d)
    # float LP: max eps, Gm w = Q, w >= eps  (sum w = 1 implied by row sums)
    Aeq = np.hstack([Gm, np.zeros((d, 1))])
    Aub = np.hstack([-np.eye(k), np.ones((k, 1))])
    c = np.zeros(k + 1); c[-1] = -1
    res = linprog(c, A_ub=Aub, b_ub=np.zeros(k), A_eq=Aeq, b_eq=Qf, bounds=[(0, None)] * k + [(None, 1)],
                  method="highs")
    if res.status != 0:
        return False, f"LP failed: {res.message}"
    w = res.x[:k]
    eps = res.x[-1]
    # choose a basis among partitions (rows 1..d-1) by greedy pivoting on weights (largest first)
    rows = list(range(1, d))
    order = np.argsort(-w)
    basis = []
    Mcur = np.zeros((d - 1, 0))
    for j in order:
        cand = np.hstack([Mcur, Gm[rows, j][:, None]])
        if np.linalg.matrix_rank(cand, tol=1e-10) > Mcur.shape[1]:
            Mcur = cand
            basis.append(j)
            if len(basis) == d - 1:
                break
    if len(basis) < d - 1:
        return False, "no basis"
    nonb = [j for j in range(k) if j not in set(basis)]
    # rational non-basic weights (rounded to denominators 10^12, kept >= eps/2)
    wt = {j: Fraction(int(round(max(w[j], eps / 2) * 1e12)), 10 ** 12) for j in nonb}
    MB = [[Fraction(int(round(4 * Gm[r, j])), 4) for j in basis] for r in rows]
    MBinv = exact_inverse(MB)
    Qi, Ii, sumG = Q_interval(d)
    rhs = []
    for r in rows:
        acc = Qi[r]
        for j in nonb:
            g = Gm[r, j]
            if g != 0:
                acc = acc - ivq(Fraction(int(round(4 * g)), 4) * wt[j])
        rhs.append(acc)
    wB = []
    for i in range(d - 1):
        acc = iv.mpf(0)
        for t in range(d - 1):
            if MBinv[i][t] != 0:
                acc = acc + ivq(MBinv[i][t]) * rhs[t]
        wB.append(acc)
    minB = min(x.a for x in wB)
    minN = min(wt.values()) if wt else None
    ok = all(x.a > 0 for x in wB) and (minN is None or minN > 0)
    if verbose:
        print(f"d={d:3d}: partitions {k:6d}; float eps {eps:.3e}; I(DKZ) in [{mpmath.nstr(Ii.a, 15)}, "
              f"{mpmath.nstr(Ii.b, 15)}] (float {If:.12f}); sum G - 1 in [{mpmath.nstr(sumG.a - 1, 3)}, "
              f"{mpmath.nstr(sumG.b - 1, 3)}]; min basic weight >= {mpmath.nstr(minB, 6)}; "
              f"min non-basic weight = {(f'{float(minN):.3e}' if minN is not None else 'none')}  -> CLAIM_d "
              f"{'CERTIFIED' if ok else 'NOT certified'}", flush=True)
    return ok, (eps, float(minB))


if __name__ == "__main__":
    d0, d1 = int(sys.argv[1]), int(sys.argv[2])
    allok = True
    for d in range(d0, d1 + 1):
        ok, info = certify(d)
        allok &= ok
    print("ALL CERTIFIED" if allok else "SOME FAILED")
