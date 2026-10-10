"""
verify_local.py -- INDEPENDENT checker for CLAIM_d (Theorem LOC), using only Python Fractions:
rigorous rational enclosures of pi (Machin) and of sin (alternating Taylor series with remainder bounds),
exact rational linear algebra, no mpmath, no floating point in any decision.

CLAIM_d:  Q = (1/kappa) G + (1-1/kappa) U  is a strictly positive combination of the partition generators
          g_pi = (1/4) sum_i delta_{pi_i}  (pi = partitions of d-1 into <= 4 parts),
where G(n) = 1/(2 d^2 sin^2(pi (4n+1)/(4d))), kappa = I/2, I = 4 - 8 mean(G)/(d-1).
The candidate weights are produced by a float LP (cert_local.py logic) -- only as DATA; the check is exact:
  non-basic weights are fixed positive rationals; basic weights = exact M_B^{-1} (rhs) with rhs an exact
  rational INTERVAL vector; positivity of every basic weight interval is checked in exact arithmetic.
Also checks (exactly, d <= dmax_facet): the CGLMP functional beta = sum_i n_i >= d-1 is a facet of L
(affine rank of its tight deterministic points = dim L - 1), and (float sanity) that the DKZ unitaries of
core.dkz give adapted link laws equal to G.
usage: python verify_local.py d_min d_max [dmax_facet]
"""
import sys
import itertools
from fractions import Fraction as Fr
import numpy as np


# ------------------------------------------------------------------ rigorous rational enclosures
SCALE = 10 ** 80


def rdown(x):
    """largest k/SCALE <= x (outward rounding keeps every enclosure valid)."""
    return Fr((x.numerator * SCALE) // x.denominator, SCALE)


def rup(x):
    return Fr(-((-x.numerator * SCALE) // x.denominator), SCALE)

def arctan_inv(k, terms):
    """enclosure of arctan(1/k) by the alternating series; returns (lo, hi)."""
    s = Fr(0)
    x = Fr(1, k)
    p = x
    for n in range(terms):
        t = p / (2 * n + 1)
        s += t if n % 2 == 0 else -t
        p *= x * x
    nxt = p / (2 * terms + 1)          # first omitted term magnitude
    if terms % 2 == 0:                 # next term positive
        return s, s + nxt
    return s - nxt, s


def pi_enclosure(terms=60):
    a_lo, a_hi = arctan_inv(5, terms)
    b_lo, b_hi = arctan_inv(239, terms)
    return rdown(16 * a_lo - 4 * b_hi), rup(16 * a_hi - 4 * b_lo)     # pi = 16 atan(1/5) - 4 atan(1/239)


def sin_enclosure(xlo, xhi, terms=30):
    """enclosure of sin on [xlo, xhi] subset [0, pi/2] (sin increasing there): Taylor with remainder."""
    def sin_bounds(x):
        s = Fr(0)
        p = x
        f = 1
        for n in range(terms):
            t = p / f
            s += t if n % 2 == 0 else -t
            p *= x * x
            f *= (2 * n + 2) * (2 * n + 3)
        rem = p / f                       # |remainder| <= next term (alternating, decreasing for x <= 1.6)
        return rdown(s - rem), rup(s + rem)
    lo, _ = sin_bounds(rdown(xlo))
    _, hi = sin_bounds(rup(xhi))
    return lo, hi


def Q_enclosure(d):
    pl, ph = pi_enclosure()
    G = []
    for n in range(d):
        # argument t = pi (4n+1)/(4d) in (0, pi); use sin(t) = sin(pi - t) to map into [0, pi/2]
        num = 4 * n + 1
        den = 4 * d
        if 2 * num <= den:                 # t <= pi/2
            lo, hi = pl * num / den, ph * num / den
        else:                              # use pi - t = pi (den - num)/den
            lo, hi = pl * (den - num) / den, ph * (den - num) / den
        slo, shi = sin_enclosure(lo, hi)
        assert slo > 0
        G.append((rdown(1 / (2 * d * d * shi * shi)), rup(1 / (2 * d * d * slo * slo))))
    mG_lo = sum(n * G[n][0] for n in range(d))
    mG_hi = sum(n * G[n][1] for n in range(d))
    I_lo = 4 - 8 * mG_hi / (d - 1)
    I_hi = 4 - 8 * mG_lo / (d - 1)
    k_lo, k_hi = rdown(I_lo / 2), rup(I_hi / 2)
    # Q(n) = G(n)/kappa + (1 - 1/kappa)/d  -- monotone in G (increasing) and in kappa: d/dk = -(G - 1/d)/k^2
    Q = []
    for n in range(d):
        cands = []
        for g in G[n]:
            for k in (k_lo, k_hi):
                cands.append(g / k + (1 - 1 / k) / d)
        Q.append((rdown(min(cands)), rup(max(cands))))
    return Q, (I_lo, I_hi), G


def partitions4(total):
    out = []
    for a in range(total, -1, -1):
        for b in range(min(a, total - a), -1, -1):
            for c in range(min(b, total - a - b), -1, -1):
                e = total - a - b - c
                if 0 <= e <= c:
                    out.append((a, b, c, e))
    return out


def exact_inverse(M):
    n = len(M)
    A = [[Fr(x) for x in row] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]


def candidate_weights(d):
    """float LP (data only)."""
    from scipy.optimize import linprog
    parts = partitions4(d - 1)
    k = len(parts)
    Gm = np.zeros((d, k))
    for j, p in enumerate(parts):
        for t in p:
            Gm[t, j] += 0.25
    n = np.arange(d)
    G = 1.0 / (2 * d * d * np.sin(np.pi * (4 * n + 1) / (4 * d)) ** 2)
    I = 4 - 8 * (n @ G) / (d - 1)
    Qf = G / (I / 2) + (1 - 2 / I) / d
    Aeq = np.hstack([Gm, np.zeros((d, 1))])
    Aub = np.hstack([-np.eye(k), np.ones((k, 1))])
    c = np.zeros(k + 1); c[-1] = -1
    r = linprog(c, A_ub=Aub, b_ub=np.zeros(k), A_eq=Aeq, b_eq=Qf, bounds=[(0, None)] * k + [(None, 1)],
                method="highs")
    return parts, r.x[:k], r.x[-1]


def check_claim(d):
    parts, w, eps = candidate_weights(d)
    k = len(parts)
    gen = [[Fr(sum(1 for t in p if t == m), 4) for m in range(d)] for p in parts]
    # basis selection (exact rank via Fractions, greedy by weight)
    rows = list(range(1, d))
    order = sorted(range(k), key=lambda j: -w[j])
    basis = []
    for j in order:
        trial = basis + [j]
        M = [[gen[jj][r] for jj in trial] for r in rows]
        # exact column rank
        A = [row[:] for row in M]
        rank = 0
        ncol = len(trial)
        for cidx in range(ncol):
            piv = next((r for r in range(rank, len(A)) if A[r][cidx] != 0), None)
            if piv is None:
                continue
            A[rank], A[piv] = A[piv], A[rank]
            for r in range(len(A)):
                if r != rank and A[r][cidx] != 0:
                    f = A[r][cidx] / A[rank][cidx]
                    A[r] = [x - f * y for x, y in zip(A[r], A[rank])]
            rank += 1
        if rank == len(trial):
            basis = trial
            if len(basis) == d - 1:
                break
    assert len(basis) == d - 1
    nonb = [j for j in range(k) if j not in basis]
    wt = {j: Fr(max(int(round(max(w[j], eps / 2) * 10 ** 12)), 1), 10 ** 12) for j in nonb}
    MB = [[gen[j][r] for j in basis] for r in rows]
    MBinv = exact_inverse(MB)
    Q, Ienc, _ = Q_enclosure(d)
    rlo, rhi = [], []
    for r in rows:
        s = sum(gen[j][r] * wt[j] for j in nonb)
        rlo.append(Q[r][0] - s)
        rhi.append(Q[r][1] - s)
    ok = True
    minw = None
    for i in range(d - 1):
        lo = Fr(0)
        for t in range(d - 1):
            c = MBinv[i][t]
            lo += c * (rlo[t] if c > 0 else rhi[t])
        ok &= lo > 0
        minw = lo if minw is None else min(minw, lo)
    ok &= all(v > 0 for v in wt.values())
    return ok, float(minw), (float(Ienc[0]), float(Ienc[1]))


def check_facet(d):
    """exact affine rank of the tight set of beta = sum_i n_i (adapted variables) in CG coordinates."""
    from facet_lib import Scenario, affine_rank
    sc = Scenario(d)
    tight = []
    for idx, (a0, a1, b0, b1) in enumerate(sc.lams):
        n = [(b0 - a0) % d, (a0 - b1) % d, (a1 - b0) % d, (b1 - a1 + d - 1) % d]
        s = sum(n)
        assert s % d == d - 1
        if s == d - 1:
            tight.append(idx)
    r = affine_rank(sc.V[tight].tolist())
    return len(tight), r, sc.dim


def check_dkz_laws(d):
    from core import dkz
    p = dkz(d)
    n = np.arange(d)
    G = 1.0 / (2 * d * d * np.sin(np.pi * (4 * n + 1) / (4 * d)) ** 2)
    laws = np.zeros((4, d))
    for a in range(d):
        for b in range(d):
            for i, (x, y, val) in enumerate([(0, 0, (b - a) % d), (0, 1, (a - b) % d),
                                              (1, 0, (a - b) % d), (1, 1, (b - a + d - 1) % d)]):
                # link i: (x,y) and adapted variable value; n1=b0-a0 (00), n2=a0-b1 (01), n3=a1-b0 (10), n4=b1-a1+d-1
                laws[i, val] += p[x, y, a, b]
    return float(np.max(np.abs(laws - G[None, :])))


if __name__ == "__main__":
    d0, d1 = int(sys.argv[1]), int(sys.argv[2])
    dfac = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    allok = True
    for d in range(d0, d1 + 1):
        ok, minw, Ienc = check_claim(d)
        dev = check_dkz_laws(d)
        line = (f"d={d:3d}: CLAIM_d {'VERIFIED' if ok else 'FAILED'} (min basic weight >= {minw:.3e}); "
                f"I(DKZ) in [{Ienc[0]:.12f}, {Ienc[1]:.12f}]; DKZ adapted link laws = G up to {dev:.1e}")
        if d <= dfac:
            nt, r, dim = check_facet(d)
            line += f"; CGLMP tight set {nt}, affine rank {r} (facet iff {dim - 1})"
            ok &= (r == dim - 1)
        allok &= ok
        print(line, flush=True)
    print("ALL VERIFIED" if allok else "FAILURES")
