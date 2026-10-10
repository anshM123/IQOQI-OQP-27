"""
IND_sdp.py -- independent re-certification (2026-10-09) of the per-class max-ent ratio bounds of Theorem D4
(d = 4).  Own code (imports only IND_core / IND_expand for the facet data); different solver path (cvxpy -> SCS)
and a different exact positive-semidefiniteness certificate than verify_sdp_exact.py (which used Bareiss).

Model (derived independently, see INDEPENDENT_CHECK_D4.md Sec. 4).  For a PVM strategy on Phi_D,
p(ab|xy) = <Phi|A^x_a (x) B^y_b|Phi> = tau(P^x_a Q^y_b), tau = tr/D, P = (A)^T, Q = B: projections in ONE matrix
algebra, no commutation.  U_g = sum_a i^a P^g_a (g = 0,1: Alice x; g = 2,3: Bob y), U^4 = 1;
p(ab|xy) = 1/16 sum_{n,m} i^{-na-mb} tau(U_x^n U_{2+y}^m); balanced <=> tau(U_g^n) = 0 (n = 1,2,3).
WLOG tau(w) = tau(reverse w): the direct sum of the strategy and its transpose (dimension 2D, still balanced,
same behaviour) has symmetrised moments.  Level 2: basis W = words of length <= 2 (adjacent letters from different
generators), N = 121; M[u,v] = tau(u^* v) depends only on the dihedral class (rotation + reversal) of the cyclically
reduced word; M >= 0, M[u,u] = 1, identity class = 1, single-letter classes = 0, class(neg w) = conj class(w).
Real variables t_r = Re / Im of one representative per conjugate pair, |t_r| <= 1 (|tau(unitary)| <= 1).

Certificate.  M = M0 + sum t_r F_r (Hermitian); Emb(A) = [[Re A, -Im A], [Im A, Re A]].  For a symmetric Z' and
s >= 0 with Z' + s I >= 0:  0 <= <Z' + sI, Emb(M)> = <Z', Emb M0> + sum_r t_r <Z', Emb F_r> + 2 N s, hence with
e_r = <Z', Emb F_r> + c_r:  beta = c0 + sum c_r t_r <= c0 + <Z', Emb M0> + sum |e_r| + 2 N s  =: UB  (exact).
Z' + sI >= 0 is certified as  Z' + sI = L' L'^T + E  with L' dyadic and E symmetric, diagonally dominant with
nonnegative diagonal (all exact integers).
Objective for class j: beta_j(p) = -slack_j(p) (affine slack extended to no-signalling p); then the white-noise ratio
R_j(p) = (beta_j(p) - beta_j(u)) / (0 - beta_j(u)) = 1 + beta_j(p) / slack_j(u) <= 1 + UB / slack_j(u).
usage: python IND_sdp.py j1 j2 ... [--eps 1e-8] [--iters 100000]
"""
import sys
import time
import json
import math
from fractions import Fraction
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
import flint
from IND_core import Scen, functional_from_slack
from IND_expand import load_reps

D = 4
LETTERS = [(g, n) for g in range(4) for n in range(1, D)]


# ----------------------------------------------------------------------------- words
def red(w):
    out = []
    for (g, n) in w:
        n %= D
        if n == 0:
            continue
        if out and out[-1][0] == g:
            m = (out[-1][1] + n) % D
            out.pop()
            if m:
                out.append((g, m))
        else:
            out.append((g, n))
    return tuple(out)


def cyc_red(w):
    w = list(red(w))
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        g = w[0][0]
        m = (w[0][1] + w[-1][1]) % D
        w = w[1:-1]
        if m:
            w = [(g, m)] + w
        w = list(red(tuple(w)))
    return tuple(w)


def klass(w):
    """dihedral class (all rotations of w and of reversed w) of the cyclically reduced word."""
    c = cyc_red(w)
    if len(c) <= 1:
        return c
    cands = []
    for v in (c, tuple(reversed(c))):
        for i in range(len(v)):
            cands.append(v[i:] + v[:i])
    return min(cands)


def neg(w):
    return tuple((g, (-n) % D) for (g, n) in w)


def adjoint(w):
    return tuple((g, (-n) % D) for (g, n) in reversed(w))


def basis():
    W = [()]
    W += [(l,) for l in LETTERS]
    W += [(a, b) for a in LETTERS for b in LETTERS if a[0] != b[0]]
    return W


class Relax:
    def __init__(self):
        self.W = basis()
        N = self.N = len(self.W)
        self.cls = [[klass(adjoint(u) + v) for v in self.W] for u in self.W]
        allc = sorted({c for row in self.cls for c in row})
        self.var = {}            # class -> list of (r, coefficient) ; constant handled separately
        self.rv = []             # real variables: (class representative, 're'|'im')
        for c in allc:
            if len(c) <= 1:
                continue
            cb = klass(neg(c))
            rep = min(c, cb)
            if rep == c:
                self.rv.append((c, 're'))
                if cb != c:
                    self.rv.append((c, 'im'))
        idx = {k: i for i, k in enumerate(self.rv)}
        for c in allc:
            if len(c) <= 1:
                continue
            cb = klass(neg(c))
            if cb == c:
                self.var[c] = [(idx[(c, 're')], 1)]
            elif c < cb:
                self.var[c] = [(idx[(c, 're')], 1), (idx[(c, 'im')], 1j)]
            else:
                self.var[c] = [(idx[(cb, 're')], 1), (idx[(cb, 'im')], -1j)]
        # real embedding: Emb(M) = Emb(M0) + sum_r t_r Emb(F_r);  sparse map t -> vec_F(Emb M)
        n2 = 2 * N
        rows, cols, vals = [], [], []
        const = np.zeros(n2 * n2)
        self.F_entries = [[] for _ in self.rv]       # list of (i, j, value) in the embedding, exact ints
        self.M0_entries = []

        def put(i, j, r, v):
            if v == 0:
                return
            if r is None:
                const[j * n2 + i] += v
                self.M0_entries.append((i, j, v))
            else:
                rows.append(j * n2 + i); cols.append(r); vals.append(v)
                self.F_entries[r].append((i, j, v))
        for u in range(N):
            for v in range(N):
                c = self.cls[u][v]
                if c == ():
                    put(u, v, None, 1); put(N + u, N + v, None, 1)
                    continue
                if len(c) == 1:
                    continue
                for (r, coef) in self.var[c]:
                    re, im = int(np.real(coef)), int(np.imag(coef))
                    put(u, v, r, re); put(N + u, N + v, r, re)
                    put(N + u, v, r, im); put(u, N + v, r, -im)
        self.Amap = sp.csc_matrix((vals, (rows, cols)), shape=(n2 * n2, len(self.rv)))
        self.const = const

    def objective(self, C, cconst):
        """beta(p) = sum C[x,y,a,b] p(ab|xy) + cconst (C, cconst Fractions)  ->  c0 + sum c_r t_r (exact)."""
        c = [Fraction(0)] * len(self.rv)
        c0 = Fraction(cconst)
        ipow = [(1, 0), (0, 1), (-1, 0), (0, -1)]
        for x in range(2):
            for y in range(2):
                c0 += sum(C[x][y][a][b] for a in range(D) for b in range(D)) / 16
                for n in range(1, D):
                    for m in range(1, D):
                        hr, hi = Fraction(0), Fraction(0)
                        for a in range(D):
                            for b in range(D):
                                pr, pi = ipow[(-n * a - m * b) % 4]
                                hr += C[x][y][a][b] * pr
                                hi += C[x][y][a][b] * pi
                        hr /= 16; hi /= 16
                        k = klass(((x, n), (2 + y, m)))
                        for (r, coef) in self.var[k]:
                            # Re(h * y): y = t_re (+/-) i t_im ; Re(h (t_re + i s t_im)) = hr t_re - s hi t_im
                            if coef == 1:
                                c[r] += hr
                            else:
                                s = int(np.imag(coef))
                                c[r] += -s * hi
        return c0, c


def facet_objective(sc, s):
    """beta(p) = -slack(p) as sum C p + const with exact Fractions (my coordinates; marginals from y=0 / x=0)."""
    den, w = functional_from_slack(sc, s)          # den * slack = h0 - h.X
    h0, h = w[0], w[1:]
    C = [[[[Fraction(0)] * D for _ in range(D)] for _ in range(2)] for _ in range(2)]
    k = 0
    for x in range(2):
        for a in range(1, D):
            for b in range(D):
                C[x][0][a][b] += Fraction(h[k], den)
            k += 1
    for y in range(2):
        for b in range(1, D):
            for a in range(D):
                C[0][y][a][b] += Fraction(h[k], den)
            k += 1
    for x in range(2):
        for y in range(2):
            for a in range(1, D):
                for b in range(1, D):
                    C[x][y][a][b] += Fraction(h[k], den)
                    k += 1
    cconst = Fraction(-h0, den)
    # check: on every deterministic point, sum C p + const = -slack
    for li, lam in enumerate(sc.lams):
        v = cconst + sum(C[x][y][int(lam[x])][int(lam[2 + y])] for x in range(2) for y in range(2))
        assert v == -int(s[li])
    su = -(cconst + sum(C[x][y][a][b] for x in range(2) for y in range(2) for a in range(D) for b in range(D)) / 16)
    return C, cconst, su                             # su = slack(u) > 0


def solve(rx, c0, c, eps, iters):
    n2 = 2 * rx.N
    t = cp.Variable(len(rx.rv))
    X = cp.reshape(rx.Amap @ t + rx.const, (n2, n2), order='F')
    con = [(X + X.T) / 2 >> 0]
    obj = cp.Maximize(float(c0) + np.array([float(v) for v in c]) @ t)
    prob = cp.Problem(obj, con)
    prob.solve(solver=cp.SCS, eps_abs=eps, eps_rel=eps, max_iters=iters, verbose=False)
    Z = con[0].dual_value
    return prob.value, prob.status, np.array(Z)


def certify(rx, c0, c, Z, K=80, K2=40):
    """exact UB from the floating dual Z (symmetric 2N x 2N)."""
    n2 = 2 * rx.N
    Z = (Z + Z.T) / 2
    scale = 2 ** K
    Zi = np.array(np.round(Z * scale), dtype=object)
    for i in range(n2):
        for j in range(i):
            Zi[i, j] = Zi[j, i]
    Zi = [[int(Zi[i, j]) for j in range(n2)] for i in range(n2)]
    # residuals, exact
    e = []
    for r in range(len(rx.rv)):
        acc = Fraction(sum(Zi[i][j] * v for (i, j, v) in rx.F_entries[r]), scale)
        e.append(acc + c[r])
    trM0 = Fraction(sum(Zi[i][j] * v for (i, j, v) in rx.M0_entries), scale)
    # shift and PSD certificate
    Zf = np.array([[Zi[i][j] / scale for j in range(n2)] for i in range(n2)])
    lmin = float(np.linalg.eigvalsh(Zf).min())
    s = Fraction(int((max(-lmin, 0.0) * 2 + 1e-7) * 2 ** 40) + 1, 2 ** 40)
    L = np.linalg.cholesky(Zf + float(s) / 2 * np.eye(n2))
    Li = np.round(L * 2 ** K2).astype(np.int64)
    Li = np.tril(Li)
    Lm = flint.fmpz_mat([[int(x) for x in row] for row in Li])
    LLt = Lm * Lm.transpose()                                   # = 2^(2 K2) L' L'^T
    # E * 2^K = Z' 2^K + s 2^K I - L'L'^T 2^K ;  2^K = 2^(2 K2) since K = 2 K2
    assert K == 2 * K2
    sK = s * scale
    assert sK.denominator == 1
    sK = int(sK)
    ok = True
    for i in range(n2):
        row = [Zi[i][j] - int(LLt[i, j]) for j in range(n2)]
        row[i] += sK
        off = sum(abs(row[j]) for j in range(n2) if j != i)
        if row[i] < off:
            ok = False
            break
    UB = c0 + trM0 + sum(abs(x) for x in e) + 2 * rx.N * s
    return ok, UB, dict(resid=float(sum(abs(x) for x in e)), shift=float(s), lmin=lmin)


def kappa4_interval():
    """rigorous enclosure of kappa_4 = I_ME(4)/2, I_ME(d) = 4d sum_{k<[d/2]} (1-2k/(d-1)) (q_k - q_{-(k+1)}),
    q_k = 1/(2 d^3 sin^2(pi (k+1/4)/d))  (arb ball arithmetic)."""
    d = 4
    pi = flint.arb.pi()
    tot = flint.arb(0)
    q = lambda k: 1 / (2 * d ** 3 * flint.arb.sin(pi * (k + flint.arb(1) / 4) / d) ** 2)
    for k in range(d // 2):
        tot += (1 - flint.arb(2 * k) / (d - 1)) * (q(k) - q(-(k + 1)))
    return 4 * d * tot / 2


def main():
    args = sys.argv[1:]
    eps, iters = 1e-8, 100000
    if "--eps" in args:
        i = args.index("--eps"); eps = float(args[i + 1]); del args[i:i + 2]
    if "--iters" in args:
        i = args.index("--iters"); iters = int(args[i + 1]); del args[i:i + 2]
    sc = Scen(D)
    reps, S = load_reps(sc)
    rx = Relax()
    kap = kappa4_interval()
    kap_lo = Fraction(1448121609, 10 ** 9)
    assert kap > flint.arb(1448121609) / 10 ** 9        # rigorous (ball comparison)
    print(f"N = {rx.N}, real variables {len(rx.rv)}; kappa_4 = {kap}; rigorous lower bound used {kap_lo}",
          flush=True)
    for a in args:
        j = int(a)
        t0 = time.time()
        C, cconst, su = facet_objective(sc, reps[j])
        c0, c = rx.objective(C, cconst)
        val, st, Z = solve(rx, c0, c, eps, iters)
        t1 = time.time()
        ok, UB, info = certify(rx, c0, c, Z)
        ratio_ub = 1 + UB / su
        below = ok and ratio_ub < kap_lo
        res = dict(cls=j, sdp_value=val, status=st, psd_certified=ok, UB=float(UB), slack_u=str(su),
                   ratio_ub=float(ratio_ub), below_kappa4=bool(below), **info, t_solve=round(t1 - t0, 1),
                   t_cert=round(time.time() - t1, 1))
        print(f"class {j}: SDP {val:.10f} ({st}); exact PSD certificate {ok} (shift {info['shift']:.2e}, "
              f"lambda_min {info['lmin']:.2e}); residual sum {info['resid']:.2e}; exact UB {float(UB):.10f}; "
              f"slack(u) {su}; ratio UB {float(ratio_ub):.10f} -> {'BELOW kappa_4' if below else 'NOT below'}  "
              f"[{t1 - t0:.0f}s + {time.time() - t1:.0f}s]", flush=True)
        with open("logs/IND_sdp_results.jsonl", "a") as fh:
            fh.write(json.dumps(res) + "\n")


if __name__ == "__main__":
    main()
