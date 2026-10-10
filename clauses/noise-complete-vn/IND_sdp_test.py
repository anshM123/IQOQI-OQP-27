"""
IND_sdp_test.py -- validity tests of the relaxation of IND_sdp.py against actual quantum strategies (numerical, not
load-bearing except as a consistency check) and the exact identification of class 17 with CGLMP_4.
  (1) random rank-one PVMs on Phi_4 (and a balanced rank-2 example on Phi_8): direct behaviour p from the state;
      symmetrised tracial moments; every moment-matrix entry equals the value assigned to its class; M >= 0;
      the relaxation objective c0 + c.t equals the direct Bell value beta_j(p) for every class j;
  (2) CGLMP_4 written from the CGLMP definition: integer slack tensor, local bound 2, I_4(u) = 0, explicit
      relabelling onto class 17 (exact); DKZ (my construction) attains ratio kappa_4 on class 17 (numerical).
"""
import itertools
from fractions import Fraction
import numpy as np
from IND_core import Scen, Matcher
from IND_expand import load_reps
from IND_sdp import Relax, facet_objective, klass, adjoint, kappa4_interval, D


def haar(n, rng):
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def strategy(rng, Dloc=4, rank=1):
    """balanced PVMs: projectors of rank 'rank' (Dloc = 4 rank)."""
    out = []
    for g in range(4):
        U = haar(Dloc, rng)
        out.append([U[:, a * rank:(a + 1) * rank] @ U[:, a * rank:(a + 1) * rank].conj().T for a in range(D)])
    return out


def behaviour_direct(A, B, Dloc):
    phi = np.eye(Dloc).reshape(-1) / np.sqrt(Dloc)
    p = np.zeros((2, 2, D, D))
    for x in range(2):
        for y in range(2):
            for a in range(D):
                for b in range(D):
                    p[x, y, a, b] = np.real(phi.conj() @ np.kron(A[x][a], B[y][b]) @ phi)
    return p


def word_op(w, U):
    Dl = U[0].shape[0]
    M = np.eye(Dl, dtype=complex)
    for (g, n) in w:
        M = M @ np.linalg.matrix_power(U[g], n)
    return M


def test_strategy(rx, reps, sc, rng, Dloc, rank):
    A = strategy(rng, Dloc, rank)[:2]
    B = strategy(rng, Dloc, rank)[:2]
    p = behaviour_direct(A, B, Dloc)
    P = [[Pa.T for Pa in A[x]] for x in range(2)]
    Q = [B[y] for y in range(2)]
    U = [sum((1j) ** a * P[x][a] for a in range(D)) for x in range(2)] + \
        [sum((1j) ** b * Q[y][b] for b in range(D)) for y in range(2)]
    tau = lambda w: (np.trace(word_op(w, U)) + np.trace(word_op(tuple(reversed(w)), U))) / (2 * Dloc)
    # moments by class
    val = {}
    err = 0.0
    N = rx.N
    M = np.zeros((N, N), dtype=complex)
    for i, u in enumerate(rx.W):
        for j, v in enumerate(rx.W):
            w = adjoint(u) + v
            t = tau(w)
            M[i, j] = t
            k = rx.cls[i][j]
            if k in val:
                err = max(err, abs(val[k] - t))
            else:
                val[k] = t
    eig = np.linalg.eigvalsh((M + M.conj().T) / 2).min()
    # class rules
    rule = max(abs(val[()] - 1), max(abs(v) for k, v in val.items() if len(k) == 1))
    # real variables
    t = np.zeros(len(rx.rv))
    for r, (k, part) in enumerate(rx.rv):
        t[r] = np.real(val[k]) if part == 're' else np.imag(val[k])
    worst = 0.0
    for j in range(len(reps)):
        C, cconst, su = facet_objective(sc, reps[j])
        c0, c = rx.objective(C, cconst)
        rel = float(c0) + sum(float(ci) * ti for ci, ti in zip(c, t))
        direct = float(cconst) + sum(float(C[x][y][a][b]) * p[x, y, a, b] for x in range(2) for y in range(2)
                                     for a in range(D) for b in range(D))
        worst = max(worst, abs(rel - direct))
    return err, eig, rule, worst


def cglmp_slack(sc):
    """3 * (2 - I_4(lam)) for the CGLMP_4 expression (weights 1, 1/3), integer tensor."""
    d = D
    def P(cond):
        return int(cond)
    out = []
    for (a0, a1, b0, b1) in sc.lams:
        A = (a0, a1); Bv = (b0, b1)
        I3 = 0
        for k, wgt in ((0, 3), (1, 1)):
            plus = (P((A[0] - Bv[0]) % d == k % d) + P((Bv[0] - A[1]) % d == (k + 1) % d) +
                    P((A[1] - Bv[1]) % d == k % d) + P((Bv[1] - A[0]) % d == k % d))
            minus = (P((A[0] - Bv[0]) % d == (-k - 1) % d) + P((Bv[0] - A[1]) % d == (-k) % d) +
                     P((A[1] - Bv[1]) % d == (-k - 1) % d) + P((Bv[1] - A[0]) % d == (-k - 1) % d))
            I3 += wgt * (plus - minus)
        out.append(6 - I3)
    return np.array(out, dtype=np.int64)


if __name__ == "__main__":
    sc = Scen(D)
    reps, S = load_reps(sc)
    rx = Relax()
    rng = np.random.default_rng(5)
    for (Dl, rk) in [(4, 1), (4, 1), (8, 2)]:
        err, eig, rule, worst = test_strategy(rx, reps, sc, rng, Dl, rk)
        print(f"(1) random balanced PVMs on Phi_{Dl}: class consistency {err:.1e}, lambda_min(M) {eig:.1e}, "
              f"identity/marginal rules {rule:.1e}, max |relaxation objective - direct Bell value| over 34 classes "
              f"{worst:.1e}")
    s = cglmp_slack(sc)
    print(f"(2) CGLMP_4: min of 3(2 - I_4) over deterministic points = {s.min()} (local bound 2 attained), "
          f"I_4(u) = {Fraction(int(6 * 256 - s.sum()), 3 * 256)} (sum over lam of I_4/256)")
    from math import gcd
    g = int(np.gcd.reduce(s[s > 0]))
    M = Matcher(sc)
    gg = M.find(reps[17], s // g)
    print(f"    primitive slack (gcd {g}) is G-equivalent to class 17: {gg is not None} (explicit g = {gg})")
    print(f"    kappa_4 = {kappa4_interval()}")
    # DKZ (state + Fourier bases with phases alpha = 0, 1/2 ; beta = 1/4, -1/4), I_4 evaluated directly
    d = D
    def basis_A(al):
        return [np.exp(2j * np.pi * np.arange(d) * (k + al) / d) / np.sqrt(d) for k in range(d)]
    def basis_B(be):
        return [np.exp(-2j * np.pi * np.arange(d) * (l + be) / d) / np.sqrt(d) for l in range(d)]
    phi = np.eye(d).reshape(-1) / np.sqrt(d)
    best = None
    for sgn in (1, -1):
        pd = np.zeros((2, 2, d, d))
        for x, al in enumerate((0.0, 0.5)):
            for y, be in enumerate((0.25 * sgn, -0.25 * sgn)):
                for k, va in enumerate(basis_A(al)):
                    for l, vb in enumerate(basis_B(be)):
                        pd[x, y, k, l] = abs(np.kron(va, vb).conj() @ phi) ** 2
        def Pd(x, y, k, xfirst=True):
            return sum(pd[x, y, a, b] for a in range(d) for b in range(d) if ((a - b) if xfirst else (b - a)) % d == k % d)
        I = 0.0
        for k, wgt in ((0, 1.0), (1, 1 / 3)):
            I += wgt * (Pd(0, 0, k) + Pd(1, 0, k + 1, False) + Pd(1, 1, k) + Pd(0, 1, k, False)
                        - Pd(0, 0, -k - 1) - Pd(1, 0, -k, False) - Pd(1, 1, -k - 1) - Pd(0, 1, -k - 1, False))
        best = I if best is None else max(best, I)
    print(f"    DKZ value of I_4 = {best:.12f}; I_4/2 = {best / 2:.12f} (= kappa_4 numerically)")
