"""
ref_numeric.py -- end-to-end floating-point sanity check of the certificate on ACTUAL POVM strategies
(no word canonicalisation at all): for a random POVM 4-tuple E on C^D, build the direct sum of all images
f.E (f in the referee's group G; image formula derived independently: (f.E)^g_a = E^{p[g]}_{eps (a - t[g])},
transposed if f reverses words), evaluate every certificate term with matrices and compare
   S(p) - lam   vs   sum_b tr(X^b G^b)  (G^b Gram / doubly-localizing matrices of the direct-sum strategy).
Also reports the same comparison WITHOUT symmetrisation (expected to fail for generic POVMs) and the
minimum of the individual block terms (must be >= 0 up to rounding).
usage: python ref_numeric.py d [trials]
"""
import sys
import pickle
import numpy as np
import mpmath
from ref_verify import make_group

mpmath.mp.dps = 50


def to_complex(x, N):
    a, den = x
    z = mpmath.exp(2j * mpmath.pi / N)
    v = mpmath.fsum(int(t) * z ** k for k, t in enumerate(a) if t) / int(den)
    return complex(v)


def random_povm(D, d, rng, rank=None):
    Ms = []
    for _ in range(d):
        r = rank or D
        M = rng.normal(size=(r, D)) + 1j * rng.normal(size=(r, D))
        Ms.append(M.conj().T @ M)
    K = sum(Ms)
    w, V = np.linalg.eigh(K)
    Kih = V @ np.diag(w ** -0.5) @ V.conj().T
    return [Kih @ A @ Kih for A in Ms]


def random_pvm(D, d, rng):
    Q, _ = np.linalg.qr(rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)))
    labels = rng.integers(0, d, size=D)
    return [sum((np.outer(Q[:, k], Q[:, k].conj()) for k in range(D) if labels[k] == a), np.zeros((D, D))) for a in range(d)]


def dkz_tracial(d, m=1):
    """DKZ strategy in the tracial chain picture (as monomial unitaries U_g, g = 0..3), tensored with 1_m:
    U_g e_k = zeta^{e_k} e_{k-1}, e_k = -a (k >= 1), a(d-1) (k = 0), a = 2 - g, zeta = exp(2 pi i/4d)."""
    N = 4 * d
    zeta = np.exp(2j * np.pi / N)
    w = np.exp(2j * np.pi / d)
    E = []
    for g in range(4):
        a = 2 - g
        U = np.zeros((d, d), dtype=complex)
        for k in range(d):
            e = (-a) % N if k >= 1 else (a * (d - 1)) % N
            U[(k - 1) % d, k] = zeta ** e
        Un = [np.linalg.matrix_power(U, n) for n in range(d)]
        Eg = [sum(w ** (-n * aa) * Un[n] for n in range(d)) / d for aa in range(d)]
        E.append([np.kron(A, np.eye(m)) for A in Eg])
    return E


def images(E, G, d):
    out = []
    for (p, eps, t, r) in G:
        F = []
        for g in range(4):
            Fg = [E[p[g]][(eps * (a - t[g])) % d] for a in range(d)]
            if r:
                Fg = [A.T for A in Fg]
            F.append(Fg)
        out.append(F)
    return out


def direct_sum(strats, d):
    D = strats[0][0][0].shape[0]
    M = len(strats) * D
    out = []
    for g in range(4):
        Eg = []
        for a in range(d):
            A = np.zeros((M, M), dtype=complex)
            for s, F in enumerate(strats):
                A[s * D:(s + 1) * D, s * D:(s + 1) * D] = F[g][a]
            Eg.append(A)
        out.append(Eg)
    return out


def S_of(E, d):
    """S(p) = E<X1-Y1> + E<Y1-X2> + E<X2-Y2> + E<Y2-X1-1>, p(a,b|x,y) = tau(E^{2x}_a E^{2y+1}_b)"""
    tau = lambda A: np.trace(A).real / A.shape[0]
    P = lambda g1, g2: np.array([[tau(E[g1][a] @ E[g2][b]) for b in range(d)] for a in range(d)])
    S = 0.0
    for (g1, g2, delta) in [(0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, 1)]:
        pp = P(g1, g2)
        S += sum(((a - b - delta) % d) * pp[a, b] for a in range(d) for b in range(d))
    return S


def literal_I(E, d):
    """literal CGLMP (BRIEF) on p(a,b|x,y) = tau(A^x_a (B^y_b)^T) = tau(E^{2x}_a E^{2y+1}_b); A1=x0, A2=x1, B1=y0, B2=y1"""
    tau = lambda A: np.trace(A).real / A.shape[0]
    p = {}
    for x in range(2):
        for y in range(2):
            p[x, y] = np.array([[tau(E[2 * x][a] @ E[2 * y + 1][b]) for b in range(d)] for a in range(d)])
    def P(x, y, rel):     # P(A_x - B_y = rel mod d)  (rel as function of a, b)
        return sum(p[x, y][a, b] for a in range(d) for b in range(d) if rel(a, b))
    I = 0.0
    for k in range(d // 2):
        wk = 1 - 2 * k / (d - 1)
        I += wk * (P(0, 0, lambda a, b: a % d == (b + k) % d) + P(1, 0, lambda a, b: b % d == (a + k + 1) % d)
                   + P(1, 1, lambda a, b: a % d == (b + k) % d) + P(0, 1, lambda a, b: b % d == (a + k) % d)
                   - P(0, 0, lambda a, b: a % d == (b - k - 1) % d) - P(1, 0, lambda a, b: b % d == (a - k) % d)
                   - P(1, 1, lambda a, b: a % d == (b - k - 1) % d) - P(0, 1, lambda a, b: b % d == (a - k - 1) % d))
    return I


def rhs_terms(comps, d, cert, Xs):
    """comps: list of strategies (components of a direct sum); tau of the direct sum = average of the
    normalised traces over the components (block-diagonal operators)."""
    N = 4 * d
    w = np.exp(2j * np.pi / d)
    acc = {}
    for E in comps:
        M = E[0][0].shape[0]
        tau = lambda A: np.trace(A) / M
        Z = {}
        for g in range(4):
            for n in range(1, d):
                Z[(g, n)] = sum(w ** (n * a) * E[g][a] for a in range(d))

        def wordmat(word):
            A = np.eye(M, dtype=complex)
            for l in word:
                A = A @ Z[l]
            return A
        for b in cert["keep"]:
            lab, els, _ = cert["bdata"][b]
            n = len(els)
            e = [sum(CPLX[(b, i, k)] * wordmat(wd) for k, (cf, wd) in enumerate(el)) for i, el in enumerate(els)]
            if lab[0] == 'M':
                Gm = np.array([[tau(e[j].conj().T @ e[i]) for i in range(n)] for j in range(n)])
            else:
                Ec, F = E[0][lab[2]], E[1][0]
                Gm = np.array([[tau(e[j].conj().T @ Ec @ e[i] @ F) for i in range(n)] for j in range(n)])
            acc[b] = acc.get(b, 0) + Gm / len(comps)
    return [np.sum(Xs[b] * acc[b].T) for b in cert["keep"]]      # sum_ij X_ij G_ji


CPLX = {}


def main():
    d = int(sys.argv[1])
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    cert = pickle.load(open(rf"..\P1_povm_numerics\certs\cert_povm_d{d}.pkl", "rb"))
    N = 4 * d
    lam = to_complex(cert["lam"], N).real
    Xs = {}
    for b in cert["keep"]:
        Y = np.array([[to_complex(x, N) for x in row] for row in cert["Y"][b]])
        Nm = np.array([[to_complex(x, N) for x in col] for col in cert["kernels"][b]]).T   # n x k
        Xs[b] = Nm @ Y @ Nm.conj().T
    G = make_group(d)
    for b in cert["keep"]:
        for i, el in enumerate(cert["bdata"][b][1]):
            for k, (cf, wd) in enumerate(el):
                CPLX[(b, i, k)] = to_complex(cf, N)
    rng = np.random.default_rng(12345 + d)
    I_me = 4 * sum((d - j) / np.cos(np.pi * j / (2 * d)) for j in range(1, d)) / (d * (d - 1))
    for trial in range(trials):
        D = [2, 3, d - 1, d + 1][trial % 4]
        kind = ["full-rank POVM", "rank-1 POVM", "PVM", "DKZ x 1_2", "DKZ+5% noise"][trial % 5]
        if kind == "DKZ x 1_2":
            D = 2 * d
            E = dkz_tracial(d, 2)
        elif kind == "DKZ+5% noise":
            D = d
            E0 = dkz_tracial(d)
            E = []
            for g in range(4):
                Rr = random_povm(d, d, rng)
                E.append([0.95 * E0[g][a] + 0.05 * Rr[a] for a in range(d)])
        elif kind == "full-rank POVM":
            E = [random_povm(D, d, rng) for _ in range(4)]
        elif kind == "rank-1 POVM":
            E = [random_povm(D, d, rng, rank=1) for _ in range(4)]
        else:
            E = [random_pvm(D, d, rng) for _ in range(4)]
        comps = images(E, G, d)
        lhs = S_of(E, d) - lam
        lhs_sym = np.mean([S_of(F, d) for F in comps]) - lam
        t_sym = rhs_terms(comps, d, cert, Xs)
        rhs_sym = sum(t_sym)
        t_raw = rhs_terms([E], d, cert, Xs)
        rhs_raw = sum(t_raw)
        # literal CGLMP with both setting labels exchanged:  I_d(p') = 4 - 2 S(p)/(d-1)
        Eswap = [E[2], E[3], E[0], E[1]]
        Ilit = literal_I(Eswap, d)
        print(f"d={d} D={D} {kind:15s}: S-lam={lhs:+.12f}  S(sym)-lam={lhs_sym:+.12f}  RHS(sym)={rhs_sym.real:+.12f}"
              f" (imag {abs(rhs_sym.imag):.1e}, min term {min(t.real for t in t_sym):+.2e})  |LHS-RHS|={abs(lhs - rhs_sym):.2e}"
              f" | unsymmetrised RHS={rhs_raw.real:+.6f} (diff {abs(lhs - rhs_raw):.2e}) | I_lit(p')={Ilit:.10f}"
              f" vs 4-2S/(d-1)={4 - 2 * (lhs + lam) / (d - 1):.10f}  (I_ME={I_me:.10f})", flush=True)


if __name__ == "__main__":
    main()
