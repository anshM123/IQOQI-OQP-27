"""
cert_numcheck.py -- floating-point semantic cross-check of cert_povm_d{d}.pkl on genuine POVM strategies.
For random (non-projective, full-rank and rank-deficient) POVM strategies on C^D, build the symmetrised strategy
(direct sum of the 16 d images, validate_sdp.images) and compare
   LHS = S(strategy) - lam      with      RHS = sum_b tr(X_b B_b),
B_b evaluated by direct matrix products:  M-blocks  B[j,i] = tau(el_j^+ el_i),
D-blocks B[j,i] = tau(u_j^+ E^0_c u_i E^1_0).  The certificate identity predicts LHS = RHS (up to rounding) for
EVERY POVM strategy, with RHS >= 0 term by term.
usage: python cert_numcheck.py d [ntrials]
"""
import sys
import pickle
import numpy as np
from validate_sdp import images, rand_povm
from povm_core import CGLMPPovm


def cval(x, N):
    a, den = x
    z = np.exp(2j * np.pi * np.arange(len(a)) / N)
    return complex(np.dot(np.array([float(v) for v in a]), z) / float(den)) if abs(den) < 1e300 else None


def cval_safe(x, N):
    """exact element -> complex, summed in 40-digit arithmetic (power-basis coefficients may cancel strongly)."""
    import mpmath as mpm
    a, den = x
    with mpm.workdps(40):
        s = mpm.mpc(0)
        for k, v in enumerate(a):
            if v:
                s += mpm.mpf(int(v)) * mpm.expjpi(mpm.mpf(2 * k) / N)
        s /= int(den)
        return complex(s)


def main(d, ntr=4):
    N = 4 * d
    cert = pickle.load(open(f"cert_povm_d{d}.pkl", "rb"))
    lam = cval_safe(cert["lam"], N).real
    w = np.exp(2j * np.pi / d)
    blocks = []
    for b in cert["keep"]:
        lab, els, _ = cert["bdata"][b]
        ker = np.array([[cval_safe(x, N) for x in col] for col in cert["kernels"][b]])
        Y = np.array([[cval_safe(x, N) for x in row] for row in cert["Y"][b]])
        X = ker.T @ Y @ ker.conj()
        els_c = [[(cval_safe(c, N), wd) for (c, wd) in el] for el in els]
        blocks.append((lab, X, els_c))
    rng = np.random.default_rng(2026)
    for t in range(ntr):
        D = d + (t % 3) - 1 if d > 2 else d
        rank = None if t % 2 == 0 else max(1, D // 2)
        Es = []
        for g in range(4):
            G = rng.normal(size=(d, D, D)) + 1j * rng.normal(size=(d, D, D))
            if rank is not None:
                G[:, rank:, :] = 0
            K = np.einsum('aki,akj->ij', G.conj(), G)
            lam_, U = np.linalg.eigh(K)
            S_ = (U * lam_ ** -0.5) @ U.conj().T
            Es.append(np.stack([S_ @ gg.conj().T @ gg @ S_ for gg in G]))
        imgs = images(Es, d)
        Zs = [{(g, n): np.einsum('a,aij->ij', w ** (n * np.arange(d)), S[g]) for g in range(4) for n in range(1, d)}
              for S in imgs]
        Effs = [[[np.einsum('n,nij->ij', w ** (-np.arange(d) * a),
                            np.stack([np.eye(D)] + [S[g] for _ in []] + [Zs[k][(g, n)] for n in range(1, d)])) / d
                  for a in range(d)] for g in range(4)] for k, S in enumerate(imgs)]

        def wordmat(k, wd):
            M = np.eye(D, dtype=complex)
            for l in wd:
                M = M @ Zs[k][l]
            return M
        rhs = 0.0
        minterm = np.inf
        for (lab, X, els_c) in blocks:
            n = len(els_c)
            B = np.zeros((n, n), complex)
            for k in range(len(imgs)):
                V = [sum(c * wordmat(k, wd) for (c, wd) in el) for el in els_c]
                if lab[0] == 'M':
                    for i in range(n):
                        for j in range(n):
                            B[j, i] += np.trace(V[j].conj().T @ V[i])
                else:
                    Ec = Effs[k][0][lab[2]]
                    F0 = Effs[k][1][0]
                    for i in range(n):
                        for j in range(n):
                            B[j, i] += np.trace(V[j].conj().T @ Ec @ V[i] @ F0)
            B /= (len(imgs) * D)
            term = np.trace(X @ B.T).real if False else np.sum(X * B.T).real   # sum_ij X_ij B_ji
            minterm = min(minterm, term)
            rhs += term
        P = CGLMPPovm(d, D)
        lhs = d * P.Pi_of_E(Es) - 1 - lam
        print(f"d={d} trial {t} D={D} rank cap {rank}: LHS = S - lam = {lhs:+.12f}   RHS = {rhs:+.12f}   "
              f"diff {lhs - rhs:+.1e}   min block term {minterm:+.2e}", flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 4)
