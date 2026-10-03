"""
cert_relations.py -- which algebraic relations do the published max-ent certificates
publish/CGLMP/certificates/maxent/cert_tracial_d{d}.pkl use?

(1) Combinatorics: for every Gram term X_ij e_j^+ e_i of the certificate, count the word products adj(w_j) w_i
    that contain two adjacent letters of the same generator (these are reduced with the GROUP LAW
    R^n R^m = R^{n+m}, R^d = 1) and those that collapse to a strictly shorter word / to the identity
    (unitarity R^{-n} R^n = 1).
(2) Evaluation: read every letter R_g^n as the Fourier operator Z^g_n = sum_a w^{na} E^g_a of a POVM and evaluate
    LHS = S(strategy) - lam   and   RHS = sum_b sum_ij X^b_ij L_sym(e_j^+ e_i)   (no word reduction)
    on the symmetrised functional L_sym of (a) random PVM strategies (group law holds: LHS = RHS expected),
    (b) random non-projective POVM strategies.  RHS >= 0 always (X_b >= 0 and Gram matrices >= 0), so equality
    for POVMs would prove the POVM bound; a mismatch shows that the identity is not valid in the POVM algebra.
usage: python cert_relations.py d [d ...]   (d <= 12; certificates read from publish/CGLMP/certificates/maxent)
"""
import os
import sys
import pickle
import numpy as np
from validate_sdp import images, rand_povm
from povm_core import CGLMPPovm

CERT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..', 'publish', 'CGLMP',
                        'certificates', 'maxent')


def cval(x, N):
    a, den = x
    z = np.exp(2j * np.pi * np.arange(len(a)) / N)
    return complex(np.dot(np.array(a, dtype=float), z) / den)


def reduce_w(w, d):
    out = []
    for (g, n) in w:
        n %= d
        if n == 0:
            continue
        if out and out[-1][0] == g:
            m = (out[-1][1] + n) % d
            out.pop()
            if m:
                out.append((g, m))
        else:
            out.append((g, n))
    return tuple(out)


def adj(w, d):
    return tuple((g, (-n) % d) for (g, n) in reversed(w))


def rand_pvm(d, D, rng):
    Z = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))
    Q, _ = np.linalg.qr(Z)
    lab = rng.integers(0, d, size=D)
    return np.stack([sum((np.outer(Q[:, k], Q[:, k].conj()) for k in range(D) if lab[k] == a),
                         np.zeros((D, D), complex)) for a in range(d)])


def main(d):
    N = 4 * d
    cert = pickle.load(open(os.path.join(CERT_DIR, f"cert_tracial_d{d}.pkl"), "rb"))
    w = np.exp(2j * np.pi / d)
    lam = cval(cert["lam"], N).real
    terms = []          # (coef, word_raw)
    n_terms = n_merge = n_short = n_unit = 0
    for b in cert["keep"]:
        lab, els, _ = cert["bdata"][b]
        ker = np.array([[cval(x, N) for x in col] for col in cert["kernels"][b]])      # k x n
        Y = np.array([[cval(x, N) for x in row] for row in cert["Y"][b]])               # k x k
        X = ker.T @ Y @ ker.conj()                                                       # X = N Y N^+
        els_c = [[(cval(c, N), wd) for (c, wd) in el] for el in els]
        n = len(els)
        for i in range(n):
            for j in range(n):
                if abs(X[i, j]) < 1e-14:
                    continue
                for (cj, wj) in els_c[j]:
                    for (ci, wi) in els_c[i]:
                        raw = adj(wj, d) + wi
                        red = reduce_w(raw, d)
                        n_terms += 1
                        if any(raw[k][0] == raw[k + 1][0] for k in range(len(raw) - 1)):
                            n_merge += 1
                        if len(red) < len(raw):
                            n_short += 1
                        if len(raw) > 0 and len(red) == 0:
                            n_unit += 1
                        terms.append((X[i, j] * np.conj(cj) * ci, raw))
    print(f"d={d}: {n_terms} expanded Gram terms; {n_merge} contain adjacent equal generators (group law needed), "
          f"{n_short} shorten under R^n R^m = R^(n+m), {n_unit} collapse to 1 (unitarity R^-n R^n = 1)")

    def S_value(Es):
        P = CGLMPPovm(d, Es[0].shape[1])
        return d * P.Pi_of_E(Es) - 1

    def rhs(Es):
        imgs = images(Es, d)
        Zs = []
        for S in imgs:
            Zs.append({(g, nn): np.einsum('a,aij->ij', w ** (nn * np.arange(d)), S[g]) for g in range(4)
                       for nn in range(1, d)})
        D = Es[0].shape[1]
        cache = {}
        tot = 0.0
        for (c, raw) in terms:
            if raw not in cache:
                v = 0.0
                for Z in Zs:
                    M = np.eye(D, dtype=complex)
                    for l in raw:
                        M = M @ Z[l]
                    v += np.trace(M)
                cache[raw] = v / (len(Zs) * D)
            tot += c * cache[raw]
        return tot
    rng = np.random.default_rng(11)
    for kind in ("PVM", "POVM"):
        for t in range(2):
            D = d + t
            Es = [rand_pvm(d, D, rng) if kind == "PVM" else rand_povm(d, D, rng) for _ in range(4)]
            lhs = S_value(Es) - lam
            r = rhs(Es)
            print(f"   random {kind:4s} D={D}: LHS = S - lam = {lhs:+.12f}   RHS (no reduction) = {r.real:+.12f} "
                  f"(imag {r.imag:+.1e})   LHS-RHS = {lhs - r.real:+.3e}")


if __name__ == "__main__":
    for d in [int(t) for t in sys.argv[1:]]:
        main(d)
