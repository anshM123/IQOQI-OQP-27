"""
povm.py -- Proposition 4 (scope, POVMs): exact checks.

Competitor PVMs P^x_a on Phi_d (even d: CHSH (x) 1; odd d: block construction), and the POVMs
    M^x_a(eps) = (1 - eps) P^x_a + (eps/d) 1,      N^y_b(eps) likewise for Bob.
Every effect is >= (eps/d) 1 (full rank), every outcome pair has probability >= eps^2/d^2 > 0.  The behaviour is
p_eps = (L_eps (x) L_eps) p with the local outcome channel L_eps (keep w.p. 1 - eps, else uniform), and L_eps (x) L_eps
fixes u.  Coarse-grained CHSH (outcome 0 -> +1, others -> -1), e = (2 - d)/d:
    even:  CHSH(p_eps) = (1-eps)^2 2 sqrt2 + 2 eps^2 e^2
    odd:   CHSH(p_eps) = (1-eps)^2 ((d-1)/d 2 sqrt2 + 2/d) + (1-eps) eps 4 e/d + 2 eps^2 e^2
    w_eps(d) = (2 - 2 e^2)/(CHSH(p_eps) - 2 e^2)  >=  v_c(p_eps).
Check (exact, Q(sqrt2)): for eps = 1/100 (and, by monotonicity in eps, all 0 <= eps <= 1/100):
    d = 4..10: w_eps(d) < v0(d) (certified DKZ lower bound, certificates/dkz_d*.json);
    d >= 11:   w_eps(d) < 1/2 <= v_c(DKZ_d)   (polynomial inequality in d, both parities).
Also the formula for CHSH(p_eps) is re-derived numerically from the explicit POVMs for d = 4..7 (sanity check).
"""
import json
import os
import sys
from fractions import Fraction as Fr

from exact import Q2, Poly, certify_nonneg

EPS = Fr(1, 100)
SQ2 = Q2(0, 1)


def chsh_eps(d, eps, parity):
    e = Fr(2 - d, d)
    if parity == "even":
        return (1 - eps) ** 2 * 2 * SQ2 + 2 * eps ** 2 * e ** 2
    return (1 - eps) ** 2 * (Fr(d - 1, d) * 2 * SQ2 + Fr(2, d)) + (1 - eps) * eps * 4 * e / d + 2 * eps ** 2 * e ** 2


def w_eps(d, eps, parity):
    e2 = Fr(d - 2, d) ** 2
    return (2 - 2 * e2) / (chsh_eps(d, eps, parity) - 2 * e2)


def monotone_in_eps(d, parity):
    """w_eps increasing in eps on [0, 1/100]: numerator constant > 0, CHSH(p_eps) decreasing.  CHSH(p_eps) is a
    quadratic polynomial in eps; we certify -d/deps CHSH(p_eps) >= 0 on [0, 1/100] exactly."""
    t = Poly.t()
    e = Fr(2 - d, d)
    if parity == "even":
        P = (1 - t) * (1 - t) * (2 * SQ2) + 2 * e * e * t * t
    else:
        P = ((1 - t) * (1 - t) * (Fr(d - 1, d) * 2 * SQ2 + Fr(2, d)) + (1 - t) * t * (4 * e / d)
             + 2 * e * e * t * t)
    # derivative
    dP = Poly([P.c[k] * k for k in range(1, len(P.c))]) if P.deg() >= 1 else Poly.const(0)
    ok, _ = certify_nonneg(-dP, 0, Fr(1, 100))
    return ok


def large_d(parity, d1=11):
    """w_eps(d) < 1/2 for all real d >= d1:  2 (2 - 2e^2) < CHSH(p_eps) - 2 e^2.  Multiply by d^2 (resp. d^2) and
    substitute d = d1 + s: certify the polynomial in s is > 0 for s >= 0 (all coefficients > 0 suffices)."""
    s = Poly.t()
    dd = s + d1
    eps = EPS
    # e = (2 - d)/d ; d^2 e^2 = (d - 2)^2 ; d^2 (1 - e^2) = 4 d - 4
    E2d2 = (dd - 2) * (dd - 2)
    if parity == "even":
        chsh_d2 = (1 - eps) ** 2 * 2 * SQ2 * dd * dd + 2 * eps ** 2 * E2d2
    else:
        # d^2 CHSH = (1-eps)^2 (2 sqrt2 (d-1) d + 2 d) + (1-eps) eps 4 (2 - d) + 2 eps^2 (d-2)^2
        chsh_d2 = ((1 - eps) ** 2 * (2 * SQ2 * (dd - 1) * dd + 2 * dd) + (1 - eps) * eps * 4 * (2 - dd)
                   + 2 * eps ** 2 * E2d2)
    G = chsh_d2 - 2 * E2d2 - 2 * (2 * (4 * dd - 4))          # must be > 0
    return all(c.sign() > 0 for c in G.c), G


def run():
    ok = True
    cert_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certificates")
    for d in range(4, 11):
        par = "even" if d % 2 == 0 else "odd"
        w = w_eps(d, EPS, par)
        w0 = w_eps(d, Fr(0), par)
        v0 = Fr(*json.load(open(os.path.join(cert_dir, f"dkz_d{d}.json")))["v0"])
        mono = monotone_in_eps(d, par)
        good = (w < Q2(v0)) and mono and (chsh_eps(d, EPS, par) > Q2(2))
        ok &= good
        print(f"  d={d:2d} ({par}): w_0 = {float(w0):.6f}, w_(1/100) = {float(w):.6f} < v0(DKZ) = {float(v0):.6f}; "
              f"CHSH decreasing in eps: {mono}  {'OK' if good else 'FAIL'}")
    for par in ("even", "odd"):
        good, G = large_d(par)
        ok &= good
        print(f"  d >= 11 ({par} formula): w_(1/100)(d) < 1/2 certified (shifted polynomial has positive coefficients): "
              f"{good}")
        # monotonicity in eps for d >= 11 is not needed: w_eps < 1/2 is checked at eps = 1/100 only and the
        # derivative argument below covers smaller eps
    # monotonicity in eps for every d >= 11: dCHSH/deps <= 0 on [0,1/100]; even: -4 sqrt2 (1-eps) + 4 eps e^2 < 0;
    # odd: additionally the middle term derivative (1 - 2 eps) 4 e/d <= 0 since e < 0.  Both clear for eps <= 1/100.
    return ok


def numeric_check():
    import numpy as np
    sz = np.array([[1, 0], [0, -1]], float)
    sx = np.array([[0, 1], [1, 0]], float)
    A = [sz, sx]
    B = [(sz + sx) / np.sqrt(2), (sz - sx) / np.sqrt(2)]
    s = np.array([[1, 1], [1, -1]])
    eps = float(EPS)
    for d in range(4, 8):
        if d % 2 == 0:
            k = d // 2
            P = [[np.kron((np.eye(2) + A[x]) / 2, np.eye(k)), np.kron((np.eye(2) - A[x]) / 2, np.eye(k))] +
                 [np.zeros((d, d))] * (d - 2) for x in range(2)]
            Q = [[np.kron((np.eye(2) + B[y]) / 2, np.eye(k)), np.kron((np.eye(2) - B[y]) / 2, np.eye(k))] +
                 [np.zeros((d, d))] * (d - 2) for y in range(2)]
        else:
            k = (d - 1) // 2

            def blk(M, extra):
                Z = np.zeros((d, d))
                Z[: 2 * k, : 2 * k] = np.kron(np.eye(k), M)
                Z[d - 1, d - 1] = extra
                return Z
            P = [[blk((np.eye(2) + A[x]) / 2, 1), blk((np.eye(2) - A[x]) / 2, 0)] + [np.zeros((d, d))] * (d - 2)
                 for x in range(2)]
            Q = [[blk((np.eye(2) + B[y]) / 2, 1), blk((np.eye(2) - B[y]) / 2, 0)] + [np.zeros((d, d))] * (d - 2)
                 for y in range(2)]
        M = [[(1 - eps) * P[x][a] + eps / d * np.eye(d) for a in range(d)] for x in range(2)]
        N = [[(1 - eps) * Q[y][b] + eps / d * np.eye(d) for b in range(d)] for y in range(2)]
        chsh = 0
        for x in range(2):
            for y in range(2):
                p = np.array([[np.trace(M[x][a].T @ N[y][b]) / d for b in range(d)] for a in range(d)])
                sgn = np.where(np.arange(d) == 0, 1, -1)
                chsh += s[x, y] * sgn @ p @ sgn
        par = "even" if d % 2 == 0 else "odd"
        print(f"  numeric d={d}: CHSH(p_eps) = {chsh:.12f}, formula {float(chsh_eps(d, EPS, par)):.12f}; "
              f"min eigenvalue of effects = {min(np.linalg.eigvalsh(m).min() for row in M for m in row):.4f} "
              f"(eps/d = {eps / d:.4f})")


def pvm_all_outcomes(dmax=9, kmax=400):
    """Remark: PVMs on Phi_D, D = 2k + d - 2, every outcome used.  P^x_0 = Pi^x_+ (x) 1_k (+) 0, P^x_1 = Pi^x_- (x) 1_k
    (+) 0, P^x_a = |e_a><e_a| (a >= 2, on the last d - 2 basis vectors), same for Bob.  Behaviour
    p = (2k/D) CH + ((d-2)/D) tau, tau = perfectly correlated uniform outcome in {2..d-1} (binarised: always -1, so
    CHSH(tau) = 2).  CHSH-witness bound v_c <= w = (2 - 2e^2)/(CHSH(p) - 2e^2).  Returns the least k with
    w < v0(d) (exact), d = 4..dmax."""
    cert_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certificates")
    out = {}
    for d in range(4, dmax + 1):
        v0 = Fr(*json.load(open(os.path.join(cert_dir, f"dkz_d{d}.json")))["v0"])
        e2 = Fr(d - 2, d) ** 2
        for k in range(1, kmax):
            D = 2 * k + d - 2
            chsh = Fr(2 * k, D) * 2 * SQ2 + Fr(d - 2, D) * 2
            if chsh - 2 * e2 <= Q2(0):
                continue
            w = (2 - 2 * e2) / (chsh - 2 * e2)
            if w < Q2(v0):
                out[d] = (k, D, float(w))
                break
    return out


if __name__ == "__main__":
    ok = run()
    numeric_check()
    for d, (k, D, w) in pvm_all_outcomes().items():
        print(f"  PVMs on Phi_D, all outcomes used: d={d}: least k = {k} (D = {D}), CHSH bound {w:.6f} < v0(DKZ_{d})")
    print("RESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
