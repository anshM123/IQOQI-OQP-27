"""
ref_dkz.py -- referee checks of the DKZ side (Lemma 0, Lemma G/S, Lemma W) with own code.

(a) d = 2..dmax: DKZ_d bases built from the definition; q from the bases (float) vs Lemma 0 closed form;
    certified interval enclosure of q computed from the Fourier sum itself (NOT from Lemma 0);
    S^UNI(DKZ_d) bracketed with the FULL d^4-strategy solver (no shift reduction, no Lemma SI).
(b) S^COR(DKZ_d) = min_{p local} max_xy D(q_xy||p_xy) (minimax, cvxpy) vs S^UNI for d = 3, 4, 5 (Lemma G check).
(c) wrapped Z-model (Lemma W(ii)): D(Q^d || wrap_d P^{mu*}) in floats for several d; must be >= S(DKZ_d), <= T.
usage: python ref_dkz.py [dmax]
"""
import sys
import json
from fractions import Fraction as Fr
import numpy as np
import cvxpy as cp
from mpmath import iv, mpf
from ref_solver import solve, certify_lower, certify_upper, cells, corr_from_bases, incidence

iv.dps = 40
T_BOUND = 0.068780260568
DL = {(0, 0): 0.25, (0, 1): 0.75, (1, 0): -0.25, (1, 1): 0.25}


def dkz_bases(d):
    w = np.exp(2j * np.pi / d)
    k = np.arange(d)
    A = [np.array([[w ** (kk * (a + al)) for a in range(d)] for kk in k]) / np.sqrt(d) for al in (0.5, 0.0)]
    B = [np.array([[w ** (-kk * (b + be)) for b in range(d)] for kk in k]) / np.sqrt(d) for be in (0.25, -0.25)]
    return A, B


def q_dkz_iv(d):
    """interval enclosure from the amplitude d^-3/2 sum_k exp(2 pi i k s/d), s = (b + beta_y) - (a + alpha_x)
    (directly from the bases; no closed form)"""
    al = (Fr(1, 2), Fr(0))
    be = (Fr(1, 4), Fr(-1, 4))
    out = {}
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    s = (b + be[y]) - (a + al[x])
                    re = iv.mpf(0)
                    im = iv.mpf(0)
                    for kk in range(d):
                        ang = 2 * iv.pi * kk * iv.mpf(s.numerator) / (s.denominator * d)
                        re += iv.cos(ang)
                        im += iv.sin(ang)
                    out[(x, y, a, b)] = (re * re + im * im) / iv.mpf(d) ** 3
    return out


def scor(qf, d):
    C, idx, S, E = incidence(d)
    w = cp.Variable(len(S), nonneg=True)
    p = E.T @ w
    tt = cp.Variable()
    cons = [cp.sum(w) == 1]
    for x in range(2):
        for y in range(2):
            sel = np.array([c[0] == x and c[1] == y for c in C])
            cons.append(cp.sum(cp.rel_entr(qf[sel], p[sel])) <= tt)
    pr = cp.Problem(cp.Minimize(tt), cons)
    pr.solve(solver=cp.CLARABEL)
    return pr.value


if __name__ == "__main__":
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for d in range(2, dmax + 1):
        A, B = dkz_bases(d)
        qf_d = corr_from_bases(A, B)
        closed = {(x, y, a, b): 1 / (2 * d ** 3 * np.sin(np.pi * (b - a - DL[(x, y)]) / d) ** 2)
                  for x in range(2) for y in range(2) for a in range(d) for b in range(d)}
        e0 = max(abs(qf_d[c] - closed[c]) for c in qf_d)
        qiv = q_dkz_iv(d)
        e1 = max(abs(float(mpf(qiv[c].mid)) - closed[c]) for c in qf_d)
        C = cells(d)
        qf = np.array([qf_d[c] for c in C])
        res = solve(qf, d)
        lo, Mx = certify_lower(qiv, d, res["r"])
        up = certify_upper(qiv, d, res["y"])
        line = (f"[a] d={d}: |q(bases)-Lemma0| = {e0:.1e}, |q_iv-Lemma0| = {e1:.1e}; "
                f"S^UNI(DKZ_d) in [{float(lo):.10f}, {float(up):.10f}] bits; <= T: {float(up) <= T_BOUND}")
        if d in (3, 4, 5):
            sc = scor(qf, d) / np.log(2)
            line += f"; S^COR (float minimax) = {sc:.10f}"
        print(line, flush=True)

    # (c) wrapped Z-model
    Z = json.load(open(r"..\P4_kl\zmodel_cert_A10.json"))
    Aw, Bw = Z["A"], Z["B"]
    t = float(Fr(Z["t"]))
    mu = np.array([float(Fr(v)) for v in Z["mu"]])
    K0 = np.array([[float(Fr(v)) for v in row] for row in Z["K0"]])
    K1 = np.array([[float(Fr(v)) for v in row] for row in Z["K1"]])
    N = 4_000_000
    tailmass = 4 * t / (2 * Aw + 1)

    def linklaw(L):
        """float link law on [-N, N] (index m+N); far tail beyond N ignored here and added per residue below."""
        P = np.zeros(2 * N + 1)
        av = np.arange(-Aw, Aw + 1)
        bv = np.arange(-Bw, Bw + 1)
        Kk = K0 if L in ("00", "10") else K1
        for i, a in enumerate(av):
            vals = bv - a if L in ("10", "11") else bv
            np.add.at(P, vals + N, mu[i] * Kk[i])
        P[{"00": 0, "01": 1, "10": 0, "11": 0}[L] + N] += tailmass / 2      # exact atom (full tail mass)
        m = np.arange(-N, N + 1).astype(float)
        mp_ = {"00": m, "01": m, "10": -m, "11": 1 - m}[L]
        far = np.where(np.abs(mp_) > Aw, t / (2 * (mp_ ** 2 - 0.25)), 0.0)
        return P + far

    laws = {L: linklaw(L) for L in ("00", "01", "10", "11")}
    ms = np.arange(-N, N + 1)
    for d in (2, 3, 4, 5, 7, 8, 16, 33, 64, 128, 1000):
        kl = 0.0
        for (x, y), L in zip(((0, 0), (0, 1), (1, 0), (1, 1)), ("00", "01", "10", "11")):
            Pd = np.bincount(ms % d, weights=laws[L], minlength=d)
            Pd += (1 - Pd.sum()) / d * 0     # mass beyond N (~1e-7) omitted: conservative (Pd too small)
            Qd = np.array([1 / (2 * d ** 2 * np.sin(np.pi * (mm - DL[(x, y)]) / d) ** 2) for mm in range(d)])
            kl += 0.25 * np.sum(Qd * np.log(Qd / Pd))
        print(f"[c] d={d}: D(Q^d || wrap_d P^mu*) = {kl / np.log(2):.10f} bits (<= T = {T_BOUND}: {kl / np.log(2) <= T_BOUND})",
              flush=True)
