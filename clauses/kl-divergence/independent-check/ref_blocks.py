"""
ref_blocks.py -- referee re-verification of Lemma B, Lemma C, Lemma F and the competitor side of Theorem 1.

(1) Their certificates (kl-divergence/blocks_testfactors.json) re-checked with own code: exact (F1) by full enumeration of
    all m^4 strategies (Fractions), (F2) exactly, and L_j with own exact-algebraic interval enclosures of q_j
    (K3 via the level form Q_{g'}/3 with Q = (2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9), not via sines).
(2) Own optimal test factors (own cvxpy solver), certified lower bound + certified explicit local model upper bound
    => two-sided brackets for S^UNI of the blocks C2, K3, CC4.
(3) The actual competitor B_d on C^d, d = 4..9: bases built from scratch, q computed from the bases and compared
    with the direct-sum formula; S^UNI(B_d) bracketed with the full d^4-strategy solver (no use of Lemma F).
usage: python ref_blocks.py [dmax]
"""
import sys
import itertools
import json
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf
from ref_solver import solve, certify_lower, certify_upper, cells, corr_from_bases

iv.dps = 40
LN2 = iv.log(iv.mpf(2))
S2 = iv.sqrt(iv.mpf(2))
S3 = iv.sqrt(iv.mpf(3))


def gp(x, y, a, b):
    """CGLMP levels for d = 3 (THEOREM.md section 3)"""
    if (x, y) in ((0, 0), (1, 1)):
        return (a - b) % 3
    if (x, y) == (1, 0):
        return (b - a) % 3
    return (b - a - 1) % 3


QK3 = [2 * (2 + S3) / 9, 2 * (2 - S3) / 9, iv.mpf(1) / 9]


def q_block(name):
    """exact interval enclosure of the block correlation on Phi_m: dict (x,y,a,b) -> iv"""
    if name == "T1":
        return 1, {(x, y, 0, 0): iv.mpf(1) for x in range(2) for y in range(2)}
    if name == "C2":
        return 2, {(x, y, a, b): (1 + (-1) ** ((a + b + x * y) % 2) / S2) / 4
                   for x, y, a, b in itertools.product(range(2), repeat=4)}
    if name == "K3":
        return 3, {(x, y, a, b): QK3[gp(x, y, a, b)] / 3
                   for x in range(2) for y in range(2) for a in range(3) for b in range(3)}
    if name == "CC4":
        _, c = q_block("C2")
        return 4, {(x, y, A, B): c[(x, y, A >> 1, B >> 1)] * c[(x, y, A & 1, B & 1)]
                   for x in range(2) for y in range(2) for A in range(4) for B in range(4)}
    raise ValueError(name)


# ------------------------------------------------------------------ bases (from scratch)
def chsh_basis(theta):
    return np.array([[np.cos(theta / 2), -np.sin(theta / 2)], [np.sin(theta / 2), np.cos(theta / 2)]], dtype=complex)


def block_bases(name):
    if name == "T1":
        return [np.eye(1, dtype=complex)] * 2, [np.eye(1, dtype=complex)] * 2
    if name == "C2":
        return [chsh_basis(0), chsh_basis(np.pi / 2)], [chsh_basis(np.pi / 4), chsh_basis(-np.pi / 4)]
    if name == "CC4":
        A, B = block_bases("C2")
        return [np.kron(A[x], A[x]) for x in range(2)], [np.kron(B[y], B[y]) for y in range(2)]
    if name == "K3":
        w = np.exp(2j * np.pi / 3)
        k = np.arange(3)
        A = [np.array([[w ** (kk * (a + al)) for a in range(3)] for kk in k]) / np.sqrt(3) for al in (0.5, 0.0)]
        B = [np.array([[w ** (-kk * (b + be)) for b in range(3)] for kk in k]) / np.sqrt(3) for be in (0.25, -0.25)]
        return A, B


def competitor_bases(d):
    k, rho = divmod(d, 4)
    names = ["CC4"] * k + ([{1: "T1", 2: "C2", 3: "K3"}[rho]] if rho else [])
    A = [np.zeros((d, d), complex) for _ in range(2)]
    B = [np.zeros((d, d), complex) for _ in range(2)]
    o = 0
    blocks = []
    for nm in names:
        a, b = block_bases(nm)
        m = a[0].shape[0]
        for x in range(2):
            A[x][o:o + m, o:o + m] = a[x]
            B[x][o:o + m, o:o + m] = b[x]
        blocks.append((nm, o, m))
        o += m
    return A, B, blocks


def q_competitor_iv(d, blocks):
    q = {c: iv.mpf(0) for c in cells(d)}
    for nm, o, m in blocks:
        _, qb = q_block(nm)
        for (x, y, a, b), v in qb.items():
            q[(x, y, o + a, o + b)] = v * m / d
    return q


if __name__ == "__main__":
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    # ---------------------------------------------- (0) bases reproduce the exact block correlations
    for nm in ("T1", "C2", "K3", "CC4"):
        A, B = block_bases(nm)
        m = A[0].shape[0]
        for x in range(2):
            assert np.allclose(A[x].conj().T @ A[x], np.eye(m)) and np.allclose(B[x].conj().T @ B[x], np.eye(m))
        qf = corr_from_bases(A, B)
        _, qe = q_block(nm)
        err = max(abs(qf[c] - float(mpf(qe.get(c, iv.mpf(0)).mid))) for c in qf)
        print(f"[0] block {nm}: |q(bases) - exact formula| = {err:.1e}")
        assert err < 1e-13

    # ---------------------------------------------- (1) their stored test factors
    TF = json.load(open(r"..\P4_kl\blocks_testfactors.json"))
    Lth, Rmax = {}, {}
    for nm in ("T1", "C2", "K3", "CC4"):
        m, qe = q_block(nm)
        r = {tuple(int(u) for u in k.split(",")): Fr(v) for k, v in TF[nm]["r"].items()}
        assert all(v > 0 for v in r.values()) and len(r) == 4 * m * m
        worst = max(sum(r[(x, y, lam[x], lam[2 + y])] for x in range(2) for y in range(2))
                    for lam in itertools.product(range(m), repeat=4)) / 4
        assert worst <= 1
        L = iv.mpf(0)
        for c, v in r.items():
            L += qe[c] * iv.log(iv.mpf(v.numerator) / v.denominator) / 4
        Lth[nm] = L / LN2
        Rmax[nm] = {(x, y): max(r[(x, y, a, b)] for a in range(m) for b in range(m)) for x in range(2) for y in range(2)}
        print(f"[1] their r_{nm}: (F1) exact max over {m**4} strategies = {float(worst):.12f}; "
              f"L in [{float(mpf(Lth[nm].a)):.12f}, {float(mpf(Lth[nm].b)):.12f}] bits; "
              f"max entry {float(max(r.values())):.6f}")
    f2 = all(Rmax[j][(0, 0)] + Rmax[k][(1, 1)] <= 4 and Rmax[j][(0, 1)] + Rmax[k][(1, 0)] <= 4
             for j in Rmax for k in Rmax)
    print(f"[1] (F2) cross conditions for all ordered type pairs (exact): {f2}")
    L4 = Lth["CC4"]
    Lr = {0: iv.mpf(0), 1: Lth["T1"], 2: Lth["C2"], 3: Lth["K3"]}
    Cs = {rho: (4 * L4 + rho * Lr[rho]) / (4 + rho) for rho in range(4)}
    for rho in range(4):
        print(f"[1] C(4+{rho}) >= {float(mpf(Cs[rho].a)):.12f} bits")
    # monotonicity in k: C(4k+rho) = L4 - rho (L4 - L_rho)/(4k+rho), needs L_rho <= L4
    assert all(Lr[rho].b <= L4.a for rho in range(4))
    Cmin = min(Cs[rho].a for rho in range(4))
    print(f"[1] => S^UNI(B_d) >= {float(mpf(Cmin)):.12f} bits for all d >= 4 (given Lemma F)")

    # ---------------------------------------------- (2) own optimal test factors for the blocks
    for nm in ("C2", "K3", "CC4"):
        m, qe = q_block(nm)
        C = cells(m)
        qf = np.array([float(mpf(qe[c].mid)) for c in C])
        res = solve(qf, m)
        qiv = {c: qe[c] for c in C}
        lo, Mx = certify_lower(qiv, m, res["r"])
        up = certify_upper(qiv, m, res["y"])
        print(f"[2] own solver, block {nm}: S^UNI in [{float(lo):.12f}, {float(up):.12f}] bits "
              f"(float dual value {res['val'] / np.log(2):.12f}; exact M = {float(Mx):.12f})")

    # ---------------------------------------------- (3) full competitor B_d
    for d in range(4, dmax + 1):
        A, B, blocks = competitor_bases(d)
        for x in range(2):
            assert np.allclose(A[x].conj().T @ A[x], np.eye(d)) and np.allclose(B[x].conj().T @ B[x], np.eye(d))
        qf_dict = corr_from_bases(A, B)
        qiv = q_competitor_iv(d, blocks)
        err = max(abs(qf_dict[c] - float(mpf(qiv[c].mid))) for c in qf_dict)
        C = cells(d)
        qf = np.array([qf_dict[c] for c in C])
        qf[qf < 1e-15] = 0.0
        res = solve(qf, d)
        lo, Mx = certify_lower(qiv, d, res["r"])
        up = certify_upper(qiv, d, res["y"])
        k, rho = divmod(d, 4)
        Cd = (4 * k * L4 + rho * Lr[rho]) / d
        print(f"[3] d={d} ({[b[0] for b in blocks]}): |q(bases) - direct sum| = {err:.1e}; "
              f"S^UNI(B_d) in [{float(lo):.10f}, {float(up):.10f}] bits; C(d) = {float(mpf(Cd.mid)):.10f}", flush=True)
