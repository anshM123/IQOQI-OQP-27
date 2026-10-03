"""
competitor_check.py -- independent numerical check of the block competitors (Lemma B, Lemma F):
builds the actual orthonormal bases on C^d (block-diagonal: k copies of the CHSH (x) CHSH bases on C^4 plus a
remainder block CHSH (C^2) / DKZ_3 (C^3) / trivial (C^1)), computes q(a,b|x,y) = |<a_x|<b_y|Phi_d>|^2 directly,
checks q against the direct-sum formula sum_j (m_j/d) q_j, and computes the full-scenario KL strength (uniform
settings) with the generic solver over all d^4 deterministic strategies; compares with C(d) and with DKZ_d.
usage: python competitor_check.py d1 d2 ...
"""
import sys
import numpy as np
sys.path.insert(0, ".")
from bell22d import probs_pure, maxent, dkz_bases, kl_strength
from product_test import chsh_bases

LOG2 = np.log(2)


def block_bases(d):
    """returns A[x], B[y] (d x d, columns = basis vectors, column index = outcome)"""
    Ac, Bc = chsh_bases()
    A4 = [np.kron(Ac[x], Ac[x]) for x in range(2)]
    B4 = [np.kron(Bc[y], Bc[y]) for y in range(2)]
    A3, B3 = dkz_bases(3)
    k, rho = divmod(d, 4)
    blocksA = [A4] * k
    blocksB = [B4] * k
    if rho == 1:
        blocksA.append([np.eye(1)] * 2)
        blocksB.append([np.eye(1)] * 2)
    elif rho == 2:
        blocksA.append(Ac)
        blocksB.append(Bc)
    elif rho == 3:
        blocksA.append(A3)
        blocksB.append(B3)
    A, B = [], []
    for x in range(2):
        M = np.zeros((d, d), complex)
        N = np.zeros((d, d), complex)
        o = 0
        for bA, bB in zip(blocksA, blocksB):
            m = bA[x].shape[0]
            M[o:o + m, o:o + m] = bA[x]
            N[o:o + m, o:o + m] = bB[x]
            o += m
        A.append(M)
        B.append(N)
    return A, B, k, rho


if __name__ == "__main__":
    for d in map(int, sys.argv[1:]):
        A, B, k, rho = block_bases(d)
        for x in range(2):
            assert np.allclose(A[x].conj().T @ A[x], np.eye(d)) and np.allclose(B[x].conj().T @ B[x], np.eye(d))
        q = probs_pure(maxent(d), A, B)
        # direct-sum formula check
        qb = np.zeros_like(q)
        Ac, Bc = chsh_bases()
        q4 = probs_pure(maxent(4), [np.kron(Ac[x], Ac[x]) for x in range(2)], [np.kron(Bc[y], Bc[y]) for y in range(2)])
        for j in range(k):
            qb[:, :, 4 * j:4 * j + 4, 4 * j:4 * j + 4] = (4 / d) * q4
        if rho:
            if rho == 1:
                qr = np.ones((2, 2, 1, 1))
            elif rho == 2:
                qr = probs_pure(maxent(2), Ac, Bc)
            else:
                A3, B3 = dkz_bases(3)
                qr = probs_pure(maxent(3), A3, B3)
            qb[:, :, 4 * k:, 4 * k:] = (rho / d) * qr
        err = np.abs(q - qb).max()
        r = kl_strength(q)
        Ad, Bd = dkz_bases(d)
        rd = kl_strength(probs_pure(maxent(d), Ad, Bd))
        print(f"d={d} (4*{k}+{rho}): |q - direct-sum formula| = {err:.1e};  KL(competitor) in "
              f"[{r['lb']/LOG2:.10f}, {r['kl']/LOG2:.10f}] bits;  KL(DKZ_d) in [{rd['lb']/LOG2:.10f}, "
              f"{rd['kl']/LOG2:.10f}] bits", flush=True)
