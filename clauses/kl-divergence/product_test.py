"""
product_test.py -- composite d: tensor products of lower-dimensional optimal strategies on the
maximally entangled state |Phi_{d1 d2}> = |Phi_{d1}> (x) |Phi_{d2}>, with SHARED settings
(Alice's setting x is used in both factors).  Compare with DKZ on |Phi_d>:
  (i) KL statistical strength (uniform settings), (ii) critical visibility against ALL Bell
  inequalities of the (2,2,d) scenario (LP), (iii) CGLMP value.
"""
import numpy as np
from bell22d import dkz_bases, maxent, probs_pure, kl_strength, critical_visibility, cglmp_I

LOG2 = np.log(2)


def chsh_bases():
    """optimal CHSH qubit bases on |Phi_2> = (|00>+|11>)/sqrt2 (real): Alice Z, X; Bob (Z+X)/sqrt2, (Z-X)/sqrt2."""
    def basis(theta):
        # eigenbasis of cos(theta) Z + sin(theta) X  (columns: outcome 0 -> +1, outcome 1 -> -1)
        return np.array([[np.cos(theta / 2), -np.sin(theta / 2)],
                         [np.sin(theta / 2), np.cos(theta / 2)]], dtype=complex)
    A = [basis(0.0), basis(np.pi / 2)]
    B = [basis(np.pi / 4), basis(-np.pi / 4)]
    return A, B


def tensor_strategy(S1, S2):
    """S = (A, B, psi_mat); returns tensor product strategy (outcome a = a1*d2 + a2)."""
    A1, B1, P1 = S1
    A2, B2, P2 = S2
    A = [np.kron(A1[x], A2[x]) for x in range(2)]
    B = [np.kron(B1[y], B2[y]) for y in range(2)]
    P = np.kron(P1, P2)
    return A, B, P


def report(name, A, B, P):
    q = probs_pure(P, A, B)
    r = kl_strength(q)
    v, beta = critical_visibility(q)
    print(f"{name:34s} I_CGLMP = {cglmp_I(q):.8f}  v_c(all Bell ineq.) = {v:.8f}  "
          f"KL = [{r['lb']/LOG2:.8f}, {r['kl']/LOG2:.8f}] bits", flush=True)
    return q, r, v


if __name__ == "__main__":
    Ac, Bc = chsh_bases()
    chsh = (Ac, Bc, maxent(2))
    report("CHSH d=2", *chsh)
    for d in (3, 4, 5, 6):
        A, B = dkz_bases(d)
        report(f"DKZ on Phi_{d}", A, B, maxent(d))
    # composite
    A3, B3 = dkz_bases(3)
    dkz3 = (A3, B3, maxent(3))
    report("CHSH x CHSH on Phi_4", *tensor_strategy(chsh, chsh))
    report("CHSH x DKZ3 on Phi_6", *tensor_strategy(chsh, dkz3))
    report("DKZ3 x CHSH on Phi_6", *tensor_strategy(dkz3, chsh))
