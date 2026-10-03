"""
d3_check.py -- independent float cross-check of the d = 3 certificate (d3_cert.py): finite-difference Hessians
of the four link functions phi_xy(s) = D(q_xy(z(s)) || p*_xy + u1(s)_xy) along the coordinate slice, where
q(z) is computed from matrix exponentials (scipy-free eigh route, as in d3_local.py) and u1(s) = sum_i s_i U_i is
the certified link-equalising correction.  Checks: gradients of all four phi_xy vanish; the average Hessian equals
the exact Hbar; plus a direct check that S^UNI (full solver) along random slice directions stays below S(DKZ_3).
"""
import sys
import itertools
import numpy as np
sys.path.insert(0, ".")
from bell22d import dkz_bases, maxent, probs_pure, kl_strength

D = np.load("d3_cert_data.npz")
I_sl, Hbar, Uc, beta = D["I_sl"], D["Hbar"], D["U"], float(D["beta"])
A0, B0 = dkz_bases(3)
U0 = A0 + B0


def herm_basis():
    Hs = []
    for i in range(3):
        H = np.zeros((3, 3), complex); H[i, i] = 1; Hs.append(H)
    for i in range(3):
        for j in range(i + 1, 3):
            H = np.zeros((3, 3), complex); H[i, j] = H[j, i] = 1; Hs.append(H)
            H = np.zeros((3, 3), complex); H[i, j] = -1j; H[j, i] = 1j; Hs.append(H)
    return Hs


Hs = herm_basis()


def expm_h(H):
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * w)) @ V.conj().T


def qz(z):
    Us = [expm_h(sum(z[m * 9 + i] * Hs[i] for i in range(9))) @ U0[m] for m in range(4)]
    return probs_pure(maxent(3), Us[:2], Us[2:])


def gp(x, y, a, b):
    if (x, y) in ((0, 0), (1, 1)):
        return (a - b) % 3
    if (x, y) == (1, 0):
        return (b - a) % 3
    return (b - a - 1) % 3


LINKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
CELLS = [(x, y, a, b) for (x, y) in LINKS for a in range(3) for b in range(3)]
LEV = np.array([gp(*c) for c in CELLS])
rst = 1 + beta * (0.5 - LEV)
q0 = qz(np.zeros(36))
q0v = np.array([q0[c] for c in CELLS])
pst = q0v / rst


def phis(s):
    z = np.zeros(36)
    z[I_sl] = s
    q = qz(z)
    qv = np.array([q[c] for c in CELLS])
    p = pst + s @ Uc
    out = []
    for L in LINKS:
        m = np.array([c[:2] == L for c in CELLS])
        out.append(np.sum(qv[m] * np.log(qv[m] / p[m])))
    return np.array(out)


ns = len(I_sl)
h = 1e-4
E = np.eye(ns)
f0 = phis(np.zeros(ns))
print("phi_xy(0) (nats):", f0, " all equal S0 =", f0.mean())
G = np.array([(phis(h * E[i]) - phis(-h * E[i])) / (2 * h) for i in range(ns)])
print("max |grad phi_xy| over links and slice directions:", np.abs(G).max())
Hl = np.zeros((4, ns, ns))
hh = 1e-3
fp = [phis(hh * E[i]) for i in range(ns)]
fm = [phis(-hh * E[i]) for i in range(ns)]
for i in range(ns):
    Hl[:, i, i] = (fp[i] - 2 * f0 + fm[i]) / hh ** 2
    for j in range(i + 1, ns):
        val = (phis(hh * (E[i] + E[j])) - fp[i] - fp[j] + 2 * f0 - fm[i] - fm[j] + phis(-hh * (E[i] + E[j]))) / (2 * hh ** 2)
        Hl[:, i, j] = Hl[:, j, i] = val
Havg = Hl.mean(0)
print("max |Havg (finite differences) - Hbar (exact)|:", np.abs(Havg - Hbar).max())
for l, L in enumerate(LINKS):
    print(f"  link {L}: eigenvalues of its own Hessian: max {np.linalg.eigvalsh(Hl[l]).max():+.5f}")
print("Hbar eigenvalues: max", np.linalg.eigvalsh(Hbar).max(), "min", np.linalg.eigvalsh(Hbar).min())
# direct check with the full solver along random slice directions
rng = np.random.default_rng(1)
S0 = kl_strength(q0)["lb"]
worst = -1
for t in range(20):
    v = rng.normal(size=ns)
    v /= np.linalg.norm(v)
    for eps in (0.02, 0.05, 0.1):
        z = np.zeros(36)
        z[I_sl] = eps * v
        Sv = kl_strength(qz(z))["kl"]
        worst = max(worst, (Sv - S0) / eps ** 2)
print(f"max over 60 samples of (S^UNI(z) - S0)/|z|^2 = {worst:.5f}  (negative => decrease, as certified)")
