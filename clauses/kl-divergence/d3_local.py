"""
d3_local.py -- numerical second-order analysis of the KL strength at DKZ_3 on Phi_3 (all rank-one PVMs).

Exact KKT data (d = 3): CGLMP levels g'_xy(a,b): g'_00 = g'_11 = (a-b) mod 3, g'_10 = (b-a) mod 3, g'_01 = (b-a-1) mod 3;
every deterministic strategy has sum_xy g'_xy >= 2 (CGLMP_3, Pi-form), with equality on 30 strategies (the facet).
Test factor r* = 1 + beta (1/2 - g'), beta root of  sum_k Q_k (1/2-k)/(1+beta(1/2-k)) = 0,  Q = DKZ_3 level law
(2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9).  p* = q0/r* lies in the relative interior of the CGLMP facet.
Upper-bound function  f(theta) = min_{p in aff(facet), p near p*} sum_xy (1/4) D(q_xy(theta) || p_xy)  >= S^UNI.
Hessian along v:  v^T H v = (1/4)[ sum (d_v^2 q) log r*  +  min_{u in V} sum (d_v q - r* u)^2 / q ],
V = { u : sum_ab u(ab|xy) = 0, no-signalling, CGLMP(u) = 0 } (direction space of the facet's affine hull).
S^COR: same with the extra linear constraint  (sum_ab r*_xy u_xy)_xy = (d_v D(q_xy||p*_xy))_xy  (link equalisation).
"""
import sys
import itertools
import numpy as np
sys.path.insert(0, ".")
from bell22d import dkz_bases, maxent, probs_pure, kl_strength

d = 3
LOG2 = np.log(2)
A0, B0 = dkz_bases(d)
U0 = A0 + B0


def gprime(x, y, a, b):
    if (x, y) in ((0, 0), (1, 1)):
        return (a - b) % 3
    if (x, y) == (1, 0):
        return (b - a) % 3
    return (b - a - 1) % 3


G = np.zeros((2, 2, 3, 3), int)
for x, y, a, b in itertools.product(range(2), range(2), range(3), range(3)):
    G[x, y, a, b] = gprime(x, y, a, b)

# check the CGLMP Pi-form bound over all 81 deterministic strategies
sums = []
for a0, a1, b0, b1 in itertools.product(range(3), repeat=4):
    lam = (a0, a1, b0, b1)
    sums.append(sum(G[x, y, lam[x], lam[2 + y]] for x in range(2) for y in range(2)))
sums = np.array(sums)
print("min sum g' over deterministic strategies:", sums.min(), " #saturating:", np.sum(sums == 2))

s3 = np.sqrt(3)
Qlev = np.array([2 * (2 + s3) / 9, 2 * (2 - s3) / 9, 1 / 9])
# beta: Q0 r1 r2 - Q1 r0 r2 - 3 Q2 r0 r1 = 0 with r0 = 1+b/2, r1 = 1-b/2, r2 = 1-3b/2  (quadratic in b)
P = np.polynomial.polynomial
r0 = np.array([1, 0.5]); r1 = np.array([1, -0.5]); r2 = np.array([1, -1.5])
poly = Qlev[0] * P.polymul(r1, r2) - Qlev[1] * P.polymul(r0, r2) - 3 * Qlev[2] * P.polymul(r0, r1)
roots = P.polyroots(poly)
beta = [b.real for b in roots if abs(b.imag) < 1e-12 and 0 < b.real < 2 / 3][0]
rlev = 1 + beta * (0.5 - np.arange(3))
S0 = np.sum(Qlev * np.log(rlev))
print(f"beta = {beta:.15f}; r* levels = {rlev}; S(DKZ_3) closed form = {S0/LOG2:.13f} bits")
q0 = probs_pure(maxent(d), A0, B0)
num = kl_strength(q0)
print(f"numerical solver: [{num['lb']/LOG2:.13f}, {num['kl']/LOG2:.13f}] bits")
rstar = 1 + beta * (0.5 - G)
pstar = q0 / rstar
print("p* normalisation per link:", [round(pstar[x, y].sum(), 14) for x in range(2) for y in range(2)])
print("max |p* - solver p*|:", np.abs(pstar - num['p']).max())

# ---------------- parametrisation
def herm_basis():
    Hs = []
    for i in range(d):
        H = np.zeros((d, d), complex); H[i, i] = 1; Hs.append(H)
    for i in range(d):
        for j in range(i + 1, d):
            H = np.zeros((d, d), complex); H[i, j] = H[j, i] = 1; Hs.append(H)
            H = np.zeros((d, d), complex); H[i, j] = -1j; H[j, i] = 1j; Hs.append(H)
    return Hs


Hs = herm_basis()
n = 4 * d * d


def expm_h(H):
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * w)) @ V.conj().T


def qz(z):
    Us = [expm_h(sum(z[m * 9 + i] * Hs[i] for i in range(9))) @ U0[m] for m in range(4)]
    return probs_pure(maxent(d), Us[:2], Us[2:])


h = 1e-4
E = np.eye(n)
J = np.array([(qz(h * E[i]) - qz(-h * E[i])) / (2 * h) for i in range(n)])        # n x (2,2,3,3)
logr = np.log(rstar)
# Pi_k gradients
for k in range(3):
    gk = np.array([np.sum(J[i][G == k]) for i in range(n)])
    print(f"|grad Pi_{k}| = {np.linalg.norm(gk):.2e}")
gradF = np.array([np.sum(J[i] * logr) for i in range(n)]) / 4
print(f"|grad <q, log r*>/4| = {np.linalg.norm(gradF):.2e}")

# Hessian of F(z) = <q(z), log r*>/4 by central differences
F = lambda z: np.sum(qz(z) * logr) / 4
HF = np.zeros((n, n))
hh = 1e-3
f0 = F(np.zeros(n))
fp = [F(hh * E[i]) for i in range(n)]
fm = [F(-hh * E[i]) for i in range(n)]
for i in range(n):
    HF[i, i] = (fp[i] - 2 * f0 + fm[i]) / hh ** 2
    for j in range(i + 1, n):
        HF[i, j] = HF[j, i] = (F(hh * (E[i] + E[j])) - fp[i] - fp[j] + 2 * f0 - fm[i] - fm[j] + F(-hh * (E[i] + E[j]))) / (2 * hh ** 2)

# V: u in R^36 (cells), NS-linear and CGLMP-zero
cells = list(itertools.product(range(2), range(2), range(3), range(3)))
idx = {c: i for i, c in enumerate(cells)}
rows = []
for x, y in itertools.product(range(2), repeat=2):          # normalisation
    v = np.zeros(36)
    for a, b in itertools.product(range(3), repeat=2):
        v[idx[(x, y, a, b)]] = 1
    rows.append(v)
for x in range(2):                                          # Alice marginal independent of y
    for a in range(3):
        v = np.zeros(36)
        for b in range(3):
            v[idx[(x, 0, a, b)]] += 1
            v[idx[(x, 1, a, b)]] -= 1
        rows.append(v)
for y in range(2):
    for b in range(3):
        v = np.zeros(36)
        for a in range(3):
            v[idx[(0, y, a, b)]] += 1
            v[idx[(1, y, a, b)]] -= 1
        rows.append(v)
v = np.array([G[c] for c in cells], float)                  # CGLMP Pi-form functional
rows.append(v)
Cmat = np.array(rows)
_, sv, Vt = np.linalg.svd(Cmat)
rank = np.sum(sv > 1e-10)
Vb = Vt[rank:].T                                            # 36 x dimV
print("dim V =", Vb.shape[1], "(expected 23)")
qf = q0.reshape(-1)
rf = rstar.reshape(-1)
Jf = J.reshape(n, -1)
# min_{u in V} sum (dq - r u)^2/q  -> least squares in weighted norm
Wq = 1 / np.sqrt(qf)
Mrv = (rf[:, None] * Vb) * Wq[:, None]
proj = Mrv @ np.linalg.pinv(Mrv)
R = (Jf * Wq[None, :])                                      # n x 36
Rres = R - R @ proj.T
HP = Rres @ Rres.T / 4
H_uni = HF + HP
# gauge tangent space
gauge = []
for m in range(4):
    for a in range(3):
        Hm = U0[m] @ np.diag(np.eye(3)[a]) @ U0[m].conj().T
        zv = np.zeros(n)
        # express Hm in the Hs basis: Hs real basis coefficients
        M = np.array([[np.real(np.trace(Hs[i].conj().T @ Hs[j])) for j in range(9)] for i in range(9)])
        c = np.linalg.solve(M, np.array([np.real(np.trace(Hs[i].conj().T @ Hm)) for i in range(9)]))
        zv[m * 9:(m + 1) * 9] = c
        gauge.append(zv)
Mg = np.array([[np.real(np.trace(Hs[i].conj().T @ Hs[j])) for j in range(9)] for i in range(9)])
for i in range(9):          # common unitary: A -> W A, B -> conj(W) B : H_A = h, H_B = -conj(h)
    h_ = Hs[i]
    zv = np.zeros(n)
    for m in range(2):
        zv[m * 9:(m + 1) * 9] = np.linalg.solve(Mg, np.array([np.real(np.trace(Hs[j].conj().T @ h_)) for j in range(9)]))
    hb = -h_.conj()
    for m in range(2, 4):
        zv[m * 9:(m + 1) * 9] = np.linalg.solve(Mg, np.array([np.real(np.trace(Hs[j].conj().T @ hb)) for j in range(9)]))
    gauge.append(zv)
Gm = np.array(gauge).T
ug, sg, _ = np.linalg.svd(Gm, full_matrices=True)
rg = np.sum(sg > 1e-9)
print("gauge tangent dimension:", rg)
Tc = ug[:, rg:]                                              # orthonormal complement (slice directions)
for name, H in (("H_UNI", H_uni),):
    Hs_ = Tc.T @ H @ Tc
    ev = np.linalg.eigvalsh((Hs_ + Hs_.T) / 2)
    print(f"{name} on slice ({Tc.shape[1]} dims): eigenvalues max {ev.max():+.4e} min {ev.min():+.4e}")
    evg = np.linalg.eigvalsh(Gm.T @ H @ Gm)
    print(f"{name} on gauge directions: max |.| {np.abs(evg).max():.1e}")
np.savez("d3_local_data.npz", H_uni=H_uni, HF=HF, HP=HP, Tc=Tc, J=J, beta=beta)

# ---------------- S^COR: constrained first-order correction (link equalisation)
# gamma_xy(v) = sum_{xy cells} d_v q log r*;  constraint: sum_{xy cells} r* u = gamma_xy(v), u in V
links = [(0, 0), (0, 1), (1, 0), (1, 1)]
Lmask = np.array([[1.0 if (c[0], c[1]) == l else 0.0 for c in cells] for l in links])     # 4 x 36
Rlin = Lmask * rf[None, :]                                                                 # 4 x 36: u -> sum r* u per link
RV = Rlin @ Vb                                                                             # 4 x dimV
print("rank of R restricted to V:", np.linalg.matrix_rank(RV, tol=1e-10), "(expected 3)")
gam = (Jf * logr.reshape(-1)[None, :]) @ Lmask.T                                         # n x 4
print("max |sum_xy gamma_xy| over directions:", np.abs(gam.sum(1)).max())
# for each direction e_i: minimise ||W(q1 - r* Vb c)||^2 s.t. RV c = gamma_i  (KKT)
A_ls = (rf[:, None] * Vb) * Wq[:, None]              # 36 x k
k = Vb.shape[1]
U, s_, Wt = np.linalg.svd(RV)
# use 3 independent constraint rows (drop the dependent sum)
Rc = RV[:3]
Hc = np.zeros((n, n))
Cs = []
for i in range(n):
    b = Jf[i] * Wq
    KKT = np.block([[2 * A_ls.T @ A_ls, Rc.T], [Rc, np.zeros((3, 3))]])
    rhs = np.concatenate([2 * A_ls.T @ b, gam[i, :3]])
    sol = np.linalg.lstsq(KKT, rhs, rcond=None)[0]
    Cs.append(sol[:k])
Cs = np.array(Cs)                                   # n x k : u_i = Vb c_i
res = (Jf * Wq[None, :]) - (Cs @ A_ls.T)            # n x 36
HPc = res @ res.T / 4
H_cor = HF + HPc
for name, H in (("H_UNI", H_uni), ("H_COR", H_cor)):
    Hs_ = Tc.T @ H @ Tc
    ev = np.linalg.eigvalsh((Hs_ + Hs_.T) / 2)
    print(f"{name} on slice: eigenvalues max {ev.max():+.4e} min {ev.min():+.4e}")
print("check equalisation residual:", np.abs((Cs @ (Rlin @ Vb).T) - gam).max())
np.savez("d3_local_data.npz", H_uni=H_uni, H_cor=H_cor, HF=HF, HP=HP, HPc=HPc, Tc=Tc, J=J, beta=beta, Cs=Cs, Vb=Vb)
