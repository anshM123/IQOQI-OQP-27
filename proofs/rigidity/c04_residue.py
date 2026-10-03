"""c04: checks for section 4 (NUMERICAL).
 (a) conjugate function of the step field: explicit formula (3.1) vs direct principal-value quadrature of
     int p.v. cot((theta - phi)/2) B(phi) dm(phi), at random interior points of random cells;
 (b) derivative formula d/dtheta [B_x, g] = (1/2pi) sum_j [B_x, B_j - B_{j-1}] cot((theta - t_j)/2) (vs central differences);
 (c) the Herglotz formula (3.2): H(r e^{i theta}) -> B(theta) + i g(theta) as r -> 1;
 (d) zero-length-cell blind spot (Remark 4.3): commuting optimal configuration V_k = diag(1, i^{-[k>=r0]}), site r's PVM replaced
     by a rotated (non-commuting) one; a cell vector with ell_r = 0 stays TIGHT, while a positive-cell certificate vector is strict
     and F < F_DKZ.
"""
import json, os
import numpy as np
from scipy.integrate import quad
from rcore import *

rng = np.random.default_rng(11)
d, M = 4, 3
N = 4 * d
V = random_family(d, M, rng)
Q = Q_from_family(V)
A, B = AB(Q)
ell = d * rng.dirichlet(np.ones(d))
t = 2 * PI * cell_endpoints(ell) / N
jumps = np.array([B[j] - B[j - 1] for j in range(N)])


def g_formula(th):
    return np.einsum('j,jab->ab', np.log(np.abs(np.sin((th - t[:N]) / 2))), jumps) / PI


def g_quad(th, a, b_):
    """p.v. quadrature, entry (a, b_) of g(theta)."""
    tot = 0.0
    for y in range(N):
        lo, hi = t[y], t[y + 1]
        f = lambda phi: 1.0 / np.tan((th - phi) / 2) / (2 * PI)
        if lo < th < hi:
            val = quad(f, lo, hi, weight='cauchy', wvar=th, limit=200)[0] if False else None
            # p.v.: integrate cot((th - phi)/2) = 2/(th - phi) + smooth; use symmetric excision
            e = min(th - lo, hi - th) * 0.999
            s1 = quad(lambda u: (f(th - u) + f(th + u)), 1e-300, e, limit=200)[0]   # symmetric part cancels singularity
            s2 = quad(f, lo, th - e, limit=200)[0] + quad(f, th + e, hi, limit=200)[0]
            val = s1 + s2
        else:
            val = quad(f, lo, hi, limit=200)[0]
        tot += val * B[y][a, b_]
    return tot


errs = []
for trial in range(6):
    x = int(rng.integers(0, N))
    th = t[x] + (t[x + 1] - t[x]) * rng.uniform(0.1, 0.9)
    G = g_formula(th)
    a, b_ = int(rng.integers(0, M)), int(rng.integers(0, M))
    errs.append(abs(G[a, b_] - g_quad(th, a, b_)))
print(f"(a) |g formula - p.v. quadrature| max over 6 points: {max(errs):.2e}")

errs = []
for trial in range(6):
    x = int(rng.integers(0, N))
    th = t[x] + (t[x + 1] - t[x]) * rng.uniform(0.2, 0.8)
    h = 1e-5
    fd = ((B[x] @ g_formula(th + h) - g_formula(th + h) @ B[x]) - (B[x] @ g_formula(th - h) - g_formula(th - h) @ B[x])) / (2 * h)
    cot = 1 / np.tan((th - t[:N]) / 2)
    an = sum(cot[j] * (B[x] @ jumps[j] - jumps[j] @ B[x]) for j in range(N)) / (2 * PI)
    errs.append(np.max(np.abs(fd - an)) / max(1.0, np.max(np.abs(an))))
print(f"(b) derivative formula rel. error max: {max(errs):.2e}")


def H_of(z):
    out = 0.25 * np.eye(M, dtype=complex)
    for j in range(N):
        out = out + (1j / PI) * jumps[j] * np.log(1 - z * np.exp(-1j * t[j]))
    return out


x = 5
th = 0.5 * (t[x] + t[x + 1])
target = B[x] + 1j * g_formula(th)
for r in (0.9, 0.99, 0.999, 0.99999):
    print(f"(c) r={r}: ||H(r e^ith) - (B + i g)|| = {np.linalg.norm(H_of(r * np.exp(1j * th)) - target):.2e}")
# H(0) and the Herglotz integral at an interior point
z0 = 0.3 + 0.2j
Hq = np.zeros((M, M), complex)
for y in range(N):
    re = quad(lambda p: ((np.exp(1j * p) + z0) / (np.exp(1j * p) - z0)).real / (2 * PI), t[y], t[y + 1])[0]
    im = quad(lambda p: ((np.exp(1j * p) + z0) / (np.exp(1j * p) - z0)).imag / (2 * PI), t[y], t[y + 1])[0]
    Hq += (re + 1j * im) * B[y]
print(f"(c) closed form vs Herglotz integral at z = {z0}: {np.linalg.norm(H_of(z0) - Hq):.2e};  ||H(0) - I/4|| = "
      f"{np.linalg.norm(H_of(0) - 0.25 * np.eye(M)):.2e}")

# (d) blind spot
d = 5
N = 4 * d
r0, rbad = 2, 3
V0 = np.array([np.diag([1.0, (1j) ** (-(1 if k >= r0 else 0))]) for k in range(d)])
U = haar(2, rng)
Vb = V0.copy()
Vb[rbad] = U @ np.diag([1.0, -1.0]) @ U.conj().T          # site rbad: a different, rotated PVM (eigenvalues 1, -1)
Qb = Q_from_family(Vb)
Ab, Bb = AB(Qb)
Pb = pair_matrix(Ab, Bb)
PHI = N ** 2 * phic(0.25, 0.25)
ell0 = d * rng.dirichlet(np.ones(d))
ell0[rbad] = 0.0
ell0 *= d / ell0.sum()
cert = json.load(open(os.path.join(os.path.dirname(__file__), '..', '..', 'cone-certificates', 'certs', f'cert_d{d}.json')))
ellc = np.array(cert['cells'][0], float) / cert['q']
print(f"(d) d={d}: F(Vb) - F_DKZ = {F_clock(Vb) - F_DKZ(d):.4f};  max ||[Q_x,Q_y]|| = {commutator_norm(Qb):.3f}")
print(f"    zero-cell vector ell (ell_{rbad} = 0): Q^ell - N^2 Phi_c = {float(np.sum(cell_kernel(ell0) * Pb)) - PHI:.2e}  (tight: blind)")
print(f"    positive certificate cell vector     : Q^ell - N^2 Phi_c = {float(np.sum(cell_kernel(ellc) * Pb)) - PHI:.4f}  (strict)")
