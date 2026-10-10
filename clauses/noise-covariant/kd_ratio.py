"""
kd_ratio.py -- max-ent ratios of the facet classes of K_d (link-difference Bell functionals).

A facet of K_d: sum_i c_i(n_i) <= 0 on deterministic points (n1 = b0-a0, n2 = a0-b1, n3 = a1-b0, n4 = b1-a1).
As a Bell functional F(p) = sum_xy sum_m c'_xy(m) Q_xy(m), Q_xy(m) = P(b_y - a_x = m):
   c'_00(m) = c_1(m), c'_01(m) = c_2(-m), c'_10(m) = c_3(-m), c'_11(m) = c_4(m).
Fourier: for balanced max-ent strategies (clock unitaries A_x, B_y, tracial state),
   F(p) - F(u) = (1/d) sum_{k=1}^{d-1} Re sum_xy chat_xy(k) <A_x^k, B_y^k>,  chat(k) = sum_m c'(m) w^{-km},
with unit vectors A_x^k, B_y^k.  Level-1 ("per-mode") bound:  F_ME - F(u) <= (1/d) sum_k T(chat(k)),
   T(M) = max over unit vectors u_x, v_y of Re sum_xy M_xy <u_x, v_y>
        = max_{|g| <= 1} sum_y sqrt(|M_0y|^2 + |M_1y|^2 + 2 Re(conj(M_0y) M_1y g))   (g = <u_0, u_1>).
Ratio R(F) = (F_ME - F(u)) / (0 - F(u)); C2 for covariant behaviours <=> R <= kappa_d for every non-positivity class.
Numerics here (lower bounds by optimisation over DFT+phase strategies and over general rank-one strategies).
"""
import sys
import json
import math
import numpy as np
from scipy.optimize import minimize


def i_me(d):
    j = np.arange(1, d)
    return 4.0 / (d * (d - 1)) * float(np.sum((d - j) / np.cos(np.pi * j / (2 * d))))


def cprime(c, d):
    c = np.asarray(c, float)
    cp = np.zeros((2, 2, d))
    for m in range(d):
        cp[0, 0, m] = c[0, m]
        cp[0, 1, m] = c[1, (-m) % d]
        cp[1, 0, m] = c[2, (-m) % d]
        cp[1, 1, m] = c[3, m]
    return cp


def T_bound(M, ngrid=400):
    """max_{|g|<=1} sum_y sqrt(|M0y|^2+|M1y|^2+2Re(conj(M0y)M1y g)); concave in g -> grid + local refine."""
    def f(g):
        s = 0.0
        for y in range(2):
            v = abs(M[0, y]) ** 2 + abs(M[1, y]) ** 2 + 2 * (np.conj(M[0, y]) * M[1, y] * g).real
            s += math.sqrt(max(v, 0.0))
        return s
    best = (-1, 0)
    for r in np.linspace(0, 1, 21):
        for t in np.linspace(0, 2 * np.pi, 72, endpoint=False):
            g = r * np.exp(1j * t)
            v = f(g)
            if v > best[0]:
                best = (v, g)
    g0 = best[1]
    res = minimize(lambda z: -f(complex(z[0], z[1])) if z[0] ** 2 + z[1] ** 2 <= 1 else 1e9,
                   [g0.real, g0.imag], method="Nelder-Mead", options={"xatol": 1e-12, "fatol": 1e-14})
    return max(best[0], -res.fun)


def level1(c, d):
    cp = cprime(c, d)
    w = np.exp(2j * np.pi / d)
    Fu = cp.sum() / d
    tot = 0.0
    for k in range(1, d):
        M = np.array([[sum(cp[x, y, m] * w ** (-k * m) for m in range(d)) for y in range(2)] for x in range(2)])
        tot += T_bound(M)
    return Fu, Fu + tot / d


def F_value(c, d, Q):
    """Q[x,y,m] link-difference laws"""
    return float((cprime(c, d) * Q).sum())


def dftphase_Q(theta, d):
    """DFT + diagonal phase strategy: link law Q_xy(m) = |(1/d) sum_k w^{km} e^{i psi_xy(k)}|^2,
    psi_xy = th_A[x] - th_B[y] (phases on k = 1..d-1; k = 0 phase 0)."""
    th = np.concatenate([np.zeros((4, 1)), np.asarray(theta).reshape(4, d - 1)], axis=1)
    w = np.exp(2j * np.pi / d)
    k = np.arange(d)
    Q = np.zeros((2, 2, d))
    for x in range(2):
        for y in range(2):
            psi = th[x] - th[2 + y]
            for m in range(d):
                Q[x, y, m] = abs(np.sum(w ** (k * m) * np.exp(1j * psi)) / d) ** 2
    return Q


def general_Q(z, d):
    """general rank-one PVM strategy on Phi_d (4 unitaries from a real vector), link-difference laws."""
    z = np.asarray(z).reshape(4, d, d, 2)
    U = []
    for i in range(4):
        Z = z[i, :, :, 0] + 1j * z[i, :, :, 1]
        Qm, R = np.linalg.qr(Z)
        U.append(Qm)
    Q = np.zeros((2, 2, d))
    for x in range(2):
        for y in range(2):
            P = np.abs(U[x].conj().T @ U[2 + y]) ** 2 / d          # p(a,b) with Bt convention
            for a in range(d):
                for b in range(d):
                    Q[x, y, (b - a) % d] += P[a, b]
    return Q


def maximise(c, d, family, starts, rng):
    best = -np.inf
    nvar = 4 * (d - 1) if family == "dft" else 4 * d * d * 2
    fn = (lambda z: -F_value(c, d, dftphase_Q(z, d))) if family == "dft" else \
         (lambda z: -F_value(c, d, general_Q(z, d)))
    for s in range(starts):
        z0 = rng.uniform(0, 2 * np.pi, nvar) if family == "dft" else rng.standard_normal(nvar)
        res = minimize(fn, z0, method="BFGS", options={"gtol": 1e-9, "maxiter": 4000})
        best = max(best, -res.fun)
    return best


if __name__ == "__main__":
    d = int(sys.argv[1])
    starts = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    rng = np.random.default_rng(11)
    kap = i_me(d) / 2
    classes = json.load(open(f"kd_facets_d{d}.json"))
    print(f"d={d} kappa_d={kap:.10f}")
    for cl in classes:
        c = np.array(cl["c"])
        if cl["tight"] == len([1 for _ in range(d ** 3)]) - 0:
            pass
        Fu, ub = level1(c, d)
        if abs(Fu) < 1e-12:
            print("  skip (F(u)=0?)", cl["c"]); continue
        lb_dft = maximise(c, d, "dft", starts, rng)
        lb_gen = maximise(c, d, "gen", max(4, starts // 4), rng) if d <= 5 else float("nan")
        r_ub = (ub - Fu) / (0 - Fu)
        r_dft = (lb_dft - Fu) / (0 - Fu)
        r_gen = (lb_gen - Fu) / (0 - Fu)
        print(f"  class size {cl['size']:5d} tight {cl['tight']:4d} c={cl['c']}\n"
              f"     F(u)={Fu:.6f}  ratio: level-1 UB {r_ub:.8f}   DFT+phase LB {r_dft:.8f}   general LB {r_gen:.8f}"
              f"   kappa_d {kap:.8f}", flush=True)
