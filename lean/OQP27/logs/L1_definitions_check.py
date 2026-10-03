"""Independent numerical check of the definitions of OQP27/Statement.lean and OQP27/Skeleton.lean (module L1).

Not part of any proof.  Every quantity is computed exactly as the Lean definitions read:
 (1) Statement.lean: p(a,b|x,y) = Re Tr(A_{x,a}^T B_{y,b}) / D; probAB/probBA; the CGLMP expression `Strategy.cglmp`;
     the DKZ projectors dkzA d x k = (d^{-1} z^{-(j-j')(4k + alpha4 x)}), dkzB d y l = (d^{-1} z^{(j-j')(4l - beta4 y)}),
     z = e^{2 pi i/(4d)}, alpha4 = (0, 2), beta4 = (1, -1): projections, sum to 1, CGLMP eq. (15), I_d(DKZ) = I_ME(d)
     (cross-checked against cglmp_standard of CGLMP/paper-classical-all-d/scripts/check_reduction.py).
 (2) Skeleton.lean `Hyp_Reduction`: for random projective strategies, with the Q-configuration produced by the twirl +
     Stone-von Neumann reduction of the paper (check_reduction.twirl_reduce) and Q_x = spectral projection of E_k = V_k^*
     for the eigenvalue i^a (x = k - d a):  I_d = I_ME(d) + 2/(d(d-1)) <v, delta>,
     T(m) = sum_y tau(Q_{y+m} Q_{y+d}), N(m) = T(m) - T(-m), delta_m = N(m) - m, v_m = 2/sin(pi m/(2d)).
 (3) Skeleton.lean `cellDirection` (kernel form, Clausen series): the stored CONE certificates satisfy
     sum_k lambda_k u^{ell_k} = v.
 (4) the cell inequalities <u^ell, delta> <= 0 on random configurations; delta = 0 on the DKZ window.
 (5) QD2-R2: two-residue cells give positive multiples of e_s + e_{d-s} (used to pass from the integral form of
     CONE_d, d >= 201, to the finite form `ConeCertPos`).
 (6) Skeleton.lean `hStrip`: the Poisson integral equals -(1/pi^2) Im Li2(e^{pi(y-lam)} e^{-i pi x}); kernel mass 1 - x.
Usage: python OQP27/logs/L1_definitions_check.py  (output: L1_definitions_check.log)
"""
import json
import sys
import numpy as np
import mpmath as mpm

import os
REPO = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))  # repository root
# check_reduction.py is in the CGLMP repository (https://github.com/anshM123/CGLMP, paper-classical-all-d/scripts);
# set CGLMP_REPO to a clone of it (default: a clone next to this repository).
CGLMP_REPO = os.environ.get("CGLMP_REPO", os.path.join(REPO, "..", "CGLMP"))
sys.path.insert(0, os.path.join(CGLMP_REPO, "paper-classical-all-d", "scripts"))
import check_reduction as cr  # noqa: E402

CERTS = os.path.join(REPO, "cone-certificates", "certs")
mpm.mp.dps = 30
rng = np.random.default_rng(20261002)
mp = np.linalg.matrix_power


def prob(A, B, D):
    d = len(A[0])
    P = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    P[x, y, a, b] = (np.trace(A[x][a].T @ B[y][b]) / D).real
    return P


def cglmp_lean(P):
    d = P.shape[2]

    def pAB(x, y, k):
        return sum(P[x, y, a, b] for a in range(d) for b in range(d) if (a - b - k) % d == 0)

    def pBA(x, y, k):
        return sum(P[x, y, a, b] for a in range(d) for b in range(d) if (b - a - k) % d == 0)

    I = 0.0
    for k in range(d // 2):
        c = 1 - 2 * k / (d - 1)
        I += c * (pAB(0, 0, k) + pBA(1, 0, k + 1) + pAB(1, 1, k) + pBA(0, 1, k)
                  - pAB(0, 0, -k - 1) - pBA(1, 0, -k) - pAB(1, 1, -k - 1) - pBA(0, 1, -k - 1))
    return I


def IME(d):
    return 4 / (d * (d - 1)) * sum((d - j) / np.cos(np.pi * j / (2 * d)) for j in range(1, d))


def dkz(d):
    z = np.exp(2j * np.pi / (4 * d))
    a4, b4 = [0, 2], [1, -1]
    A = [[np.array([[z ** (-(j - jp) * (4 * k + a4[x])) / d for jp in range(d)] for j in range(d)])
          for k in range(d)] for x in range(2)]
    B = [[np.array([[z ** ((j - jp) * (4 * l - b4[y])) / d for jp in range(d)] for j in range(d)])
          for l in range(d)] for y in range(2)]
    return A, B


def qconfig_from_V(V, d):
    N = 4 * d
    Q = {}
    for k in range(d):
        E = V[k].conj().T
        for a in range(4):
            Q[(k - d * a) % N] = sum((1j ** (-a * n)) * mp(E, n) for n in range(4)) / 4
    return [Q[x] for x in range(N)]


def delta_of_Q(Q, d):
    N = 4 * d
    M = Q[0].shape[0]
    tau = lambda X: np.trace(X).real / M
    T = lambda m: sum(tau(Q[(y + m) % N] @ Q[(y + d) % N]) for y in range(N))
    Nm = lambda m: T(m) - T(-m)
    return np.array([Nm(m) - m for m in range(1, d)]), Nm


def vvec(d):
    return np.array([2 / np.sin(np.pi * m / (2 * d)) for m in range(1, d)])


def G(u, d):
    N = 4 * d
    return -(mpm.mpf(N) ** 2 / (2 * mpm.pi ** 2)) * mpm.clsin(2, 2 * mpm.pi * u / N)


def u_kernel(ell, d):
    L = [mpm.mpf(0)]
    for n in range(3 * d + 2):
        L.append(L[-1] + ell[n % d])
    K = lambda x, y: G(L[x + 1] - L[y], d) - G(L[x] - L[y], d) - G(L[x + 1] - L[y + 1], d) + G(L[x] - L[y + 1], d)
    Kt = lambda n: sum(K(r + n, r) for r in range(d)) / d
    return [Kt(m) + Kt(2 * d - m) for m in range(1, d)]


def main():
    print("(1) DKZ strategy with the Lean definitions:")
    for d in range(2, 10):
        A, B = dkz(d)
        err = 0
        for X in A + B:
            for k in range(d):
                M = X[k]
                err = max(err, abs(M - M.conj().T).max(), abs(M @ M - M).max())
            err = max(err, abs(sum(X) - np.eye(d)).max())
        P = prob(A, B, d)
        al, be = (0.0, 0.5), (0.25, -0.25)
        e15 = max(abs(P[x, y, k, l] - 1 / (2 * d ** 3 * np.sin(np.pi * (k - l + al[x] + be[y]) / d) ** 2))
                  for x in range(2) for y in range(2) for k in range(d) for l in range(d))
        print(f"  d={d}: projection/PVM err {err:.1e}, eq.(15) err {e15:.1e}, I_d(DKZ) = {cglmp_lean(P):.12f}, "
              f"I_ME(d) = {IME(d):.12f}, check_reduction.cglmp_standard = {cr.cglmp_standard(P):.12f}")

    print("(2) Hyp_Reduction: I_d = I_ME + 2/(d(d-1)) <v, delta(Q)> on random strategies:")
    for d in (2, 3, 4, 5, 6):
        worst = 0
        for t in range(4):
            D = int(rng.integers(1, 4))
            pv = [cr.rand_pvm(d, D) for _ in range(4)]       # A1, A2, B1, B2
            w = np.exp(2j * np.pi / d)
            U = [sum(w ** a * p[a] for a in range(d)) for p in pv]
            R = [U[1], U[3].T, U[0], U[2].T]
            I = cglmp_lean(prob([pv[0], pv[1]], [pv[2], pv[3]], D))
            V, cov, zerr = cr.twirl_reduce(R, d)
            Q = qconfig_from_V(V, d)
            ax = max(abs(Q[x] @ Q[x] - Q[x]).max() for x in range(4 * d))
            ax = max(ax, max(abs(sum(Q[r + j * d] for j in range(4)) - np.eye(Q[0].shape[0])).max() for r in range(d)))
            dl, Nm = delta_of_Q(Q, d)
            pred = IME(d) + 2 / (d * (d - 1)) * vvec(d) @ dl
            worst = max(worst, abs(I - pred), ax, abs(Nm(d) - d),
                        max(abs(Nm(2 * d - m) - Nm(m)) for m in range(1, d)))
        print(f"  d={d}: max of |I_d - (I_ME + 2<v,delta>/(d(d-1)))|, config axioms, |N(d)-d|, |N(2d-m)-N(m)|: {worst:.1e}")

    print("(3) CONE certificates with the kernel-form cell directions: max |sum_k lam_k u^{ell_k} - v|:")
    for d in (2, 3, 4, 5, 7, 10):
        c = json.load(open(CERTS + "\\cert_d" + str(d) + ".json"))
        q = c['q']
        tot = [mpm.mpf(0)] * (d - 1)
        for n, lam in zip(c['cells'], c['lam']):
            u = u_kernel([mpm.mpf(x) / q for x in n], d)
            tot = [t + lam * ui for t, ui in zip(tot, u)]
        v = [2 / mpm.sin(mpm.pi * m / (2 * d)) for m in range(1, d)]
        print(f"  d={d}: K={len(c['cells'])}, all n_r >= 1: {all(min(n) >= 1 for n in c['cells'])}, "
              f"max residual {float(max(abs(t - vv) for t, vv in zip(tot, v))):.2e}")

    print("(4) cell inequalities <u^ell, delta> <= 0 (random ell, random configurations); window delta:")
    for d in (3, 4, 5):
        worst = -1e9
        for t in range(6):
            M = int(rng.integers(1, 4))
            Q = qconfig_from_V([cr.rand_order4(M) for _ in range(d)], d)
            dl, _ = delta_of_Q(Q, d)
            ell = rng.dirichlet(np.ones(d)) * d
            u = np.array([float(x) for x in u_kernel([mpm.mpf(e) for e in ell], d)])
            worst = max(worst, u @ dl)
        dl, _ = delta_of_Q(qconfig_from_V([np.eye(1)] * d, d), d)
        print(f"  d={d}: max <u,delta> = {worst:.4f}; window max|delta| = {np.abs(dl).max():.1e}")

    print("(5) QD2-R2: two-residue cells (ell_0 = a, ell_s = d - a) give c (e_s + e_{d-s}), c > 0:")
    for d in (4, 5, 7):
        ok = True
        for s in range(1, d):
            for a in (mpm.mpf(1), mpm.mpf(d) / 3):
                ell = [mpm.mpf(0)] * d
                ell[0], ell[s] = a, d - a
                u = [float(x) for x in u_kernel(ell, d)]
                supp = {s, d - s}
                c = u[s - 1]
                ok = ok and c > 0 and all(abs(u[m - 1] - (c if m in supp else 0.0)) < 1e-12 for m in range(1, d))
        print(f"  d={d}: all s, two cell sizes: {ok}")

    print("(6) strip function: Poisson integral vs -(1/pi^2) Im Li2(e^{pi(y-lam)} e^{-i pi x}); kernel mass:")
    Ks = lambda x, u: mpm.sin(mpm.pi * x) / (2 * (mpm.cosh(mpm.pi * u) - mpm.cos(mpm.pi * x)))
    for (lam, x, y) in [(0.0, 0.3, 0.2), (0.4, 0.7, -1.1), (-0.5, 0.05, 1.3), (0.2, 0.95, 2.0), (0.1, 0.5, 0.1)]:
        pts = sorted({lam, max(lam, y)}) + [max(lam, y) + 5, mpm.inf]
        hp = mpm.quad(lambda s: Ks(x, y - s) * (s - lam), pts)
        hl = -mpm.im(mpm.polylog(2, mpm.exp(mpm.pi * (y - lam)) * mpm.exp(-1j * mpm.pi * x))) / mpm.pi ** 2
        print(f"  lam={lam}, x={x}, y={y}: Poisson {float(hp):.15f}, Li2 {float(hl):.15f}, diff {float(abs(hp - hl)):.1e}")
    for x in (0.2, 0.6):
        print(f"  mass of K_x, x={x}: {float(mpm.quad(lambda u: Ks(x, u), [-mpm.inf, 0, mpm.inf])):.15f} (1-x = {1 - x})")


if __name__ == "__main__":
    main()
