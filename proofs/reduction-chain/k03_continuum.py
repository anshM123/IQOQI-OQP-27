"""Referee check, item 2: the continuum theorem Q-T1 for cell-embedded STEP fields (independent code).

Random non-commuting 27B configurations (d = 3, 4; M = 2, 3) and random cells (all positive; one run with zero cells):
  (1) closed-form Herglotz function H(z) = (1/4) 1 + (i/pi) sum_j (B_j - B_{j-1}) Log(1 - z e^{-i t_j}) vs the Herglotz integral
      (cellwise Gauss-Legendre) at interior points;
  (2) h_lam via Li2 vs h_lam via the strip Poisson integral (two independent formulas);
  (3) mean value: mean over |z| = r of u_lam(z) = sum h_lam(spec H(z)) equals M h_lam(1/4) for r = 0.3, 0.7, 0.95 (harmonicity);
  (4) boundary: int u*_lam dm = M h_lam(1/4) with u* built from B(theta) + i g(theta) (log-singular step field), tanh-sinh per cell;
  (5) Q^ell / N^2 (kernel formula) = int tau(A g) dm (quadrature);
  (6) the chain  int tau(A(g-lam)) <= int tau((P(g-lam)P)_+) <= h_lam(1/4)  and the Legendre step  min_lam [lam/4 + h_lam(1/4)] = G/pi^2
      at lam* = log(2)/(2 pi).
"""
import numpy as np, mpmath as mp
mp.mp.dps = 20
rng = np.random.default_rng(4242)
PI = np.pi


def haar(n):
    z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def Qconf(d, M):
    N = 4 * d
    Q = [None] * N
    for k in range(d):
        U = haar(M)
        lab = rng.integers(0, 4, M)
        Ek = U @ np.diag(1j ** lab) @ U.conj().T          # E_k = V_k^*, eigenvalue i^a <-> Q_{k - d a}
        for a in range(4):
            Q[(k - d * a) % N] = U[:, lab == a] @ U[:, lab == a].conj().T
    return Q


def h_li2(lam, w):
    x, y = w.real, w.imag
    if x <= 1e-13:
        return max(y - lam, 0.0)
    if x >= 1 - 1e-13:
        return 0.0
    z = mp.exp(mp.pi * (y - lam)) * mp.exp(-1j * mp.pi * x)
    return float(-mp.im(mp.polylog(2, z)) / mp.pi ** 2)


def h_poisson(lam, w):
    x, y = w.real, w.imag
    K = lambda t: mp.sin(mp.pi * x) / (2 * (mp.cosh(mp.pi * t) - mp.cos(mp.pi * x)))
    return float(mp.quad(lambda s: (s - lam) * K(y - s), [lam, y, mp.inf]))


def Hfun(z, Bs, t):
    """closed form, |z| < 1 (or boundary point off the t_j)."""
    M = Bs[0].shape[0]
    N = len(Bs)
    H = 0.25 * np.eye(M, dtype=complex)
    for j in range(N):
        H = H + (1j / PI) * (Bs[j] - Bs[j - 1]) * np.log(1 - z * np.exp(-1j * t[j]))
    return H


def tanh_sinh(a, b, h=1 / 24, umax=3.2):
    ks = np.arange(-int(umax / h), int(umax / h) + 1)
    u = ks * h
    s = PI / 2 * np.sinh(u)
    left = (b - a) / (1 + np.exp(-2 * s))      # theta - a
    right = (b - a) / (1 + np.exp(2 * s))      # b - theta
    wts = (b - a) / 2 * (PI / 2) * h * np.cosh(u) / np.cosh(s) ** 2
    keep = (left > 1e-13 * (b - a)) & (right > 1e-13 * (b - a))
    return left[keep], right[keep], wts[keep]


def g_at(x, dl, dr, Bs, t):
    """conjugate function on cell x at theta = t_x + dl = t_{x+1} - dr."""
    N = len(Bs); M = Bs[0].shape[0]
    theta = t[x] + dl
    g = np.zeros((M, M), complex)
    for j in range(N):
        if j == x:
            s = np.sin(dl / 2)
        elif j == (x + 1) % N:
            s = np.sin(-dr / 2)
        else:
            s = np.sin((theta - t[j]) / 2)
        g = g + (1 / PI) * (Bs[j] - Bs[j - 1]) * np.log(abs(s))
    return (g + g.conj().T) / 2


def run(d, M, ell, lams):
    N = 4 * d
    Q = Qconf(d, M)
    A = Q
    Bs = [Q[(x + d) % N] for x in range(N)]
    L = np.concatenate([[0.0], np.cumsum([ell[x % d] for x in range(N)])])
    t = 2 * PI * L[:N] / N
    tt = 2 * PI * L / N
    # (1) Herglotz closed form vs integral at interior points
    xg, wg = np.polynomial.legendre.leggauss(200)
    err1 = 0
    for z in [0.3 * np.exp(1.1j), 0.8 * np.exp(-2.0j), 0.95 * np.exp(0.4j)]:
        Hint = np.zeros((M, M), complex)
        for x in range(N):
            a, b = tt[x], tt[x + 1]
            if b - a <= 0:
                continue
            ph = (a + b) / 2 + (b - a) / 2 * xg
            ker = (np.exp(1j * ph) + z) / (np.exp(1j * ph) - z)
            Hint = Hint + Bs[x] * np.sum(wg * ker) * (b - a) / 2 / (2 * PI)
        err1 = max(err1, np.abs(Hint - Hfun(z, Bs, t)).max())
    # (5) and (4), (6) on the boundary
    QAg = 0.0
    tails = {lam: [0.0, 0.0, 0.0] for lam in lams}     # int tau(A(g-lam)), int tau((P(g-lam)P)_+), int u*/M
    for x in range(N):
        a, b = tt[x], tt[x + 1]
        if b - a <= 0:
            continue
        dls, drs, ws = tanh_sinh(a, b)
        for dl, dr, w in zip(dls, drs, ws):
            g = g_at(x, dl, dr, Bs, t)
            P = np.eye(M) - Bs[x]
            QAg += w / (2 * PI) * np.trace(A[x] @ g).real / M
            ev = np.linalg.eigvals(Bs[x] + 1j * g)
            for lam in lams:
                X = P @ (g - lam * np.eye(M)) @ P
                Xe = np.linalg.eigvalsh((X + X.conj().T) / 2)
                tails[lam][0] += w / (2 * PI) * np.trace(A[x] @ (g - lam * np.eye(M))).real / M
                tails[lam][1] += w / (2 * PI) * np.sum(np.maximum(Xe, 0)) / M
                tails[lam][2] += w / (2 * PI) * sum(h_li2(lam, e) for e in ev) / M
    # kernel value
    pref = -(mp.mpf(N) ** 2) / (2 * mp.pi ** 2)
    G = lambda u: pref * mp.clsin(2, 2 * mp.pi * mp.mpf(u) / N)
    Qell = 0.0
    for x in range(N):
        for y in range(N):
            if x == y:
                continue
            K = float(G(L[x + 1] - L[y]) - G(L[x] - L[y]) - G(L[x + 1] - L[y + 1]) + G(L[x] - L[y + 1]))
            Qell += K * np.trace(A[x] @ Bs[y]).real / M
    # (3) mean value on circles
    mv = {}
    for r in [0.3, 0.7, 0.95]:
        th = 2 * PI * np.arange(512) / 512
        for lam in lams[:2]:
            vals = []
            for tht in th:
                ev = np.linalg.eigvals(Hfun(r * np.exp(1j * tht), Bs, t))
                vals.append(sum(h_li2(lam, e) for e in ev))
            mv[(r, lam)] = np.mean(vals) / M - h_li2(lam, 0.25 + 0j)
    return err1, QAg, Qell / N ** 2, tails, mv


lamstar = np.log(2) / (2 * PI)
# (2) two formulas for h
err2 = 0
for w in [0.3 + 0.2j, 0.05 + 1.3j, 0.9 - 0.4j, 0.5 + 3.0j, 0.01 - 2.0j]:
    for lam in [-0.3, lamstar, 0.8]:
        err2 = max(err2, abs(h_li2(lam, w) - h_poisson(lam, w)))
print(f"(2) h_lam: Li2 formula vs strip Poisson integral: max diff {err2:.2e}")
# (6b) Legendre
f = lambda lam: lam / 4 + h_li2(lam, 0.25 + 0j)
Gpi = float(mp.catalan / mp.pi ** 2)
print(f"(6b) lam* = {lamstar:.12f}: f(lam*) - G/pi^2 = {f(lamstar) - Gpi:.2e};  f(lam*+-0.05) - f(lam*) = "
      f"{f(lamstar + 0.05) - f(lamstar):.3e}, {f(lamstar - 0.05) - f(lamstar):.3e};  f'(lam*) ~ {(f(lamstar + 1e-5) - f(lamstar - 1e-5)) / 2e-5:.2e}")
lams = [lamstar, -0.4, 0.0, 0.6]
for (d, M, kind) in [(3, 2, 'pos'), (4, 3, 'pos'), (4, 2, 'zero')]:
    ell = rng.dirichlet(np.ones(d)) * d
    if kind == 'zero':
        ell[1] = 0.0
        ell = ell / ell.sum() * d
    err1, QAg, Qn, tails, mv = run(d, M, ell, lams)
    print(f"d={d} M={M} cells={np.round(ell, 3)}:")
    print(f"   (1) Herglotz closed form vs integral: {err1:.2e}")
    print(f"   (5) int tau(A g) dm = {QAg:.10f}, Q^ell/N^2 = {Qn:.10f}, diff {QAg - Qn:.2e}  (Phi_c = {Gpi:.10f})")
    for lam in lams:
        a, b, c = tails[lam]
        print(f"   (4,6) lam={lam:+.4f}: int tau(A(g-lam)) = {a:.8f} <= int tau((P(g-lam)P)_+) = {b:.8f} <= "
              f"int u*/M = {c:.8f} vs h_lam(1/4) = {h_li2(lam, 0.25 + 0j):.8f} (diff {c - h_li2(lam, 0.25 + 0j):.1e})")
    print("   (3) mean value on circles (mean u/M - h(1/4)):", {k: f"{v:.1e}" for k, v in mv.items()})
