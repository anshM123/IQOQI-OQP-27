"""Referee check, item 3: cell-embedding inequalities QD2-L1, rotation identity (1.4), window-sum form QD2-L2.  Independent code.

For random NON-commuting 27B configurations (V_k = U_k diag(i^{a}) U_k^*, Haar U_k, M = 2..5) and random cells ell
(Dirichlet, sparse with zero cells, rational):
  (a) every rotated cell value Q^ell(rot_c Q) <= N^2 Phi_c(1/4,1/4)   (all c in Z_N, not only c < d)
  (b) (1/d) sum_{c<d} [Q^ell(rot_c Q) - N^2 Phi_c] = <u^ell, delta>   with u^ell from the DEFINITION Kt(m) + Kt(2d-m)
  (c) definition = window-sum form Delta^2 (1/d) sum_r Ghat(S_r(m))
  (d) windows and commuting one-step mixtures: Q^ell = N^2 Phi_c exactly (every rotation)
  (e) two-residue cells: u^ell is a POSITIVE multiple of e_s + e_{d-s}
  (f) adversarial: maximise <u^ell, delta> over configurations (M = 2,3) by BFGS; maximum should be 0 (windows)
Kernel in mpmath (30 digits).
"""
import numpy as np, mpmath as mp
from scipy.optimize import minimize
mp.mp.dps = 30
rng = np.random.default_rng(31337)
GCAT = mp.catalan


def haar(n):
    z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def Qconf_from_V(V, d):
    N = 4 * d; M = V[0].shape[0]
    Q = [None] * N
    for k in range(d):
        Ek = V[k].conj().T
        for a in range(4):
            P = np.eye(M, dtype=complex)
            for b in range(4):
                if b != a:
                    P = P @ (Ek - 1j ** b * np.eye(M)) / (1j ** a - 1j ** b)
            Q[(k - d * a) % N] = P
    return Q


def rand_V(d, M):
    V = []
    for k in range(d):
        U = haar(M)
        V.append(U @ np.diag(1j ** (-rng.integers(0, 4, M))) @ U.conj().T)
    return V


def pairmat(Q, d):
    """Tab[x,y] = tau(A_x B_y) = tau(Q_x Q_{y+d})"""
    N = 4 * d; M = Q[0].shape[0]
    Tab = np.zeros((N, N))
    for x in range(N):
        for y in range(N):
            Tab[x, y] = np.trace(Q[x] @ Q[(y + d) % N]).real / M
    return Tab


def Nvec(Tab, d):
    N = 4 * d
    T = np.array([sum(Tab[(y + m) % N, y] for y in range(N)) for m in range(N)])
    return np.array([T[m] - T[(-m) % N] for m in range(N)])


class Kernel:
    def __init__(self, ell, d):
        self.d = d; N = self.N = 4 * d
        ell = [mp.mpf(e) for e in ell]
        L = [mp.mpf(0)]
        for x in range(N):
            L.append(L[-1] + ell[x % d])
        self.L = L
        self.ell = ell
        pref = -(mp.mpf(N) ** 2) / (2 * mp.pi ** 2)
        self.G = lambda u: pref * mp.clsin(2, 2 * mp.pi * u / N)
        cache = {}
        Gc = lambda u: cache.setdefault(u, self.G(u))
        K = np.zeros((N, N))
        for x in range(N):
            for y in range(N):
                K[x, y] = float(Gc(L[x + 1] - L[y]) - Gc(L[x] - L[y]) - Gc(L[x + 1] - L[y + 1]) + Gc(L[x] - L[y + 1]))
        self.K = K

    def Q(self, Tab, c=0):
        N = self.N
        idx = (np.arange(N) + c) % N
        # Q^ell(rot_c Q) = sum_{x,y} K(x+c,y+c) tau(A_x B_y)
        return float(np.sum(self.K[np.ix_(idx, idx)] * Tab))

    def u_def(self):
        d, N = self.d, self.N
        Kt = [sum(self.K[(r + m) % N, r] for r in range(d)) / d for m in range(N)]
        return np.array([Kt[m] + Kt[2 * d - m] for m in range(1, d)])

    def u_win(self):
        d = self.d
        Gh = lambda u: self.G(u) + self.G(2 * d - u)
        ell2 = self.ell + self.ell
        P = []
        for m in range(d + 1):
            s = mp.mpf(0)
            for r in range(d):
                s += Gh(mp.fsum(ell2[r:r + m]))
            P.append(s / d)
        return np.array([float(P[m + 1] - 2 * P[m] + P[m - 1]) for m in range(1, d)])


def rand_cells(d, kind):
    if kind == 'dir':
        return list(rng.dirichlet(np.ones(d) * rng.uniform(0.3, 3)) * d)
    if kind == 'sparse':          # some zero cells
        e = rng.dirichlet(np.ones(d)) * d
        z = rng.choice(d, size=max(1, d // 3), replace=False)
        e[z] = 0
        return list(e / e.sum() * d)
    if kind == 'rat':
        n = rng.integers(1, 40, size=d).astype(float)
        return [mp.mpf(int(x)) * d / int(n.sum()) for x in n]


report = dict(a_max=-1e9, b_err=0, c_err=0, d_err=0, e_ok=True)
for d in range(3, 9):
    N = 4 * d
    target = float(mp.mpf(N) ** 2 * GCAT / mp.pi ** 2)
    v = np.array([2 / np.sin(np.pi * m / (2 * d)) for m in range(1, d)])
    for kind in ['dir', 'sparse', 'rat']:
        ell = rand_cells(d, kind)
        Ker = Kernel(ell, d)
        uD, uW = Ker.u_def(), Ker.u_win()
        report['c_err'] = max(report['c_err'], np.abs(uD - uW).max() / np.abs(uW).max())
        for M in [2, 3, 5]:
            V = rand_V(d, M)
            Tab = pairmat(Qconf_from_V(V, d), d)
            Nm = Nvec(Tab, d)
            delta = np.array([Nm[m] - m for m in range(1, d)])
            vals = [Ker.Q(Tab, c) - target for c in range(N)]
            report['a_max'] = max(report['a_max'], max(vals))
            avg = np.mean(vals[:d])
            report['b_err'] = max(report['b_err'], abs(avg - uD @ delta) / max(1, abs(avg)))
        # windows and commuting one-step mixtures
        for M in [1, 3]:
            V = []
            r0 = rng.integers(0, d, M); c0 = rng.integers(0, 4, M)
            for k in range(d):
                V.append(np.diag([1j ** (-(c0[i] + (k >= r0[i]))) for i in range(M)]))
            Tab = pairmat(Qconf_from_V(V, d), d)
            report['d_err'] = max(report['d_err'], max(abs(Ker.Q(Tab, c) - target) / target for c in range(N)))
    # two-residue cells
    for s in range(1, d):
        a = rng.uniform(0.2, 0.8) * d
        ell = [0.0] * d; ell[0] = a; ell[s] = d - a
        u = Kernel(ell, d).u_win()
        t = np.zeros(d - 1); t[s - 1] += 1; t[d - s - 1] += 1
        c = u @ t / (t @ t)
        if not (c > 0 and np.abs(u - c * t).max() < 1e-9 * abs(c)):
            report['e_ok'] = False
            print(f"   two-residue cell d={d} s={s}: u = {u}, c = {c}")
    print(f"d={d}: running {report}", flush=True)

print("FINAL:", report)

# (f) adversarial ascent of <u^ell, delta> for fixed random cells
print("adversarial ascent of <u^ell, delta> (BFGS over unitaries, eigen-labels fixed):")


def unit_from(p, n):
    Hm = np.zeros((n, n), complex)
    iu = np.triu_indices(n, 1); k = len(iu[0])
    Hm[iu] = p[:k] + 1j * p[k:2 * k]
    Hm = Hm + Hm.conj().T + np.diag(p[2 * k:2 * k + n])
    w_, U = np.linalg.eigh(Hm)
    return U @ np.diag(np.exp(1j * w_)) @ U.conj().T


for (d, M) in [(4, 2), (5, 3), (6, 2), (6, 3)]:
    ell = rand_cells(d, 'dir')
    u = Kernel(ell, d).u_win()
    best = -1e9
    for rep in range(4):
        labs = [rng.integers(0, 4, M) for _ in range(d)]

        def f(p):
            V = [unit_from(p[k * M * M:(k + 1) * M * M], M) @ np.diag(1j ** (-labs[k])) @ unit_from(p[k * M * M:(k + 1) * M * M], M).conj().T
                 for k in range(d)]
            Tab = pairmat(Qconf_from_V(V, d), d)
            Nm = Nvec(Tab, d)
            return -(u @ np.array([Nm[m] - m for m in range(1, d)]))
        r = minimize(f, rng.standard_normal(d * M * M), method='BFGS', options=dict(maxiter=300))
        best = max(best, -r.fun)
    print(f"  d={d} M={M}: max <u,delta> found = {best:.3e}")
