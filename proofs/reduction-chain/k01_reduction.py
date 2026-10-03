"""Referee check, item 1: strategy -> clock model -> Q-configuration -> linear form.  Independent re-implementation.

For random projective strategies on Phi_D (D = 2..6) and d = 3..8:
  I_direct : the CGLMP expression of Collins et al. (PRL 88, 040404), computed from P(a,b|x,y) = <Phi_D|P^x_a (x) Q^y_b|Phi_D>
  I_chain  : twirl over rho (Z_{4d}), Stone-von Neumann basis, reduced family V_k (V_k^4 = 1), F(V), I = 4F/(d(d-1))
  I_Q      : Q-configuration (spectral projections of E_k = V_k^*), N(m), F = sum_{m<d} csc(pi m/2d) N(m)
plus: Lemma 2.1 (I = 4 - 2S/(d-1)), F = <A,B>/2 - d/2, N(d) = d, N(2d-m) = N(m), N(s) + N(d-s) <= d, DKZ = I_ME(d),
DKZ (x) 1_K, and a small ascent of I_d over strategies (sanity: never above I_ME).
"""
import numpy as np, sys
from scipy.optimize import minimize

rng = np.random.default_rng(20261002)


def haar(n):
    z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def rand_pvm(D, d):
    U = haar(D)
    lab = rng.integers(0, d, size=D)
    return [U[:, lab == a] @ U[:, lab == a].conj().T for a in range(d)]


def probs(PA, PB, D, d):
    p = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    p[x, y, a, b] = np.trace(PA[x][a] @ PB[y][b].T).real / D
    return p


def cglmp(p, d):
    # P(A_x = B_y + k) = sum_j p[x,y,j+k,j];  P(B_y = A_x + k) = sum_j p[x,y,j,j+k]   (x,y = 0 <-> setting 1)
    PAB = lambda x, y, k: sum(p[x, y, (j + k) % d, j] for j in range(d))
    PBA = lambda x, y, k: sum(p[x, y, j, (j + k) % d] for j in range(d))
    I = 0.0
    for k in range(d // 2):
        c = 1 - 2 * k / (d - 1)
        plus = PAB(0, 0, k) + PBA(1, 0, k + 1) + PAB(1, 1, k) + PBA(0, 1, k)
        minus = PAB(0, 0, -k - 1) + PBA(1, 0, -k) + PAB(1, 1, -k - 1) + PBA(0, 1, -k - 1)
        I += c * (plus - minus)
    return I


def S_chain(p, d):
    # S = E m(A2-B2) + E m(B2-A1) + E m(A1-B1) + E m(B1-A2-1)   (paper eq. (S), X1=A2, Y1=B2, X2=A1, Y2=B1)
    S = 0.0
    for a in range(d):
        for b in range(d):
            S += p[1, 1, a, b] * ((a - b) % d) + p[0, 1, a, b] * ((b - a) % d) \
                 + p[0, 0, a, b] * ((a - b) % d) + p[1, 0, a, b] * ((b - a - 1) % d)
    return S


def I_ME(d):
    return 4 / (d * (d - 1)) * sum((d - j) / np.cos(np.pi * j / (2 * d)) for j in range(1, d))


def reduce_to_clock(PA, PB, D, d):
    """returns V (list of d unitaries of size M = 4D) and check residuals."""
    w = np.exp(2j * np.pi / d); z = np.exp(2j * np.pi / (4 * d))
    U = [sum(w ** a * PA[x][a] for a in range(d)) for x in range(2)]
    Up = [sum(w ** b * PB[y][b] for b in range(d)) for y in range(2)]
    R = [U[1], Up[1].T, U[0], Up[0].T]
    # twirl
    quads = [R]
    for r in range(1, 4 * d):
        q = quads[-1]
        quads.append([q[1], q[2], q[3], w * q[0]])
    n = 4 * d * D
    Rt = []
    for i in range(4):
        Mx = np.zeros((n, n), complex)
        for r in range(4 * d):
            Mx[r * D:(r + 1) * D, r * D:(r + 1) * D] = quads[r][i]
        Rt.append(Mx)
    Wsh = np.zeros((n, n), complex)                    # W(e_{r+1} (x) v) = e_r (x) v
    for r in range(4 * d):
        rp = (r + 1) % (4 * d)
        Wsh[r * D:(r + 1) * D, rp * D:(rp + 1) * D] = np.eye(D)
    res_cov = max(np.abs(Wsh @ Rt[i] @ Wsh.conj().T - (Rt[i + 1] if i < 3 else w * Rt[0])).max() for i in range(4))
    # H_0 = ker(Z - 1), Z = W^4: vectors 4-periodic in r
    M = 4 * D
    f = np.zeros((n, M), complex)
    for s in range(4):
        for j in range(D):
            for r in range(s, 4 * d, 4):
                f[r * D + j, s * D + j] = 1 / np.sqrt(d)
    E = [f]
    for k in range(1, d):
        E.append(Rt[0] @ E[-1])
    T = np.hstack(E)                                    # columns e_{k,mu}, k-major
    res_T = np.abs(T.conj().T @ T - np.eye(n)).max()
    X = np.roll(np.eye(d), 1, axis=0)                  # X|k> = |k+1>
    res_X = np.abs(T.conj().T @ Rt[0] @ T - np.kron(X, np.eye(M))).max()
    Wb = T.conj().T @ Wsh @ T
    offd = Wb.copy()
    V = []
    for k in range(d):
        Wk = Wb[k * M:(k + 1) * M, k * M:(k + 1) * M]
        offd[k * M:(k + 1) * M, k * M:(k + 1) * M] = 0
        V.append(z ** (-k) * Wk)
    res_blk = np.abs(offd).max()
    res_V4 = max(np.abs(np.linalg.matrix_power(Vk, 4) - np.eye(M)).max() for Vk in V)
    res_unit = max(np.abs(Vk @ Vk.conj().T - np.eye(M)).max() for Vk in V)
    return V, max(res_cov, res_T, res_X, res_blk, res_V4, res_unit)


def F_of_V(V, d):
    M = V[0].shape[0]
    F = 0.0
    for j in range(d):
        for k in range(j + 1, d):
            m = k - j
            h = 1 / np.cos(np.pi * m / (2 * d)) - 1j / np.sin(np.pi * m / (2 * d))
            F += (h * np.trace(V[j] @ V[k].conj().T) / M).real
    return F


def Qconfig(V, d):
    """Q_x (x in Z_4d), x = k - d a, spectral projection of E_k = V_k^* for eigenvalue i^a."""
    N = 4 * d; M = V[0].shape[0]
    Q = [None] * N
    for k in range(d):
        Ek = V[k].conj().T
        for a in range(4):
            lam = 1j ** a
            P = np.eye(M, dtype=complex)
            for b in range(4):
                if b != a:
                    P = P @ (Ek - 1j ** b * np.eye(M)) / (lam - 1j ** b)
            Q[(k - d * a) % N] = P
    return Q


def linear_form(Q, d):
    N = 4 * d; M = Q[0].shape[0]
    A = Q; B = [Q[(x + d) % N] for x in range(N)]
    tau = lambda X: np.trace(X).real / M
    T = np.array([sum(tau(A[(y + m) % N] @ B[y]) for y in range(N)) for m in range(N)])
    Nm = np.array([T[m] - T[(-m) % N] for m in range(N)])
    kap = lambda u: 0.0 if u % N == 0 else 1 / np.tan(np.pi * u / N)
    AB = sum(kap(x - y) * tau(A[x] @ B[y]) for x in range(N) for y in range(N))
    return Nm, AB


worst = dict(I_chain=0, I_Q=0, lemma21=0, F_AB=0, Nd=0, Nsym=0, red=0, Nsum_viol=-1e9)
count = 0
maxratio = -1e9
for d in range(3, 9):
    FD = sum((d - m) / np.cos(np.pi * m / (2 * d)) for m in range(1, d))
    for D in range(2, 7):
        ntr = 3 if d <= 6 else 2
        for t in range(ntr):
            PA = [rand_pvm(D, d) for _ in range(2)]
            PB = [rand_pvm(D, d) for _ in range(2)]
            p = probs(PA, PB, D, d)
            I1 = cglmp(p, d)
            S = S_chain(p, d)
            V, rr = reduce_to_clock(PA, PB, D, d)
            F = F_of_V(V, d)
            I2 = 4 * F / (d * (d - 1))
            Q = Qconfig(V, d)
            Nm, AB = linear_form(Q, d)
            FQ = sum(Nm[m] / np.sin(np.pi * m / (2 * d)) for m in range(1, d))
            I3 = 4 * FQ / (d * (d - 1))
            worst['I_chain'] = max(worst['I_chain'], abs(I1 - I2))
            worst['I_Q'] = max(worst['I_Q'], abs(I1 - I3))
            worst['lemma21'] = max(worst['lemma21'], abs(I1 - (4 - 2 * S / (d - 1))))
            worst['F_AB'] = max(worst['F_AB'], abs(F - (AB / 2 - d / 2)))
            worst['Nd'] = max(worst['Nd'], abs(Nm[d] - d))
            worst['Nsym'] = max(worst['Nsym'], max(abs(Nm[2 * d - m] - Nm[m]) for m in range(1, d)))
            worst['red'] = max(worst['red'], rr)
            worst['Nsum_viol'] = max(worst['Nsum_viol'], max(Nm[s] + Nm[d - s] - d for s in range(1, d)))
            maxratio = max(maxratio, I1 - I_ME(d))
            count += 1
    print(f"d={d}: done (I_ME = {I_ME(d):.10f}, F_DKZ = {FD:.10f})", flush=True)
print(f"{count} random strategies (d = 3..8, D = 2..6)")
for k, v in worst.items():
    print(f"  max {k:10s} = {v:.3e}")
print(f"  max (I_direct - I_ME) over random strategies = {maxratio:.4f}  (must be < 0)")

# DKZ (CGLMP eqs. (12)-(15)) and DKZ (x) 1_K
print("DKZ checks:")
for d in range(2, 9):
    alpha = [0.0, 0.5]; beta = [0.25, -0.25]
    js = np.arange(d)
    PA = [[None] * d for _ in range(2)]; PB = [[None] * d for _ in range(2)]
    for x in range(2):
        for a in range(d):
            v = np.exp(-2j * np.pi * js * (a + alpha[x]) / d) / np.sqrt(d)
            PA[x][a] = np.outer(v, v.conj())
    for y in range(2):
        for b in range(d):
            v = np.exp(2j * np.pi * js * (b - beta[y]) / d) / np.sqrt(d)
            PB[y][b] = np.outer(v, v.conj())
    p = probs(PA, PB, d, d)
    # CGLMP eq. (15)
    dev15 = max(abs(p[x, y, k, l] - 1 / (2 * d ** 3 * np.sin(np.pi * (k - l + alpha[x] + beta[y]) / d) ** 2))
                for x in range(2) for y in range(2) for k in range(d) for l in range(d))
    I1 = cglmp(p, d)
    K = 2
    PA2 = [[np.kron(P, np.eye(K)) for P in PA[x]] for x in range(2)]
    PB2 = [[np.kron(P, np.eye(K)) for P in PB[y]] for y in range(2)]
    I2 = cglmp(probs(PA2, PB2, d * K, d), d)
    V, rr = reduce_to_clock(PA, PB, d, d)
    Q = Qconfig(V, d)
    Nm, AB = linear_form(Q, d)
    print(f"  d={d}: I(DKZ) - I_ME = {I1 - I_ME(d):.2e}; I(DKZ(x)1_2) - I_ME = {I2 - I_ME(d):.2e}; eq.(15) dev {dev15:.1e};"
          f" N(m) - m (m<d) = {max(abs(Nm[m] - m) for m in range(1, d)):.1e}")

# small ascent of I_d over strategies (sanity check of conventions; never above I_ME)
print("ascent (BFGS over unitaries, eigen-labels fixed):")


def unit_from(params, n):
    Hm = np.zeros((n, n), complex)
    iu = np.triu_indices(n, 1)
    k = len(iu[0])
    Hm[iu] = params[:k] + 1j * params[k:2 * k]
    Hm = Hm + Hm.conj().T + np.diag(params[2 * k:2 * k + n])
    w_, Uv = np.linalg.eigh(Hm)
    return Uv @ np.diag(np.exp(1j * w_)) @ Uv.conj().T


for (d, D) in [(3, 3), (3, 4), (4, 4), (3, 6), (5, 5)]:
    n = D
    npar = n * n
    best = -1e9
    for rep in range(6):
        labs = [rng.permutation(np.arange(D) % d) for _ in range(4)]

        def neg(params):
            Us = [unit_from(params[i * npar:(i + 1) * npar], n) for i in range(4)]
            PA = [[Us[x][:, labs[x] == a] @ Us[x][:, labs[x] == a].conj().T for a in range(d)] for x in range(2)]
            PB = [[Us[2 + y][:, labs[2 + y] == b] @ Us[2 + y][:, labs[2 + y] == b].conj().T for b in range(d)] for y in range(2)]
            return -cglmp(probs(PA, PB, D, d), d)
        r = minimize(neg, rng.standard_normal(4 * npar), method='BFGS', options=dict(maxiter=400))
        best = max(best, -r.fun)
    print(f"  d={d} D={D}: best I found = {best:.10f}, I_ME = {I_ME(d):.10f}, diff = {best - I_ME(d):.2e}")
