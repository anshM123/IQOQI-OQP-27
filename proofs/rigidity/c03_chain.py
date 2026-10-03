"""c03: the Q-T1 chain for a cell-embedded step field, term by term (NUMERICAL check of section 3).

Unit circle T, dm = dtheta/2pi, cells J_x = (t_x, t_{x+1}), t_j = 2 pi L_j / N, B(theta) = B_x, A(theta) = A_x on J_x.
g(theta) = (1/pi) sum_j (B_j - B_{j-1}) log|sin((theta - t_j)/2)|      (conjugate function, explicit on each open cell).
Checks, at lam* = log(2)/(2 pi) (alpha = beta = 1/4):
  (1) Q^ell / N^2  ==  int tau(A g) dm                      (closed-form cell kernel vs quadrature)
  (2) int (1/M) sum_{nu in spec(B+ig)} h_lam(nu) dm == h_lam(1/4)   (harmonicity / mean value, operator constraint), several lam
  (3) Phi_c - Q^ell/N^2 == S_star + S_bath   with  S_star = int [(1/M) sum h_lam*(nu) - tau((P(g-lam*)P)_+)] dm >= 0,
                                                    S_bath = int [tau((P(g-lam*)P)_+) - tau(A(g-lam*))] dm >= 0
  (4) pointwise: (*)-defect density >= 0; its size vs ||[B(theta), g(theta)]||.
Configurations: random non-commuting; commuting one-step mixture (F = F_DKZ: all slacks must vanish); near-optimal
non-commuting rotations of a one-step mixture (slacks ~ t^2).
"""
import json, os
import numpy as np
from rcore import *

LAMS = 0.5 * np.log(2) / PI


def quad_rule(panels, nodes):
    xg, wg = np.polynomial.legendre.leggauss(nodes)
    u = np.concatenate([(p + (xg + 1) / 2) / panels for p in range(panels)])
    w = np.concatenate([wg / (2 * panels) for p in range(panels)])
    s = 6 * u ** 5 - 15 * u ** 4 + 10 * u ** 3
    return s, w * 30 * u ** 2 * (1 - u) ** 2


def chain_terms(Q, ell, panels=40, nodes=10, lams=(LAMS,)):
    N = Q.shape[0]
    d = N // 4
    M = Q.shape[-1]
    A, B = AB(Q)
    L = cell_endpoints(ell)
    t = 2 * PI * L / N                      # t_0..t_N (t_N = 2 pi)
    jumps = np.array([B[j] - B[j - 1] for j in range(N)])          # B_j - B_{j-1}, j in Z_N
    s, w = quad_rule(panels, nodes)
    res = {lam: dict(hint=0.0, star=0.0, bath=0.0, Ag=0.0) for lam in lams}
    Ag = 0.0
    maxcomm = 0.0
    mindens = 1e9
    for x in range(N):
        th = t[x] + (t[x + 1] - t[x]) * s
        wt = w * (t[x + 1] - t[x]) / (2 * PI)
        logs = np.log(np.abs(np.sin((th[:, None] - t[None, :N]) / 2)))          # (S, N)
        G = np.einsum('sj,jab->sab', logs, jumps) / PI
        Px = np.eye(M) - B[x]
        ev, U = np.linalg.eigh(Px)
        Ub = U[:, ev > 0.5]                                                  # ONB of ran P
        for i in range(len(th)):
            g = G[i]
            Ag += wt[i] * np.trace(A[x] @ g).real / M
            comm = np.linalg.norm(B[x] @ g - g @ B[x])
            maxcomm = max(maxcomm, comm)
            nu = np.linalg.eigvals(B[x] + 1j * g)
            xr = np.clip(nu.real, 0.0, 1.0)
            comp = np.linalg.eigvalsh(Ub.conj().T @ g @ Ub) if Ub.shape[1] else np.zeros(0)
            for lam in lams:
                hs = hlam(xr, nu.imag, lam).sum()
                pos = np.clip(comp - lam, 0, None).sum()
                bath_pt = pos - np.trace(A[x] @ (g - lam * np.eye(M))).real
                r = res[lam]
                r['hint'] += wt[i] * hs / M
                r['star'] += wt[i] * (hs - pos) / M
                r['bath'] += wt[i] * bath_pt / M
                if lam == LAMS:
                    mindens = min(mindens, (hs - pos) / M)
    return Ag, res, maxcomm, mindens


def report(name, Q, ell):
    N = Q.shape[0]
    d = N // 4
    A, B = AB(Q)
    P = pair_matrix(A, B)
    Qell = float(np.sum(cell_kernel(ell) * P))
    lams = (LAMS, -0.3, 0.0, 0.7)
    Ag, res, maxcomm, mindens = chain_terms(Q, ell, lams=lams)
    Pc = phic(0.25, 0.25)
    r = res[LAMS]
    print(f"[{name}] d={d} M={Q.shape[-1]}  ||[Q,Q]||max={commutator_norm(Q):.3e}")
    print(f"   (1) Q^ell/N^2 = {Qell / N**2:.10f}   quadrature int tau(Ag) = {Ag:.10f}   diff {Qell / N**2 - Ag:.2e}")
    for lam in lams:
        hl = float(hlam(np.array([0.25]), np.array([0.0]), lam)[0])
        print(f"   (2) lam={lam:+.4f}: int (1/M) sum h = {res[lam]['hint']:.10f}  vs h_lam(1/4) = {hl:.10f}  diff {res[lam]['hint'] - hl:.2e}")
    lhs = Pc - Qell / N ** 2
    print(f"   (3) Phi_c - Q^ell/N^2 = {lhs:.10f};  S_star = {r['star']:.10f}, S_bath = {r['bath']:.10f}, sum = "
          f"{r['star'] + r['bath']:.10f}  diff {lhs - r['star'] - r['bath']:.2e}")
    print(f"   (4) min pointwise (*)-defect density = {mindens:.3e};  max_theta ||[B(theta), g(theta)]|| = {maxcomm:.3e}")
    return lhs, r['star'], r['bath']


if __name__ == '__main__':
    rng = np.random.default_rng(7)
    d = 4
    c = json.load(open(os.path.join(os.path.dirname(__file__), '..', '..', 'cone-certificates', 'certs', f'cert_d{d}.json')))
    ell_cert = np.array(c['cells'][0], float) / c['q']
    ell_rand = d * rng.dirichlet(np.ones(d))
    print("cell vectors:", np.round(ell_cert, 4), np.round(ell_rand, 4))
    # (a) random non-commuting
    V = random_family(d, 2, rng)
    report('random M=2, cert cell', Q_from_family(V), ell_cert)
    V3 = random_family(d, 3, rng)
    report('random M=3, random cell', Q_from_family(V3), ell_rand)
    # (b) commuting one-step mixture: V_k = diag(1, i^{-[k >= r]})  (direct sum of two one-step configurations)
    r0 = 2
    V0 = np.array([np.diag([1.0, (1j) ** (-(1 if k >= r0 else 0))]) for k in range(d)])
    print("F(V0) - F_DKZ =", F_clock(V0) - F_DKZ(d))
    report('commuting one-step mixture', Q_from_family(V0), ell_cert)
    # (c) near-optimal non-commuting rotations of V0
    H = []
    for k in range(d):
        X = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
        H.append((X + X.conj().T) / 2)
    from scipy.linalg import expm
    for tt in (0.2, 0.1, 0.05):
        Vt = np.array([expm(1j * tt * H[k]) @ V0[k] @ expm(-1j * tt * H[k]) for k in range(d)])
        dF = F_DKZ(d) - F_clock(Vt)
        lhs, st, ba = report(f'rotated mixture t={tt}', Q_from_family(Vt), ell_cert)
        print(f"   F_DKZ - F = {dF:.4e};  (Phi_c - Q^ell/N^2)/t^2 = {lhs / tt**2:.4f}, S_star/t^2 = {st / tt**2:.4f}")
