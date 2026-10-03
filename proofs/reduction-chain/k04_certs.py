"""Referee check, item 4: QD2-R1 with the actual LP certificates (QD2/certs, read only), d = 2..8; plus the pair form of N(m)
(RIGIDITY_ALLD (1.2), trivial directions t_s) on random strategies.

(a) u^{ell_k} from the ORIGINAL cell-pair kernel (Kt(m) + Kt(2d-m), G via mpmath.clsin at 50 digits; NOT the window-sum form),
    residual v - sum_k lam~_k u^{ell_k} with the stored float lam~, then the exact minimum-norm correction lam = lam~ + U^T y
    computed at 50 digits: min lam > 0 and |U lam - v| ~ 1e-45  (independent, non-interval re-verification of cone membership);
(b) random strategies (D = 2..5): full chain strategy -> V -> Q -> delta; every certificate direction pairs nonpositively
    (<u^{ell_k}, delta> <= 0), sum_k lam_k <u^{ell_k},delta> = <v,delta> = 2 (F - F_DKZ), and I_d <= I_ME(d);
(c) pair form N(m) = sum_{k-j=m} [pi(1)-pi(3)] + sum_{k-j=d-m} [pi(0)-pi(2)] and N(s)+N(d-s) <= d (t_s directions).
"""
import json, numpy as np, mpmath as mp
from k00_core import rand_pvm, probs, cglmp, I_ME, reduce_to_clock, F_of_V, Qconfig, linear_form, rng
mp.mp.dps = 50
CERT = '../../cone-certificates/certs/cert_d{}.json'


def u_cellpair(n, q, d):
    N = 4 * d
    G = lambda j: -(mp.mpf(N) ** 2 / (2 * mp.pi ** 2)) * mp.clsin(2, 2 * mp.pi * mp.mpf(j) / (q * N))   # G(j/q)
    cache = {}
    Gq = lambda j: cache.setdefault(j, G(j))
    L = [0]
    for x in range(N):
        L.append(L[-1] + n[x % d])
    K = lambda x, y: Gq(L[x + 1] - L[y]) - Gq(L[x] - L[y]) - Gq(L[x + 1] - L[y + 1]) + Gq(L[x] - L[y + 1])
    Kt = [sum(K((r + m) % N, r) for r in range(d)) / d if m % N else mp.mpf(0) for m in range(N)]
    return [Kt[m] + Kt[2 * d - m] for m in range(1, d)]


certs = {}
print("(a) certificates, original cell-pair kernel, 50 digits:")
for d in range(2, 9):
    c = json.load(open(CERT.format(d)))
    q = c['q']
    assert all(sum(n) == q * d and min(n) >= 1 for n in c['cells'])
    U = mp.matrix([u_cellpair(n, q, d) for n in c['cells']]).T          # (d-1) x K
    v = mp.matrix([2 / mp.sin(mp.pi * m / (2 * d)) for m in range(1, d)])
    lam = mp.matrix(c['lam'])
    res = v - U * lam
    y = mp.lu_solve(U * U.T, res)
    lam_ex = lam + U.T * y
    res2 = v - U * lam_ex
    print(f"  d={d}: K={len(c['cells'])}, cells n_r >= 1 and sum n = 16 d: True;  |v - U lam~| = {float(mp.norm(res, mp.inf)):.2e};"
          f"  exact min lam = {float(min(lam_ex)):.6e} (> 0: {min(lam_ex) > 0});  |v - U lam| = {float(mp.norm(res2, mp.inf)):.1e}")
    certs[d] = (np.array([[float(U[i, k]) for k in range(U.cols)] for i in range(U.rows)]), np.array([float(x) for x in lam_ex]))

print("(b,c) random strategies:")
worst = dict(dir_max=-1e9, sum_err=0, F_err=0, I_gap=-1e9, pair_err=0, ts_max=-1e9)
for d in range(3, 9):
    Umat, lam = certs[d]
    v = np.array([2 / np.sin(np.pi * m / (2 * d)) for m in range(1, d)])
    FD = sum((d - m) / np.cos(np.pi * m / (2 * d)) for m in range(1, d))
    for D in range(2, 6):
        for t in range(2):
            PA = [rand_pvm(D, d) for _ in range(2)]; PB = [rand_pvm(D, d) for _ in range(2)]
            I1 = cglmp(probs(PA, PB, D, d), d)
            V, _ = reduce_to_clock(PA, PB, D, d)
            F = F_of_V(V, d)
            Q = Qconfig(V, d)
            Nm, AB = linear_form(Q, d)
            delta = np.array([Nm[m] - m for m in range(1, d)])
            pairs = Umat.T @ delta
            worst['dir_max'] = max(worst['dir_max'], pairs.max())
            worst['sum_err'] = max(worst['sum_err'], abs(lam @ pairs - v @ delta))
            worst['F_err'] = max(worst['F_err'], abs(v @ delta - 2 * (F - FD)))
            worst['I_gap'] = max(worst['I_gap'], I1 - I_ME(d))
            # (c) pair form
            M = Q[0].shape[0]
            Qs = lambda k, a: Q[(k - d * a) % (4 * d)]
            pi_ = lambda j, k, tt: sum(np.trace(Qs(j, b) @ Qs(k, b + tt)).real / M for b in range(4))
            for m in range(1, d):
                pf = sum(pi_(j, j + m, 1) - pi_(j, j + m, 3) for j in range(d - m)) + \
                     sum(pi_(j, j + d - m, 0) - pi_(j, j + d - m, 2) for j in range(m))
                worst['pair_err'] = max(worst['pair_err'], abs(pf - Nm[m]))
            worst['ts_max'] = max(worst['ts_max'], max(Nm[s] + Nm[d - s] - d for s in range(1, d)))
    print(f"  d={d}: {worst}", flush=True)
print("FINAL:", worst)
