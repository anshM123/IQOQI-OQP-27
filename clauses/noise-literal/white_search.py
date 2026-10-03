"""
white_search.py -- ledger B1 search (float exploration): CGLMP witness with white state noise and unbalanced PVMs.

For a PVM strategy on Phi_D with rank pattern r (r_x(a) = rank of Alice's projector P^x_a, s_y(b) for Bob) the white
noise term is the product of the marginals n_r(a,b|x,y) = r_x(a) s_y(b)/D^2, a constant of the pattern, and
    F = v* I(p) + (1 - v*) I(n_r),   v* = 2/I_ME(d);     B1 (refined inequality)  <=>  F <= 2 for all strategies.
Pruning (rigorous upper bound, cheap): the marginals of p are fixed by r, so
    I(p) <= min(I_ME(d), N(r)),   N(r) = sum_xy max{ sum_ab beta_xy(a,b) t(a,b) : t >= 0 with marginals r_x/D, s_y/D }
(four transportation LPs).  Patterns with v* min(I_ME, N(r)) + (1-v*) I(n_r) <= 2 cannot violate B1.
Survivors: maximise I(p) over the bases (Riemannian gradient ascent, several starts) and report F.

usage: python white_search.py d D nsample nstart seed   (all patterns enumerated; nsample > 0 caps the number
       of survivors optimised: the nsample/2 with the largest bound + a random sample of the rest)
"""
import itertools
import sys
import time

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, ".")
from white_qubit_scan import beta_np, i_me  # noqa: E402


def compositions(D, d):
    for c in itertools.product(range(D + 1), repeat=d - 1):
        s = sum(c)
        if s <= D:
            yield tuple(c) + (D - s,)


_ot_cache = {}


def ot_max(beta_xy, ma, mb):
    key = (beta_xy.tobytes(), ma, mb)
    if key in _ot_cache:
        return _ot_cache[key]
    d = len(ma)
    A = []
    b = []
    for a in range(d):
        row = np.zeros((d, d))
        row[a, :] = 1
        A.append(row.ravel())
        b.append(ma[a])
    for c in range(d):
        row = np.zeros((d, d))
        row[:, c] = 1
        A.append(row.ravel())
        b.append(mb[c])
    res = linprog(-beta_xy.ravel(), A_eq=np.array(A), b_eq=np.array(b, float), bounds=(0, None), method="highs")
    val = -res.fun
    _ot_cache[key] = val
    return val


def noise_I(beta, r, D):
    m = [np.array(x, float) / D for x in r]
    return sum(float(m[x] @ beta[x, y] @ m[2 + y]) for x in range(2) for y in range(2))


def ns_bound(beta, r, D):
    m = [tuple(np.array(x, float) / D) for x in r]
    return sum(ot_max(beta[x, y], m[x], m[2 + y]) for x in range(2) for y in range(2))


# ---------------------------------------------------------------- PVM optimisation (labels = rank pattern)
def labels(ranks):
    lab = []
    for a, k in enumerate(ranks):
        lab += [a] * k
    return np.array(lab, int)


def probs(U, labs, d):
    D = U[0].shape[0]
    p = np.zeros((2, 2, d, d))
    M = [[None, None], [None, None]]
    for x in range(2):
        for y in range(2):
            Mxy = U[x].T @ U[2 + y]
            M[x][y] = Mxy
            np.add.at(p[x, y], (labs[x][:, None], labs[2 + y][None, :]), np.abs(Mxy) ** 2 / D)
    return p, M


def grads(U, labs, d, G):
    D = U[0].shape[0]
    _, M = probs(U, labs, d)
    Gx = [[G[x, y][np.ix_(labs[x], labs[2 + y])] for y in range(2)] for x in range(2)]
    gA2 = np.zeros((D, D), complex)
    for y in range(2):
        gA2 += np.conj(U[2 + y]) @ (Gx[1][y] * M[1][y]).T / D
    gB = []
    for y in range(2):
        g = np.zeros((D, D), complex)
        for x in range(2):
            g += np.conj(U[x]) @ (Gx[x][y] * M[x][y]) / D
        gB.append(g)
    return [gA2, gB[0], gB[1]]


def expm_skew(Om):
    w, V = np.linalg.eigh(1j * Om)
    return (V * np.exp(-1j * w)) @ V.conj().T


def haar(D, rng):
    Z = (rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def maximise_I(beta, labs, d, D, rng, maxit=300):
    U = [np.eye(D, dtype=complex), haar(D, rng), haar(D, rng), haar(D, rng)]
    f = float(np.sum(beta * probs(U, labs, d)[0]))
    eta = 0.3
    for it in range(maxit):
        g = grads(U, labs, d, beta)
        dirs = [U[k].conj().T @ gk - gk.conj().T @ U[k] for k, gk in zip((1, 2, 3), g)]
        nrm = np.sqrt(sum(np.sum(np.abs(O) ** 2) for O in dirs)) + 1e-300
        ok = False
        while eta > 1e-9:
            U2 = list(U)
            for k, Om in zip((1, 2, 3), dirs):
                U2[k] = U[k] @ expm_skew(eta * Om / nrm)
            f2 = float(np.sum(beta * probs(U2, labs, d)[0]))
            if f2 > f + 1e-13:
                U, f, eta, ok = U2, f2, min(eta * 1.5, 1.0), True
                break
            eta *= 0.4
        if not ok:
            break
    return f


def run(d, D, nsample, nstart, seed):
    rng = np.random.default_rng(seed)
    beta = beta_np(d)
    IME = i_me(d)
    vs = 2 / IME
    comps = list(compositions(D, d))
    nc = len(comps)
    t0 = time.time()
    M = np.array(comps, float) / D                        # nc x d marginal vectors
    # per-link tables: noise term and transportation bound, indexed by (Alice composition, Bob composition)
    Nn = np.einsum("xyab,ia,jb->xyij", beta, M, M)        # noise contributions
    Nt = np.zeros((2, 2, nc, nc))
    for x in range(2):
        for y in range(2):
            for i in range(nc):
                for j in range(nc):
                    Nt[x, y, i, j] = ot_max(beta[x, y], tuple(M[i]), tuple(M[j]))
    surv = []
    npat = 0
    for i0 in range(nc):
        # arrays over (i1, j0, j1)
        In = (Nn[0, 0, i0][None, :, None] + Nn[0, 1, i0][None, None, :] + Nn[1, 0][:, :, None]
              + Nn[1, 1][:, None, :])
        Ns = (Nt[0, 0, i0][None, :, None] + Nt[0, 1, i0][None, None, :] + Nt[1, 0][:, :, None]
              + Nt[1, 1][:, None, :])
        ub = vs * np.minimum(IME, Ns) + (1 - vs) * In
        npat += ub.size
        idx = np.argwhere((ub > 2 + 1e-9) & (In > 1e-12))
        for i1, j0, j1 in idx:
            surv.append((float(ub[i1, j0, j1]), float(In[i1, j0, j1]), (comps[i0], comps[i1], comps[j0], comps[j1])))
    if nsample > 0 and len(surv) > nsample:
        surv.sort(key=lambda t: -t[0])
        top = surv[: nsample // 2]
        rest = [surv[k] for k in rng.choice(np.arange(nsample // 2, len(surv)), size=nsample - nsample // 2,
                                            replace=False)]
        surv = top + rest
    surv.sort(key=lambda t: -t[0])
    print(f"d={d} D={D}: {npat} patterns, {len(surv)} survivors examined after NS pruning "
          f"({time.time() - t0:.0f}s)", flush=True)
    best = (-np.inf, None)
    for k, (ub, In, r) in enumerate(surv):
        labs = [labels(x) for x in r]
        Imax = max(maximise_I(beta, labs, d, D, rng) for _ in range(nstart))
        F = vs * Imax + (1 - vs) * In
        if F > best[0]:
            best = (F, r)
        if F > 2 - 1e-9 or k % 25 == 0:
            print(f"   [{k}] r={r} I(n)={In:.6f} NS-ub F<={ub:.6f}  I_max~{Imax:.8f}  F={F:.10f}  "
                  f"best {best[0]:.10f}  ({time.time() - t0:.0f}s)" + ("   <-- F > 2" if F > 2 + 1e-9 else ""),
                  flush=True)
    print(f"RESULT d={d} D={D}: max F over survivors = {best[0]:.10f} at {best[1]}  (B1 needs <= 2)", flush=True)


if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
