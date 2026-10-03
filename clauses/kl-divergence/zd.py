"""
zd.py -- Z_d-symmetric (Fourier-diagonal) strategies on |Phi_d> and symmetry-reduced solvers.

Fourier-diagonal family ("DFT + diagonal unitaries"):
    Alice |a>_x = d^-1/2 sum_k e^{i theta_x(k)} w^{ k a}|k>,  Bob |b>_y = d^-1/2 sum_k e^{i eta_y(k)} w^{-k b}|k>
On |Phi_d>:  p(a,b|x,y) = P_xy(b - a mod d)/d,  P_xy(m) = d^-2 |sum_k e^{-i(theta_x(k)+eta_y(k))} w^{k m}|^2.
DKZ: theta_x(k) = 2 pi k alpha_x/d, eta_y(k) = -2 pi k beta_y/d, alpha = (1/2, 0), beta = (1/4, -1/4).

Symmetry reduction (rigorous): q is invariant under the simultaneous shift a -> a+s, b -> b+s; the
local set is invariant; KL(q||.) is convex and the LP feasibility set is convex, so both the KL
minimiser and the LP can be restricted to shift-invariant local points = convex hull of the
orbit-averages of deterministic strategies, V_lam[x,y,m] = [b_y - a_x = m mod d], lam = (0,a1,b0,b1).
"""
import itertools
import numpy as np
from scipy.optimize import linprog, minimize

LOG2 = np.log(2)


def zd_vertices(d):
    S = np.array([(0,) + t for t in itertools.product(range(d), repeat=3)])   # a0=0, a1, b0, b1
    V = np.zeros((len(S), 2, 2, d))
    rows = np.arange(len(S))
    for x in range(2):
        for y in range(2):
            m = (S[:, 2 + y] - S[:, x]) % d
            V[rows, x, y, m] = 1.0
    return S, V.reshape(len(S), 4 * d)


def fourier_P(theta, eta):
    """theta, eta: arrays (2, d). returns P[x,y,m]."""
    d = theta.shape[1]
    k = np.arange(d)
    m = np.arange(d)
    W = np.exp(2j * np.pi * np.outer(k, m) / d)          # w^{k m}
    P = np.zeros((2, 2, d))
    for x in range(2):
        for y in range(2):
            g = np.exp(-1j * (theta[x] + eta[y]))
            P[x, y] = np.abs(g @ W) ** 2 / d ** 2
    return P


def dkz_phases(d):
    k = np.arange(d)
    theta = np.array([2 * np.pi * k * 0.5 / d, 0 * k])
    eta = np.array([-2 * np.pi * k * 0.25 / d, 2 * np.pi * k * 0.25 / d])
    return theta, eta


def kl_generic(qj, Ej, w0=None, tol=1e-13, maxit=20000, barrier=True):
    """min_{w in simplex} sum qj log(qj / (w Ej)); qj joint (sums to 1), Ej rows = joint vertices.
    returns (ub, lb, w, r) with lb certified by the dual test factor."""
    mask = qj > 1e-300
    qm = qj[mask]
    Em = Ej[:, mask]
    m, n = Em.shape
    # --- EM + SQUAREM
    w = np.full(m, 1.0 / m) if w0 is None else np.maximum(w0, 0) + 1e-12 / m
    w /= w.sum()

    def em(ww):
        p = np.maximum(ww @ Em, 1e-300)
        wn = ww * (Em @ (qm / p))
        return wn / wn.sum()

    def nll(ww):
        return -float(np.sum(qm * np.log(np.maximum(ww @ Em, 1e-300))))
    f = nll(w)
    for it in range(maxit // 3):
        w1 = em(w)
        w2 = em(w1)
        rr = w1 - w
        vv = w2 - w1 - rr
        nv = np.linalg.norm(vv)
        cand = [(nll(w2), w2)]
        if nv > 0:
            al = min(-np.linalg.norm(rr) / nv, -1.0)
            wp = np.maximum(w - 2 * al * rr + al * al * vv, 0)
            if wp.sum() > 0:
                wp = em(wp / wp.sum())
                cand.append((nll(wp), wp))
        fn, w = min(cand, key=lambda t: t[0])
        if it % 10 == 0:
            p = np.maximum(w @ Em, 1e-300)
            M = (Em @ (qm / p)).max()
            if M - 1 < tol:
                break
        f = fn
    w = (1 - 1e-14) * w + 1e-14 / m
    p = w @ Em
    ub = float(np.sum(qm * np.log(qm / p)))
    M = float((Em @ (qm / p)).max())
    lb = ub - np.log(M)
    r = (qm / p) / M
    if ub - lb > 1e-10 and barrier:
        # barrier method on the dual
        rr_ = np.full(n, 0.5)
        mu = 1.0 / m

        def phi(x, mu_):
            s = Em @ x
            if np.any(s >= 1) or np.any(x <= 0):
                return np.inf
            return -np.sum(qm * np.log(x)) - mu_ * np.sum(np.log1p(-s))
        while True:
            for _ in range(100):
                s = Em @ rr_
                u = 1.0 / (1 - s)
                g = -qm / rr_ + mu * (Em.T @ u)
                H = np.diag(qm / rr_ ** 2) + mu * (Em.T * (u * u)[None, :]) @ Em
                step = -np.linalg.solve(H, g)
                dec = -g @ step
                if dec < 1e-15:
                    break
                t = 1.0
                f0 = phi(rr_, mu)
                while t > 1e-14:
                    fn = phi(rr_ + t * step, mu)
                    if np.isfinite(fn) and fn <= f0 - 0.25 * t * dec:
                        break
                    t *= 0.5
                if t <= 1e-14:
                    break
                rr_ = rr_ + t * step
            if mu <= 1e-15:
                break
            mu = max(mu * 0.1, 1e-15)
        lb2 = float(np.sum(qm * np.log(rr_)))
        s = Em @ rr_
        w2 = mu / (1 - s)
        w2 /= w2.sum()
        ub2, lb3, w3, r3 = kl_generic(qj, Ej, w0=w2, tol=tol, maxit=maxit, barrier=False)
        if lb2 > lb:
            lb, r = lb2, rr_
        if lb3 > lb:
            lb, r = lb3, r3
        if ub2 < ub:
            ub, w = ub2, w3
    rfull = np.zeros(len(qj))
    rfull[mask] = r
    return ub, lb, w, rfull


_zcache = {}


def kl_zd(P, w0=None):
    """KL (uniform settings) of the Z_d-invariant correlation p(a,b|xy) = P[x,y,b-a]/d."""
    d = P.shape[2]
    if d not in _zcache:
        _zcache[d] = zd_vertices(d)
    S, V = _zcache[d]
    qj = 0.25 * P.reshape(-1)
    Ej = 0.25 * V
    return kl_generic(qj, Ej, w0=w0)


def vc_zd(P):
    """critical visibility (white noise = uniform) of the Z_d-invariant correlation, via the
    reduced LP over shift-invariant local points."""
    d = P.shape[2]
    if d not in _zcache:
        _zcache[d] = zd_vertices(d)
    S, V = _zcache[d]
    qf = P.reshape(-1)
    nf = np.full(4 * d, 1.0 / d)
    m = V.shape[0]
    Aeq = np.hstack([V.T, -(qf - nf)[:, None]])
    c = np.zeros(m + 1)
    c[-1] = -1
    res = linprog(c, A_eq=Aeq, b_eq=nf, bounds=[(0, None)] * m + [(None, None)], method="highs")
    return float(res.x[-1]), res


def optimise_fourier(d, objective="kl", nstart=20, seed=0, verbose=True):
    rng = np.random.default_rng(seed)
    best = None

    def unpack(z):
        theta = np.vstack([np.zeros(d), z[:d]])
        eta = np.vstack([z[d:2 * d], z[2 * d:]])
        return theta, eta

    def f(z):
        P = fourier_P(*unpack(z))
        if objective == "kl":
            ub, lb, w, r = kl_zd(P)
            return -lb
        else:
            v, _ = vc_zd(P)
            return v
    for s in range(nstart):
        z0 = rng.uniform(0, 2 * np.pi, size=3 * d)
        res = minimize(f, z0, method="Powell", options=dict(maxiter=20000, xtol=1e-9, ftol=1e-13))
        res = minimize(f, res.x, method="Nelder-Mead", options=dict(maxiter=20000, xatol=1e-10, fatol=1e-15))
        val = -res.fun if objective == "kl" else res.fun
        better = best is None or (val > best[0] if objective == "kl" else val < best[0])
        if better:
            best = (val, res.x)
        if verbose:
            unit = LOG2 if objective == "kl" else 1.0
            print(f"  d={d} start {s}: {val/unit:.10f}  best {best[0]/unit:.10f}", flush=True)
    return best, unpack(best[1])


if __name__ == "__main__":
    import sys
    for d in range(2, 9):
        P = fourier_P(*dkz_phases(d))
        ub, lb, w, r = kl_zd(P)
        v, _ = vc_zd(P)
        print(f"DKZ d={d}: KL (Z_d-reduced) in [{lb/LOG2:.12f}, {ub/LOG2:.12f}] bits;  v_c = {v:.10f}", flush=True)
