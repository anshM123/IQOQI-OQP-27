"""
bell22d.py -- core routines for the (2 parties, 2 settings, d outcomes) scenario.

Conventions
-----------
Correlation vector q[x, y, a, b] = p(a, b | x, y), x, y in {0, 1}, a, b in {0..d-1}.
Flattened index i = ((x*2 + y)*d + a)*d + b.
Deterministic local strategies lam = (a0, a1, b0, b1), d**4 of them.

Statistical strength (van Dam - Gruenwald - Gill), setting distribution sigma[x, y]:
    KL(sigma; q) = min_{p local} sum_{xy} sigma_xy sum_ab q log(q / p)
Primal solver: constrained Newton method with support reduction (Y. Wang, JRSS B 69 (2007) 185)
for the mixing weights over deterministic strategies; certified by the dual (test factor)
    r = q/p*,  M = max_lam sum_{xy} sigma_xy r(lam(x), lam(y)|xy)  ->  KL >= KL(p*) - log M,
since sum sigma p r <= 1 for every local p after dividing r by M (Gibbs inequality).

Noise threshold (critical visibility) against ALL Bell inequalities of the scenario:
    v_c(q, n) = max { v : v q + (1 - v) n  is local }   (LP; HiGHS)
"""
import itertools
import numpy as np
from scipy.optimize import linprog


# ----------------------------------------------------------------------------------------------
# scenario data
# ----------------------------------------------------------------------------------------------
_cache = {}


def det_matrix(d):
    """E[lam, i] = 1 if deterministic strategy lam gives outcome pair (a,b) on (x,y) at index i."""
    if d in _cache:
        return _cache[d]
    S = np.array(list(itertools.product(range(d), repeat=4)))   # a0 a1 b0 b1
    m = len(S)
    E = np.zeros((m, 4 * d * d))
    rows = np.arange(m)
    for x in range(2):
        for y in range(2):
            idx = ((x * 2 + y) * d + S[:, x]) * d + S[:, 2 + y]
            E[rows, idx] = 1.0
    _cache[d] = (S, E)
    return S, E


def flat(q):
    return np.asarray(q).reshape(-1)


# ----------------------------------------------------------------------------------------------
# quantum correlations
# ----------------------------------------------------------------------------------------------
def probs_pure(psi_mat, A, B):
    """psi_mat: DxD coefficient matrix of |psi> = sum psi_mat[i,j] |i>|j>.
    A[x]: D x d matrix whose columns are Alice's (orthonormal) basis vectors for setting x
          (rank-one projective measurement); same for B[y].
    returns q[x,y,a,b] = |<a_x| <b_y| psi>|^2."""
    d = A[0].shape[1]
    q = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            T = A[x].conj().T @ psi_mat @ B[y].conj()
            q[x, y] = np.abs(T) ** 2
    return q


def dkz_bases(d):
    """DKZ/CGLMP Fourier measurements in the convention stated in THEOREM.md:
    Alice |a>_x = d^-1/2 sum_k w^{k(a+alpha_x)}|k>, alpha = (1/2, 0) [x=0,1];
    Bob   |b>_y = d^-1/2 sum_k w^{-k(b+beta_y)}|k>, beta = (1/4, -1/4)."""
    k = np.arange(d)
    A, B = [], []
    for al in (0.5, 0.0):
        A.append(np.array([np.exp(2j * np.pi * k * (a + al) / d) / np.sqrt(d) for a in range(d)]).T)
    for be in (0.25, -0.25):
        B.append(np.array([np.exp(-2j * np.pi * k * (b + be) / d) / np.sqrt(d) for b in range(d)]).T)
    return A, B


def maxent(d):
    return np.eye(d) / np.sqrt(d)


def cglmp_coeffs(d):
    """coefficient tensor c[x,y,a,b] of the chain form Pi = P(X1<Y1)+P(Y1<X2)+P(X2<Y2)+P(Y2<=X1)
    (x index 0 = X1, 1 = X2; y index 0 = Y1, 1 = Y2); local minimum 1, I = 4 - 2(d Pi - 1)/(d-1)."""
    a = np.arange(d)
    lt = (a[:, None] < a[None, :]).astype(float)   # [a < b]
    le = (a[:, None] <= a[None, :]).astype(float)
    c = np.zeros((2, 2, d, d))
    c[0, 0] = lt          # X1 < Y1
    c[1, 0] = lt.T        # Y1 < X2   <=> b < a on (x=1,y=0)
    c[1, 1] = lt          # X2 < Y2
    c[0, 1] = le.T        # Y2 <= X1  <=> b <= a on (x=0,y=1)
    return c


def cglmp_I(q):
    d = q.shape[2]
    Pi = float(np.sum(cglmp_coeffs(d) * q))
    return 4 - 2 * (d * Pi - 1) / (d - 1)


# ----------------------------------------------------------------------------------------------
# KL statistical strength
# ----------------------------------------------------------------------------------------------
def kl_strength_em(q, sigma=None, tol=1e-12, maxit=20000, w0=None, verbose=False):
    """KL(sigma; q) = min over local p.  EM (multiplicative) updates on the weights of the d^4
    deterministic strategies, accelerated by SQUAREM (Varadhan-Roland 2008).
    returns dict(kl = KL(p*) [upper value, p* local], lb = KL(p*) - log M [certified lower value],
    M = max_lam gradient, p = p* (conditional), w = weights over all strategies)."""
    q = np.asarray(q, float)
    d = q.shape[2]
    S, E = det_matrix(d)
    if sigma is None:
        sigma = np.full((2, 2), 0.25)
    sig = np.repeat(np.asarray(sigma, float).reshape(4), d * d)
    qj = sig * flat(q)
    mask = qj > 0
    qj_m = qj[mask]
    Ej_m = (E * sig[None, :])[:, mask]
    m = E.shape[0]
    const = float(np.sum(qj_m * np.log(qj_m)))
    w = np.full(m, 1.0 / m) if w0 is None else np.maximum(np.asarray(w0, float), 0) + 1e-12 / m
    w = w / w.sum()

    def em(ww):
        p = np.maximum(ww @ Ej_m, 1e-300)
        g = Ej_m @ (qj_m / p)
        wn = ww * g
        return wn / wn.sum()

    def negll(ww):
        return -float(np.sum(qj_m * np.log(np.maximum(ww @ Ej_m, 1e-300))))

    f = negll(w)
    it = 0
    while it < maxit:
        w1 = em(w)
        w2 = em(w1)
        it += 2
        r = w1 - w
        v = w2 - w1 - r
        nv = np.linalg.norm(v)
        if nv > 0:
            alpha = -np.linalg.norm(r) / nv
            alpha = min(alpha, -1.0)
            wp = w - 2 * alpha * r + alpha * alpha * v
            wp = np.maximum(wp, 0)
            if wp.sum() > 0:
                wp = em(wp / wp.sum())
                it += 1
                fp = negll(wp)
            else:
                fp = np.inf
        else:
            fp = np.inf
        f2 = negll(w2)
        if fp <= f2:
            w, fnew = wp, fp
        else:
            w, fnew = w2, f2
        if it % 20 < 3 or fnew > f - 1e-18:
            p = w @ Ej_m
            M = float((Ej_m @ (qj_m / p)).max())
            if verbose:
                print(it, fnew + const, M - 1)
            if M - 1 < tol:
                f = fnew
                break
        f = fnew
    w = (1 - 1e-14) * w + 1e-14 / m          # full support (avoids p = 0 on cells with tiny q > 0)
    p = w @ Ej_m
    kl = float(np.sum(qj_m * np.log(qj_m / p)))
    M = float((Ej_m @ (qj_m / p)).max())
    pfull = (w @ E).reshape(2, 2, d, d)
    return dict(kl=kl, lb=kl - np.log(M), M=M, p=pfull, w=w, iters=it)


def kl_strength_ipm(q, sigma=None, r0=None, mu_final=1e-15, verbose=False):
    """KL(sigma; q) via a log-barrier Newton method on the DUAL (test-factor) problem
        max_r  sum_i qj_i log r_i   s.t.  sum_i Ej[lam, i] r_i <= 1  for all deterministic lam
    (cells with q = 0 are dropped, i.e. r = 0 there).  Every strictly feasible r gives the
    certified lower bound sum qj log r (Gibbs inequality); the barrier multipliers
    w_lam = mu / (1 - s_lam) give a local model p (upper value KL(p)).
    returns dict(kl=upper, lb=lower, p, w, r)."""
    q = np.asarray(q, float)
    d = q.shape[2]
    S, E = det_matrix(d)
    if sigma is None:
        sigma = np.full((2, 2), 0.25)
    sig = np.repeat(np.asarray(sigma, float).reshape(4), d * d)
    qj = sig * flat(q)
    mask = qj > 1e-300
    qm = qj[mask]
    Em = (E * sig[None, :])[:, mask]            # m x n
    m, n = Em.shape
    r = np.full(n, 0.5) if r0 is None else np.asarray(r0, float)[: n] * 0.98
    s_ = Em @ r
    if np.any(s_ >= 1) or np.any(r <= 0):
        r = np.full(n, 0.5)
    mu = 1.0 / m

    def phi(rr, mu_):
        ss = Em @ rr
        if np.any(ss >= 1) or np.any(rr <= 0):
            return np.inf
        return -np.sum(qm * np.log(rr)) - mu_ * np.sum(np.log1p(-ss))

    while True:
        for it in range(100):
            ss = Em @ r
            u = 1.0 / (1 - ss)
            g = -qm / r + mu * (Em.T @ u)
            H = np.diag(qm / r ** 2) + mu * (Em.T * (u * u)[None, :]) @ Em
            try:
                step = -np.linalg.solve(H, g)
            except np.linalg.LinAlgError:
                step = -np.linalg.lstsq(H, g, rcond=None)[0]
            dec = -g @ step
            if dec < 1e-14 * max(1.0, abs(phi(r, mu))):
                break
            t = 1.0
            f0 = phi(r, mu)
            while True:
                rn = r + t * step
                fn = phi(rn, mu)
                if np.isfinite(fn) and fn <= f0 - 0.25 * t * dec:
                    break
                t *= 0.5
                if t < 1e-14:
                    break
            r = rn if np.isfinite(fn) else r
            if t < 1e-14:
                break
        if verbose:
            print("mu", mu, "lb", np.sum(qm * np.log(r)))
        if mu <= mu_final:
            break
        mu = max(mu * 0.1, mu_final)
    ss = Em @ r
    w = mu / (1 - ss)
    w = w / w.sum()
    p = w @ Em
    kl = float(np.sum(qm * np.log(qm / p)))
    lb = float(np.sum(qm * np.log(r)))
    M = float(ss.max())
    # r is (strictly) feasible: lb is a certified lower bound; kl is attained by the local model w
    rfull = np.zeros(4 * d * d)
    rfull[mask] = r
    return dict(kl=kl, lb=lb, M=M, p=(w @ E).reshape(2, 2, d, d), w=w, r=rfull)


def kl_strength(q, sigma=None, w0=None, gap=1e-10, em_maxit=4000):
    """robust KL strength: EM+SQUAREM (warm start w0); if the certified gap exceeds `gap`,
    fall back to the barrier method on the dual and polish its local model by EM.
    returns dict(kl = upper value (attained by an explicit local model), lb = certified lower value,
    p, w)."""
    r1 = kl_strength_em(q, sigma=sigma, w0=w0, maxit=em_maxit)
    if r1['kl'] - r1['lb'] <= gap:
        return r1
    r2 = kl_strength_ipm(q, sigma=sigma)
    r3 = kl_strength_em(q, sigma=sigma, w0=r2['w'], maxit=em_maxit)
    best_ub = min(r1['kl'], r3['kl'])
    best_lb = max(r1['lb'], r2['lb'], r3['lb'])
    out = r3 if r3['kl'] <= r1['kl'] else r1
    out = dict(out)
    out['kl'] = best_ub
    out['lb'] = best_lb
    return out


# ----------------------------------------------------------------------------------------------
# noise threshold LP
# ----------------------------------------------------------------------------------------------
def critical_visibility(q, n=None):
    """v_c = max v s.t. v q + (1-v) n local.  returns (v_c, beta) where beta (flat) is the dual:
    a Bell functional with beta.p <= 0 ... (normalised so that beta.(q-n) = 1 at the optimum)."""
    q = np.asarray(q, float)
    d = q.shape[2]
    S, E = det_matrix(d)
    if n is None:
        n = np.full_like(q, 1.0 / d ** 2)
    qf, nf = flat(q), flat(n)
    m = E.shape[0]
    # variables: w (m), v ; constraints E^T w - v (q - n) = n
    Aeq = np.hstack([E.T, -(qf - nf)[:, None]])
    beq = nf
    c = np.zeros(m + 1)
    c[-1] = -1.0
    bounds = [(0, None)] * m + [(None, None)]
    res = linprog(c, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
    if res.status != 0:
        raise RuntimeError(res.message)
    v = res.x[-1]
    beta = res.eqlin.marginals          # sensitivity of objective (-v) wrt beq
    return float(v), np.asarray(beta)


# ----------------------------------------------------------------------------------------------
# parametrisations
# ----------------------------------------------------------------------------------------------
def unitary_from(params, D):
    """exp(i H) with H Hermitian built from D*D real parameters."""
    H = np.zeros((D, D), complex)
    iu = np.triu_indices(D, 1)
    n_off = len(iu[0])
    H[iu] = params[:n_off] + 1j * params[n_off:2 * n_off]
    H = H + H.conj().T
    H[np.diag_indices(D)] = params[2 * n_off:2 * n_off + D]
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * w)) @ V.conj().T


if __name__ == "__main__":
    # smoke tests
    for d in (2, 3, 4):
        A, B = dkz_bases(d)
        q = probs_pure(maxent(d), A, B)
        r = kl_strength(q)
        v, _ = critical_visibility(q)
        print(f"d={d}: I_DKZ,ME = {cglmp_I(q):.10f}  2/I = {2/cglmp_I(q):.8f}  v_c(LP) = {v:.8f}  "
              f"KL = {r['kl']/np.log(2):.8f} bits  (certified lb {r['lb']/np.log(2):.8f})  M-1 = {r['M']-1:.1e}")
