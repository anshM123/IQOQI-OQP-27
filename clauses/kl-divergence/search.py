"""
search.py -- global numerical search over rank-one projective measurements (and optionally pure
states) in the (2,2,d) scenario, for
  (KL)    the statistical strength with uniform settings, KL_uni(q) = min_{p local} D(q || p);
  (NOISE) the critical visibility v_c(q) against ALL Bell inequalities (white noise 1/d^2 on
          the state; for rank-one PVMs the noise correlations are uniform 1/d^2).

Both are done by monotone "linearise-and-seesaw" iterations:
  KL:    for the current q, the optimal test factor r = q/p* satisfies E_p[r] <= 1 for every local
         p (sigma-weighted), hence KL(q') >= sum sigma q' log r for EVERY q', with equality at q.
         Maximising the linear Bell functional  c = sigma log r  over the quantum set (seesaw)
         therefore cannot decrease KL.
  NOISE: the LP dual gives the Bell functional beta with v_c(q) = (b - beta.n)/(beta.(q - n));
         maximising beta.q' over the quantum set cannot increase v_c.
Seesaw for a linear functional over rank-one PVMs on a fixed state: for each measurement in turn,
maximise sum_a <u_a|W_a|u_a> over orthonormal bases by the monotone polar-decomposition iteration
(minorise the convex quadratic by its tangent; W_a shifted to be PSD).  State update (if free):
top eigenvector of the Bell operator.
"""
import sys
import time
import numpy as np
from bell22d import (det_matrix, probs_pure, dkz_bases, maxent, kl_strength, critical_visibility,
                     cglmp_I)

LOG2 = np.log(2)


def haar_unitary(D, rng):
    Z = (rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def linear_value(c, psi, A, B):
    return float(np.sum(c * probs_pure(psi, A, B)))


def _polar(M):
    U, s, Vh = np.linalg.svd(M)
    return U @ Vh


def improve_basis(U, Ws, iters=20):
    """maximise sum_a <u_a|W_a|u_a> over unitaries U (columns u_a); W_a Hermitian."""
    D = U.shape[0]
    shift = max(0.0, -min(np.linalg.eigvalsh(W)[0] for W in Ws)) + 1e-9
    Wp = [W + shift * np.eye(D) for W in Ws]
    for _ in range(iters):
        M = np.column_stack([Wp[a] @ U[:, a] for a in range(len(Ws))])
        U = _polar(M)
    return U


def seesaw(c, psi, A, B, rounds=10, inner=10, free_state=False):
    """maximise sum c q over Alice/Bob rank-one PVMs (and the pure state if free_state)."""
    d = A[0].shape[1]
    D = psi.shape[0]
    A = [a.copy() for a in A]
    B = [b.copy() for b in B]
    psi = psi.copy()
    for _ in range(rounds):
        # Alice: W_{a|x} = sum_{y,b} c[x,y,a,b] * Psi Bbar_y |b><b| B_y^T Psi^dagger  (acts on A space)
        for x in range(2):
            Ws = []
            for a in range(d):
                W = np.zeros((D, D), complex)
                for y in range(2):
                    V = psi @ B[y].conj()          # columns: Psi |b_y>^*
                    W += (V * c[x, y, a][None, :]) @ V.conj().T
                Ws.append(W)
            A[x] = improve_basis(A[x], Ws, inner)
        for y in range(2):
            Ws = []
            for b in range(d):
                W = np.zeros((D, D), complex)
                for x in range(2):
                    V = psi.T @ A[x].conj()        # columns: Psi^T |a_x>^*
                    W += (V * c[x, y, :, b][None, :]) @ V.conj().T
                Ws.append(W)
            B[y] = improve_basis(B[y], Ws, inner)
        if free_state:
            # Bell operator on C^D (x) C^D: sum c |a_x><a_x| (x) |b_y><b_y|; top eigenvector
            Bop = np.zeros((D * D, D * D), complex)
            for x in range(2):
                for y in range(2):
                    for a in range(d):
                        Pa = np.outer(A[x][:, a], A[x][:, a].conj())
                        for b in range(d):
                            if c[x, y, a, b] != 0:
                                Pb = np.outer(B[y][:, b], B[y][:, b].conj())
                                Bop += c[x, y, a, b] * np.kron(Pa, Pb)
            w, V = np.linalg.eigh((Bop + Bop.conj().T) / 2)
            psi = V[:, -1].reshape(D, D)
    return psi, A, B


def kl_ascent(psi, A, B, free_state=False, maxit=200, tol=1e-11, verbose=False, vis=1.0):
    """monotone ascent of KL(vis*q + (1-vis)*uniform) (vis = 1: noiseless)."""
    d = A[0].shape[1]
    un = np.full((2, 2, d, d), 1.0 / d ** 2)

    def corr(ps, AA, BB):
        return vis * probs_pure(ps, AA, BB) + (1 - vis) * un
    q = corr(psi, A, B)
    r = kl_strength(q)
    val = r['kl']
    w = r['w']
    for it in range(maxit):
        p = r['p']
        with np.errstate(divide='ignore'):
            logr = np.where(q > 0, np.log(np.maximum(q, 1e-300) / np.maximum(p, 1e-300)), -50.0)
        logr = np.maximum(logr, -50.0)
        c = 0.25 * vis * logr
        psi2, A2, B2 = seesaw(c, psi, A, B, rounds=3, inner=5, free_state=free_state)
        q2 = corr(psi2, A2, B2)
        r2 = kl_strength(q2, w0=w)
        if (not np.isfinite(r2['kl'])) or r2['kl'] <= val + tol:
            if verbose:
                print(f"   stop it={it} KL={val/LOG2:.10f} bits")
            break
        psi, A, B, q, r, val, w = psi2, A2, B2, q2, r2, r2['kl'], r2['w']
        if verbose and it % 10 == 0:
            print(f"   it={it} KL={val/LOG2:.10f} bits", flush=True)
    return val, psi, A, B, r


def noise_descent(psi, A, B, free_state=False, maxit=300, tol=1e-12, verbose=False):
    q = probs_pure(psi, A, B)
    v, beta = critical_visibility(q)
    d = q.shape[2]
    for it in range(maxit):
        c = beta.reshape(2, 2, d, d)
        # maximise violation direction: v_c decreases when beta.q' moves in the direction that
        # makes the dual objective ... we simply try both signs and keep the improving one
        best = None
        for sgn in (1.0, -1.0):
            psi2, A2, B2 = seesaw(sgn * c, psi, A, B, rounds=3, inner=5, free_state=free_state)
            q2 = probs_pure(psi2, A2, B2)
            v2, beta2 = critical_visibility(q2)
            if best is None or v2 < best[0]:
                best = (v2, beta2, psi2, A2, B2, q2)
        if best[0] >= v - tol:
            break
        v, beta, psi, A, B, q = best[0], best[1], best[2], best[3], best[4], best[5]
        if verbose and it % 10 == 0:
            print(f"   it={it} v_c={v:.10f}", flush=True)
    return v, psi, A, B, beta


def random_start(d, D, rng, free_state):
    A = [haar_unitary(D, rng)[:, :d] for _ in range(2)]
    B = [haar_unitary(D, rng)[:, :d] for _ in range(2)]
    if free_state:
        psi = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))
        psi /= np.linalg.norm(psi)
    else:
        psi = maxent(D)
    return psi, A, B


if __name__ == "__main__":
    mode = sys.argv[1]            # kl | noise
    d = int(sys.argv[2])
    nstart = int(sys.argv[3])
    free = (len(sys.argv) > 4 and sys.argv[4] == "free")
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    rng = np.random.default_rng(seed)
    A0, B0 = dkz_bases(d)
    q0 = probs_pure(maxent(d), A0, B0)
    ref_kl = kl_strength(q0)['kl']
    ref_v = critical_visibility(q0)[0]
    print(f"mode={mode} d={d} starts={nstart} free_state={free} seed={seed}")
    print(f"reference DKZ+Phi_d: KL = {ref_kl/LOG2:.10f} bits, v_c = {ref_v:.10f}", flush=True)
    results = []
    t0 = time.time()
    for s in range(nstart):
        psi, A, B = random_start(d, d, rng, free)
        if mode == "kl":
            # enter the nonlocal region first (KL = 0 gives no ascent direction)
            for attempt in range(20):
                if kl_strength(probs_pure(psi, A, B))['kl'] > 1e-10:
                    break
                vv, psi, A, B, _ = noise_descent(psi, A, B, free_state=free, maxit=40)
                if vv < 1 - 1e-9:
                    break
                psi, A, B = random_start(d, d, rng, free)
            val, psi, A, B, r = kl_ascent(psi, A, B, free_state=free)
            q = probs_pure(psi, A, B)
            results.append(val)
            print(f"start {s:3d}: KL = {val/LOG2:.10f} bits  (I_CGLMP = {cglmp_I(q):.6f})  "
                  f"best {max(results)/LOG2:.10f}  [{time.time()-t0:.0f}s]", flush=True)
        elif mode == "noise":
            v, psi, A, B, beta = noise_descent(psi, A, B, free_state=free)
            q = probs_pure(psi, A, B)
            results.append(v)
            print(f"start {s:3d}: v_c = {v:.10f}  (I_CGLMP = {cglmp_I(q):.6f})  best {min(results):.10f}  "
                  f"[{time.time()-t0:.0f}s]", flush=True)
        else:   # homotopy: KL ascent at decreasing visibility, then LP polish
            for attempt in range(20):
                if kl_strength(probs_pure(psi, A, B))['kl'] > 1e-10:
                    break
                vv, psi, A, B, _ = noise_descent(psi, A, B, free_state=free, maxit=40)
                if vv < 1 - 1e-9:
                    break
                psi, A, B = random_start(d, d, rng, free)
            v_last = None
            for vis in (1.0, 0.85, 0.78, 0.74, 0.72, 0.71, 0.70, 0.695, 0.69, 0.685, 0.68):
                val, psi2, A2, B2, r = kl_ascent(psi, A, B, free_state=free, vis=vis)
                if val < 1e-12:
                    break
                psi, A, B = psi2, A2, B2
                v_last = vis
            v, psi, A, B, beta = noise_descent(psi, A, B, free_state=free)
            q = probs_pure(psi, A, B)
            results.append(v)
            print(f"start {s:3d}: last nonlocal vis {v_last}  v_c(LP polish) = {v:.10f}  (I_CGLMP = {cglmp_I(q):.6f})  "
                  f"best {min(results):.10f}  [{time.time()-t0:.0f}s]", flush=True)
        if s == 0 or (mode == "kl" and results[-1] >= max(results)) or (mode != "kl" and results[-1] <= min(results)):
            np.save(f"best_{mode}_d{d}_{'free' if free else 'me'}_s{seed}.npy",
                    np.array([psi] + A + B, dtype=object), allow_pickle=True)
