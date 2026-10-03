"""
povm_search.py -- global search for CGLMP_d on Phi_D with general POVMs (see povm_core.py).
usage: python povm_search.py d D nstart seed [outtag]
Initialisations (cycled): gauss, rank (random rank pattern), rank1 (rank-one / overcomplete frames),
frame (harmonic tight frames: trine / SIC-like for D < d), dkzpert (DKZ (x) 1 + noise when d | D),
dkzcomp (DKZ on C^d compressed to a random D-dim subspace or dilated), seesaw-free L-BFGS on all four POVMs.
Prints one line per start, and the best value; saves the best strategy to best_d{d}_D{D}_{tag}.npz.
"""
import sys
import time
import numpy as np
from scipy.optimize import minimize
from povm_core import CGLMPPovm, I_ME, I_from_Pi, dkz_povms, check_povm

INITS = ['gauss', 'rank', 'rank1', 'frame', 'dkzpert', 'dkzcomp']


def cgauss(rng, *shape):
    return (rng.normal(size=shape) + 1j * rng.normal(size=shape)) / np.sqrt(2)


def haar(rng, n):
    Z = cgauss(rng, n, n)
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def sqrtm_psd(E):
    lam, U = np.linalg.eigh((E + E.conj().T) / 2)
    return (U * np.sqrt(np.maximum(lam, 0))) @ U.conj().T


def M_from_E(E):
    return np.stack([sqrtm_psd(e) for e in E])


def init_M(kind, d, D, rng, g):
    if kind == 'gauss':
        return cgauss(rng, d, D, D)
    if kind == 'rank':
        while True:
            r = rng.integers(0, D + 1, size=d)
            if r.sum() >= D:
                break
        M = 1e-3 * cgauss(rng, d, D, D)
        for a in range(d):
            M[a, :r[a]] += cgauss(rng, r[a], D)
        return M
    if kind == 'rank1':
        # each outcome gets ceil(D/d) or a random number of rank-one pieces ; overcomplete if d >= D
        M = 1e-4 * cgauss(rng, d, D, D)
        nrows = max(1, -(-D // d))
        for a in range(d):
            M[a, :nrows] += cgauss(rng, nrows, D)
        return M
    if kind == 'frame':
        # harmonic frame: rank-one elements |v_a><v_a|, v_a = (w^{a s_k})_k / sqrt(d), random distinct s_k;
        # for D < d this is a tight frame (trine-like: d = 3, D = 2; SIC-like for d = D^2 after rotation)
        w = np.exp(2j * np.pi / d)
        if D <= d:
            s = rng.choice(d, size=D, replace=False)
            V = np.array([[w ** (a * sk) for sk in s] for a in range(d)]) / np.sqrt(d)   # d x D, V^*V = 1
            U = haar(rng, D)
            M = np.zeros((d, D, D), complex)
            for a in range(d):
                M[a, 0] = (V[a] @ U.T)   # row vector v_a^T U^T -> E_a = conj... fine (any rank-one tight frame)
            return M + 1e-4 * cgauss(rng, d, D, D)
        # D > d: block-diagonal frame pieces of size <= d
        M = 1e-4 * cgauss(rng, d, D, D)
        row = 0
        off = 0
        while off < D:
            m = min(d, D - off)
            s = rng.choice(d, size=m, replace=False)
            V = np.array([[w ** (a * sk) for sk in s] for a in range(d)]) / np.sqrt(d)
            for a in range(d):
                M[a, row % D, off:off + m] += V[a]
            row += 1
            off += m
        U = haar(rng, D)
        return M @ U
    if kind == 'dkzpert':
        if D % d == 0:
            E = dkz_povms(d, D // d)[g]
            eps = 10 ** rng.uniform(-3, -0.5)
            return M_from_E(E) + eps * cgauss(rng, d, D, D)
        kind = 'dkzcomp'
    if kind == 'dkzcomp':
        # DKZ (x) 1_k on C^{dk} (k = ceil(D/d)) compressed by a random isometry C^D -> C^{dk}: E_a = V^* P_a V
        k = -(-D // d)
        P = dkz_povms(d, k)[g]
        Dbig = d * k
        if Dbig == D:
            V = haar(rng, D)
        else:
            V = haar(rng, Dbig)[:, :D]
        E = np.stack([V.conj().T @ p @ V for p in P])
        return M_from_E(E) + 1e-3 * cgauss(rng, d, D, D)
    raise ValueError(kind)


def run_start(P, kind, rng, maxiter=20000):
    d, D = P.d, P.D
    Ms = [init_M(kind, d, D, rng, g) for g in range(4)]
    # a common random unitary frame for the compressed / perturbed DKZ is irrelevant (gauge); keep as is
    z0 = P.pack(Ms)
    res = minimize(P.fg, z0, jac=True, method='L-BFGS-B',
                   options=dict(maxiter=maxiter, maxfun=4 * maxiter, maxcor=30, ftol=1e-16, gtol=1e-11))
    # re-polish from the POVMs themselves (re-parametrise M_a = E_a^{1/2}: well-conditioned K = 1)
    Es = P.Es_of_z(res.x)
    z1 = P.pack([M_from_E(E) for E in Es])
    res2 = minimize(P.fg, z1, jac=True, method='L-BFGS-B',
                    options=dict(maxiter=maxiter, maxfun=4 * maxiter, maxcor=30, ftol=1e-16, gtol=1e-12))
    if res2.fun <= res.fun:
        res = res2
    Es = P.Es_of_z(res.x)
    return res, Es


def main():
    d, D, nstart, seed = (int(t) for t in sys.argv[1:5])
    tag = sys.argv[5] if len(sys.argv) > 5 else f"s{seed}"
    rng = np.random.default_rng(seed)
    P = CGLMPPovm(d, D)
    ime = I_ME(d)
    best = (-np.inf, None, None)
    t0 = time.time()
    counts = {}
    print(f"# d={d} D={D} nstart={nstart} seed={seed}  I_ME(d) = {ime:.13f}", flush=True)
    for s in range(nstart):
        kind = INITS[s % len(INITS)]
        res, Es = run_start(P, kind, rng)
        I = I_from_Pi(res.fun, d)
        gmax = float(np.abs(res.jac).max())
        sm, mine = max(check_povm(E)[0] for E in Es), min(check_povm(E)[1] for E in Es)
        # non-projectivity measure: max_a ||E_a^2 - E_a||
        nonproj = max(float(np.abs(E @ E - E).max()) for E in Es)
        ranks = [tuple(int(np.sum(np.linalg.eigvalsh(e) > 1e-6)) for e in E) for E in Es]
        status = 'ME' if abs(I - ime) < 1e-9 else ('ABOVE' if I > ime + 1e-9 else 'below')
        counts[status] = counts.get(status, 0) + 1
        if I > best[0]:
            best = (I, Es, kind)
        print(f"start {s:4d} {kind:8s} I = {I:.13f}  I-I_ME = {I - ime:+.3e}  |grad| = {gmax:.1e}  "
              f"nonproj = {nonproj:.1e}  ranks = {ranks}  {status}  [{time.time() - t0:.0f}s]", flush=True)
    I, Es, kind = best
    print(f"# BEST d={d} D={D}: I = {I:.13f}  I_ME = {ime:.13f}  I-I_ME = {I - ime:+.3e}  (init {kind})  counts {counts}",
          flush=True)
    np.savez(f"best_d{d}_D{D}_{tag}.npz", Es=np.array(Es), I=I, I_ME=ime)


if __name__ == "__main__":
    main()
