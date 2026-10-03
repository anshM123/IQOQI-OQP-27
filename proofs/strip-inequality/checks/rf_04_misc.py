# rf_04: misc checks -- Lemma 4 (t -> +-inf limits), the bound F <= (M/2pi)||g - s||/sqrt(tau(1-tau)) and F = 0 off (lmin,lmax),
# the count of non-real roots <= 2 min(r, M-r) (Remark 4.2), and the equality case of Theorem 2.
import numpy as np, mpmath as mp
from rf_core import rand_inst, F_vals, defect_mp, compressions

rng = np.random.default_rng(4242)
mp.mp.dps = 40
print("Lemma 4:")
for M, r in [(3, 1), (5, 2), (6, 4)]:
    B, g = rand_inst(M, r, 2.0, rng); P = np.eye(M) - B
    a = 0.7
    Am = mp.matrix((a*g).tolist()); Pm = mp.matrix(P.tolist())
    bb, pp = compressions(a*B @ g @ B, np.eye(M)) if False else compressions(B, a*g)
    trB = sum(mp.exp(x) for x in bb); trP = sum(mp.exp(x) for x in pp)
    out = []
    for t in [20, 80, 320]:
        v1 = sum(mp.expm(Am - t*Pm)[i, i] for i in range(M)).real
        v2 = (mp.exp(-t)*sum(mp.expm(Am + t*Pm)[i, i] for i in range(M))).real
        out.append((t, float(v1 - trB), float(v2 - trP)))
    print(f"   M={M} r={r}: (t, Tr e^(A-tP) - Tr_B e^(BAB), e^(-t)Tr e^(A+tP) - Tr_P e^(PAP)) = {[(t, f'{x:.1e}', f'{y:.1e}') for t, x, y in out]}")

print("Lemma 1 bound / support / Remark 4.2 count:")
worst_ratio = 0; bad_support = 0; maxpairs_ok = True
for trial in range(40):
    M = int(rng.integers(3, 7)); r = int(rng.integers(1, M)); B, g = rand_inst(M, r, float(rng.choice([1, 10, 100])), rng)
    ev = np.linalg.eigvalsh(g); lmin, lmax = ev[0], ev[-1]
    s = np.linspace(lmin - 0.2*(lmax - lmin), lmax + 0.2*(lmax - lmin), 801)
    for tau in [1e-3, 0.1, 0.37, 0.5, 0.8, 0.999]:
        F = F_vals(B, g, s, tau)
        nrm = np.array([np.linalg.norm(g - x*np.eye(M), 2) for x in s])
        bound = M/(2*np.pi)*nrm/np.sqrt(tau*(1 - tau))
        worst_ratio = max(worst_ratio, np.max(F/bound))
        bad_support += int(np.sum(F[(s <= lmin) | (s >= lmax)] > 0))
        P = np.eye(M) - B
        A = (P/(1 - tau) - B/tau)[None] @ (g[None] - s[:, None, None]*np.eye(M)[None])
        evs = np.linalg.eigvals(A)
        nonreal = np.sum(np.abs(evs.imag) > 1e-9*np.abs(evs).max(-1, keepdims=True), axis=1)
        if nonreal.max() > 2*min(r, M - r):
            maxpairs_ok = False
print(f"   max F/bound = {worst_ratio:.3f} (must be <= 1);  # grid points with F > 0 outside (lmin,lmax): {bad_support};"
      f"  #non-real roots <= 2 min(r,M-r) everywhere: {maxpairs_ok}")

print("Theorem 2 equality case:")
for M, r in [(3, 1), (5, 2)]:
    U = np.linalg.qr(rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)))[0]
    B = U[:, :r] @ U[:, :r].conj().T; P = np.eye(M) - B
    G = rng.normal(size=(M, M)) + 1j*rng.normal(size=(M, M)); G = (G + G.conj().T)/2
    gc = B @ G @ B + P @ G @ P                      # commutes with B
    for eps in [0.0, 1e-3, 1e-1]:
        g = gc + eps*(B @ G @ P + P @ G @ B)
        ds = [float(defect_mp(B, g, lam)[0]) for lam in [-1.0, 0.0, 0.5, 2.0]]
        print(f"   M={M} r={r} eps={eps}: defect(lam = -1, 0, .5, 2) = {[f'{d:.3e}' for d in ds]}")
