"""
validate_sdp.py -- consistency checks of povm_sdp.py on genuine strategies.
For a POVM strategy S = (E^0, E^1, E^2, E^3) on C^D (tau-picture, Bob transposed) build the symmetrised functional
L_sym = average of tau over the 16 d images S o g, g in <rho, sigma, rev> (realised by a direct sum of strategies,
so L_sym is again a POVM strategy on a maximally entangled state).  Then
  (a) every block evaluated directly (matrix products) equals the block built from the variables y = L_sym(reps);
  (b) all blocks are PSD (the relaxation does not cut off genuine POVM strategies);
  (c) the objective equals S = d Pi - 1 computed from the probabilities.
usage: python validate_sdp.py d D ntrials
"""
import sys
import numpy as np
from povm_sdp import build, dense_blocks, S_to_I
from povm_core import CGLMPPovm, dkz_povms, I_from_Pi


def rand_povm(d, D, rng, rank=None):
    G = rng.normal(size=(d, D, D)) + 1j * rng.normal(size=(d, D, D))
    if rank is not None:
        G[:, rank:, :] = 0
    K = np.einsum('aki,akj->ij', G.conj(), G)
    lam, U = np.linalg.eigh(K)
    S = (U * lam ** -0.5) @ U.conj().T
    return np.stack([S @ g.conj().T @ g @ S for g in G])


def images(Es, d):
    """all 16 d images rho^k sigma^s rev^r of the strategy."""
    def rho(S):
        E0 = S[0]
        E3n = np.stack([E0[(b - 1) % d] for b in range(d)])
        return [S[1], S[2], S[3], E3n]

    def sigma(S):
        return [np.stack([S[3 - g][(-b) % d] for b in range(d)]) for g in range(4)]

    def rev(S):
        return [np.transpose(E, (0, 2, 1)) for E in S]
    out = []
    base = [Es]
    base.append(sigma(Es))
    for B in list(base):
        base.append(rev(B))
    for B in base:
        cur = B
        for k in range(4 * d):
            out.append(cur)
            cur = rho(cur)
    return out


class Evaluator:
    def __init__(self, imgs, d):
        self.d = d
        w = np.exp(2j * np.pi / d)
        self.Z = []
        for S in imgs:
            Zs = {}
            for g in range(4):
                for n in range(1, d):
                    Zs[(g, n)] = np.einsum('a,aij->ij', w ** (n * np.arange(d)), S[g])
            self.Z.append(Zs)
        self.D = imgs[0][0].shape[1]
        self.cache = {}

    def word(self, w):
        if w in self.cache:
            return self.cache[w]
        tot = 0.0
        for Zs in self.Z:
            M = np.eye(self.D, dtype=complex)
            for l in w:
                M = M @ Zs[l]
            tot += np.trace(M)
        val = tot / (len(self.Z) * self.D)
        self.cache[w] = val
        return val

    def poly(self, p):
        return sum(c * self.word(w) for w, c in p.items())


def check(d, Es, st, blocks, obj, const, label):
    imgs = images(Es, d)
    ev = Evaluator(imgs, d)
    # variables from the symmetrised functional
    y = np.zeros(st.nvar)
    for v, (rep, kind, f) in enumerate(st.var_info):
        val = ev.word(rep)
        if kind == 'real':
            yv = val / f
            assert abs(yv.imag) < 1e-9 * max(1, abs(yv)), ("real var not real", rep, yv)
            y[v] = yv.real
        elif kind == 're':
            y[v] = val.real
        else:
            y[v] = val.imag
    db = dense_blocks(blocks, st.nvar)
    maxdiff, mineig = 0.0, np.inf
    # direct evaluation needs the polynomials: rebuild them from block definitions
    for (lab, H0, Hv) in db:
        H = H0 + sum(y[v] * Hm for v, Hm in Hv.items())
        e = np.linalg.eigvalsh((H + H.conj().T) / 2).min()
        mineig = min(mineig, e)
    # (a) consistency on random words: compare L(w) via moment() with direct evaluation
    rng = np.random.default_rng(0)
    letters = [(g, n) for g in range(4) for n in range(1, d)]
    for _ in range(400):
        Lw = rng.integers(1, 5)
        w = tuple(letters[i] for i in rng.integers(0, len(letters), size=Lw))
        mv = st.moment(w)
        val_var = sum(c * (1.0 if v < 0 else y[v]) for v, c in mv.items())
        val_dir = ev.word(w)
        maxdiff = max(maxdiff, abs(val_var - val_dir))
    Sobj = const + sum(c * y[v] for v, c in obj.items())
    P = CGLMPPovm(d, Es[0].shape[1])
    Pi = P.Pi_of_E(Es)
    print(f"  {label}: max |L(w) via vars - direct| = {maxdiff:.2e}   min block eigenvalue = {mineig:+.3e}   "
          f"S(vars) = {Sobj:.12f}  S(direct) = {d * Pi - 1:.12f}  I = {I_from_Pi(Pi, d):.10f}")
    return maxdiff, mineig


if __name__ == "__main__":
    d, D, ntr = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    st, blocks, obj, const = build(d)
    rng = np.random.default_rng(7)
    check(d, dkz_povms(d, 1), st, blocks, obj, const, "DKZ")
    for t in range(ntr):
        rk = None if t % 2 == 0 else 1
        Es = [rand_povm(d, D, rng, rank=rk) for _ in range(4)]
        check(d, Es, st, blocks, obj, const, f"random POVM (rank cap {rk}) #{t}")
