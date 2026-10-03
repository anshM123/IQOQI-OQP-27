"""white_mixture.py -- exploration for ledger B1 (float, not a proof): block-diagonal strategies on Phi_D.

A block-diagonal PVM strategy on Phi_D = (+)_k Phi_{D_k} (weights w_k = D_k/D) has behaviour p = sum w_k p_k and
white-noise term n = pbar_A (x) pbar_B (pbar = sum w_k p_{k,A}), so
    F(w) = v* sum_k w_k I(p_k) + (1 - v*) sum_{k,l} w_k w_l I(p_{k,A} (x) p_{l,B}),     v* = 2/I_ME(d).
B1 holds for such strategies iff F <= 2.  Candidate blocks: all deterministic strategies, DKZ, and the optimal
qubit-pattern strategies (each measurement deterministic or a rank-one pair of outcomes, planar Bloch vectors).
We maximise F over pairs (exact quadratic in one variable) and by projected gradient over the simplex.
"""
import itertools
import sys

import numpy as np

sys.path.insert(0, ".")
from facets223 import cglmp_beta  # noqa: E402
from white_qubit_scan import beta_np, i_me  # noqa: E402


def dkz_p(d):
    delta = {(0, 0): 0.25, (0, 1): -0.25, (1, 0): 0.75, (1, 1): 0.25}
    p = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            for a in range(d):
                for b in range(d):
                    p[x, y, a, b] = 1 / (2 * d ** 3 * np.sin(np.pi * (b - a - delta[(x, y)]) / d) ** 2)
    return p


def det_p(s, d):
    p = np.zeros((2, 2, d, d))
    for x in range(2):
        for y in range(2):
            p[x, y, s[x], s[2 + y]] = 1
    return p


def qubit_blocks(d, beta):
    """optimal qubit strategies for every pattern whose restricted CGLMP has I_max > 2 (nonlocal blocks)."""
    meas = [("det", a) for a in range(d)] + [("pair", s, t) for s in range(d) for t in range(s + 1, d)]
    out = []
    ph = np.linspace(0, 2 * np.pi, 2001)
    for M in itertools.product(meas, repeat=4):
        if all(m[0] == "det" for m in M):
            continue
        marg, e = [], []
        for m in M:
            v = np.zeros(d)
            w = np.zeros(d)
            if m[0] == "det":
                v[m[1]] = 1
            else:
                v[m[1]] = v[m[2]] = 0.5
                w[m[1]], w[m[2]] = 1, -1
            marg.append(v)
            e.append(w)
        c = np.array([[0.25 * np.sum(beta[x, y] * np.outer(e[x], e[2 + y])) for y in range(2)] for x in range(2)])
        In = sum(np.sum(beta[x, y] * np.outer(marg[x], marg[2 + y])) for x in range(2) for y in range(2))
        val = np.abs(c[0, 0] + c[0, 1] * np.exp(-1j * ph)) + np.abs(c[1, 0] + c[1, 1] * np.exp(-1j * ph))
        k = int(np.argmax(val))
        if In + val[k] <= 2 + 1e-9:
            continue
        phi = [0.0, ph[k]]
        th = [np.angle(c[x, 0] + c[x, 1] * np.exp(-1j * ph[k])) for x in range(2)]
        p = np.zeros((2, 2, d, d))
        for x in range(2):
            for y in range(2):
                E = np.cos(th[x] - phi[y])
                p[x, y] = np.outer(marg[x], marg[2 + y]) + 0.25 * np.outer(e[x], e[2 + y]) * E
        assert p.min() > -1e-12
        out.append(p)
    return out


def run(d):
    beta = beta_np(d)
    vs = 2 / i_me(d)
    I = lambda p: float(np.sum(beta * p))
    blocks = [dkz_p(d)] + [det_p(s, d) for s in itertools.product(range(d), repeat=4)]
    blocks += qubit_blocks(d, beta)
    K = len(blocks)
    Ik = np.array([I(p) for p in blocks])
    PA = np.array([[p[x, 0].sum(axis=1) for x in range(2)] for p in blocks])      # K x 2 x d
    PB = np.array([[p[0, y].sum(axis=0) for y in range(2)] for p in blocks])
    M = np.einsum("xyab,kxa,lyb->kl", beta, PA, PB)
    print(f"d={d}: {K} blocks (1 DKZ, {d ** 4} deterministic, {K - 1 - d ** 4} nonlocal qubit blocks); "
          f"v* = {vs:.8f}", flush=True)
    # pairs
    best = (-np.inf, None)
    for k in range(K):
        for l in range(k, K):
            # F((1-s) e_k + s e_l) quadratic in s
            a0 = vs * Ik[k] + (1 - vs) * M[k, k]
            Mkl = M[k, l] + M[l, k]
            # F(s) = vs((1-s)Ik + s Il) + (1-vs)((1-s)^2 Mkk + s(1-s) Mkl + s^2 Mll)
            c2 = (1 - vs) * (M[k, k] - Mkl + M[l, l])
            c1 = vs * (Ik[l] - Ik[k]) + (1 - vs) * (-2 * M[k, k] + Mkl)
            cands = [0.0, 1.0]
            if c2 < 0:
                cands.append(min(max(-c1 / (2 * c2), 0.0), 1.0))
            for s in cands:
                F = a0 + c1 * s + c2 * s * s
                if F > best[0] + 1e-12:
                    best = (F, (k, l, s))
    print(f"   best pair mixture: F = {best[0]:.10f} at {best[1]}", flush=True)
    # projected gradient ascent on the simplex from random starts (support up to 4 blocks)
    rng = np.random.default_rng(1)
    bestF = best[0]
    for trial in range(300):
        idx = rng.choice(K, size=4, replace=False)
        if trial % 3 == 0:
            idx[0] = 0
        w = rng.dirichlet(np.ones(4))
        for it in range(400):
            Ms = M[np.ix_(idx, idx)]
            g = vs * Ik[idx] + (1 - vs) * (Ms + Ms.T) @ w
            w = w + 0.05 * (g - g.mean())
            w = np.maximum(w, 0)
            w = w / w.sum()
        F = vs * Ik[idx] @ w + (1 - vs) * w @ M[np.ix_(idx, idx)] @ w
        if F > bestF + 1e-10:
            bestF = F
            print(f"   simplex search: F = {F:.10f} blocks {idx.tolist()} weights {np.round(w, 4).tolist()}",
                  flush=True)
    print(f"d={d}: max F found = {bestF:.10f} (B1 needs <= 2)", flush=True)


if __name__ == "__main__":
    for d in [int(t) for t in sys.argv[1:]] or [3, 4]:
        run(d)
