"""
maxent_opt.py -- lower bounds: maximise a Bell functional C[x,y,a,b] over rank-one PVM strategies on Phi_d
(p = |A_x^T B_y|^2/d) by Riemannian gradient ascent on U(d)^3 (A_0 fixed), many random starts.
Also returns the optimal unitaries and the tracial moment data (R_g) of the optimum.
"""
import numpy as np
from core import haar


def probs(U, d):
    p = np.zeros((2, 2, d, d))
    M = [[None, None], [None, None]]
    for x in range(2):
        for y in range(2):
            M[x][y] = U[x].T @ U[2 + y]
            p[x, y] = np.abs(M[x][y]) ** 2 / d
    return p, M


def grads(U, d, G):
    _, M = probs(U, d)
    gA2 = np.zeros((d, d), complex)
    for y in range(2):
        gA2 += np.conj(U[2 + y]) @ (G[1, y] * M[1][y]).T / d
    gB = []
    for y in range(2):
        g = np.zeros((d, d), complex)
        for x in range(2):
            g += np.conj(U[x]) @ (G[x, y] * M[x][y]) / d
        gB.append(g)
    return [gA2, gB[0], gB[1]]


def expm_skew(Om):
    w, V = np.linalg.eigh(1j * Om)
    return (V * np.exp(-1j * w)) @ V.conj().T


def ascend(C, U, d, maxit=600):
    f = float(np.sum(C * probs(U, d)[0]))
    eta = 0.3
    for it in range(maxit):
        g = grads(U, d, C)
        dirs = [U[k].conj().T @ gk - gk.conj().T @ U[k] for k, gk in zip((1, 2, 3), g)]
        nrm = np.sqrt(sum(np.sum(np.abs(O) ** 2) for O in dirs)) + 1e-300
        if nrm < 1e-13:
            break
        ok = False
        while eta > 1e-12:
            U2 = list(U)
            for k, Om in zip((1, 2, 3), dirs):
                U2[k] = U[k] @ expm_skew(eta * Om / nrm)
            f2 = float(np.sum(C * probs(U2, d)[0]))
            if f2 > f + 1e-15:
                U, f, eta, ok = U2, f2, min(eta * 1.5, 1.0), True
                break
            eta *= 0.4
        if not ok:
            break
    return f, U


def maximise(C, d, nstart=30, seed=0):
    C = np.asarray(C, dtype=float)
    rng = np.random.default_rng(seed)
    best = (-np.inf, None)
    for s in range(nstart):
        U = [np.eye(d, dtype=complex), haar(d, rng), haar(d, rng), haar(d, rng)]
        f, U = ascend(C, U, d)
        if f > best[0]:
            best = (f, U)
    return best


def tracial_unitaries(U, d):
    """R_g for the tracial model: P^x_a = (|alpha><alpha|)^T, Q^y_b = |beta><beta| (columns of U)."""
    w = np.exp(2j * np.pi / d)
    R = []
    for x in range(2):
        M = np.zeros((d, d), complex)
        for a in range(d):
            v = U[x][:, a]
            M += w ** a * np.outer(v, v.conj()).T
        R.append(M)
    for y in range(2):
        M = np.zeros((d, d), complex)
        for b in range(d):
            v = U[2 + y][:, b]
            M += w ** b * np.outer(v, v.conj())
        R.append(M)
    return R
