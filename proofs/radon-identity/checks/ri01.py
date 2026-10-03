# Radon identity (RI):  (1/2pi) int_0^1 sum_i |Im eig((P - tau)^{-1} H)| dtau  =  Tr H_+ - Tr (H_d)_+ ,  H_d = BHB + PHP
import numpy as np
from scipy.integrate import quad
rng = np.random.default_rng(3)
def lhs(H, P):
    M = H.shape[0]; B = np.eye(M) - P
    def f(th):   # tau = sin^2 th
        tau = np.sin(th)**2
        A = (P/(1-tau) - B/tau) @ H
        ev = np.linalg.eigvals(A)
        return np.sum(np.abs(ev.imag))*np.sin(2*th)
    v, err = quad(f, 0, np.pi/2, limit=400, epsabs=1e-12, epsrel=1e-12)
    return v/(2*np.pi)
def rhs(H, P):
    M = H.shape[0]; B = np.eye(M) - P
    Hd = B@H@B + P@H@P
    pos = lambda X: np.sum(np.maximum(np.linalg.eigvalsh(X), 0))
    return pos(H) - pos(Hd)
for t in range(8):
    M = int(rng.integers(2, 6)); r = int(rng.integers(1, M))
    U = np.linalg.qr(rng.normal(size=(M,M)) + 1j*rng.normal(size=(M,M)))[0]
    P = U[:, r:]@U[:, r:].conj().T
    H = rng.normal(size=(M,M)) + 1j*rng.normal(size=(M,M)); H = (H + H.conj().T)/2*[1,4][t%2]
    a, b = lhs(H, P), rhs(H, P)
    print(f'M={M} r={r}: LHS={a:.10f} RHS={b:.10f} diff={a-b:.2e}')
