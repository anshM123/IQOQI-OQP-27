"""positivity margin of the core recursion: r(y) = (nu*nu)(S-y)/2 / (target(y) + (nu*nu)(y)/2), y = 1..L (needs < 1)."""
import sys, numpy as np
from lemmaM_pairing import Q_law
def run(d, eta=1e-3, iters=600):
    Q, G, kap = Q_law(d); S = d - 1; L = (S - 1) // 2
    D = Q - Q[::-1]
    # eta part only through its antisymmetric F: compute with vectorised sums
    QQ = np.outer(Q, Q); I = np.add.outer(np.arange(d), np.arange(d)) <= S - 1
    I[0, :] = False; I[:, 0] = False
    Pe = eta * QQ * I
    m_e = Pe.sum(1)
    R_e = np.array([np.trace(np.fliplr(Pe), offset=(d - 1) - y) for y in range(d)])
    F_e = m_e - R_e / 2
    target = D - (F_e - F_e[::-1])
    nu = np.zeros(d); nu[1:L + 1] = np.maximum(target[1:L + 1], 0) / 0.2
    for it in range(iters):
        N = nu.sum(); conv = np.convolve(nu, nu)
        new = np.zeros(d)
        y = np.arange(1, L + 1)
        new[1:L + 1] = (target[y] + conv[y] / 2 - conv[S - y] / 2) / N
        if np.max(np.abs(new - nu)) < 1e-17: nu = new; break
        nu = 0.5 * nu + 0.5 * new
    conv = np.convolve(nu, nu); y = np.arange(1, L + 1)
    r = (conv[S - y] / 2) / (target[y] + conv[y] / 2)
    mI = np.zeros(d); mI[1:L + 1] = nu[1:L + 1] * nu.sum()
    use = (mI + m_e)[1:S] / Q[1:S]
    return r.max(), y[np.argmax(r)], use.max(), nu[1:L + 1].min() * d ** 3, it
for d in [int(a) for a in sys.argv[1:]]:
    rmax, yat, use, numin_scaled, it = run(d)
    print(f"d={d:5d}  max_y r(y) = {rmax:.4f} (at y={yat}, L={(d-2)//2})   max core usage m_I/Q = {use:.4f}   "
          f"d^3 * min nu = {numin_scaled:.4f}   iterations {it}", flush=True)
