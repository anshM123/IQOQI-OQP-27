"""lemma_sanity.py -- float sanity check (NOT part of the proof) of every explicit bound used in the large-n proof
(PROOF_PHI.md, Lemmas C, Phi, D, E, F and the region-B envelopes), at a few large n.  Any violation = algebra slip."""
import sys
import numpy as np
import mpmath

mpmath.mp.dps = 30
Cat = float(mpmath.catalan); PHI1 = float(mpmath.pi / 16 + mpmath.pi ** 2 / 32 - mpmath.catalan / 2)
KINF = 16 * Cat / np.pi ** 2; CINF = 8 / (np.pi ** 2 * (2 - KINF)); k = 1 / 50


def f_c(x):
    x = np.asarray(x, float)
    return np.where(x <= 0.25, 4 * np.log(2) - 8 * x, 4 * (2 * x - 1 - np.log(np.maximum(2 * x, 1e-300))))


def wc(x):
    return np.maximum(0, 1 - 4 * x)


def g_c(x):
    return f_c(x) - 2 * wc(x)


def run(n):
    S = n - 1; L = (S - 1) // 2
    j = np.arange(n)
    z = 4 * j + 1; z = np.where(z > 2 * n, 4 * n - z, z)          # reflect: avoid sin near pi
    G = 1.0 / (2.0 * n * n * np.sin(np.pi * z / (4 * n)) ** 2)
    kap = 2 - 4 * (j @ G) / S; cn = 8 / (np.pi ** 2 * (2 - kap))
    phi = G / (2 - kap)
    ys = np.arange(1, L + 1)
    D = phi[ys] - phi[S - ys]
    phit = 8 * (2 * ys + 1) / ((4.0 * ys + 1) ** 2 * (4.0 * ys + 3) ** 2)
    yy = np.arange(0, L + 2)
    rho = np.zeros(L + 2)
    rho[1:] = k * np.minimum(1, yy[1:] / 3) * np.maximum(0, 1 - (2 * yy[1:] + 1) / L) / (yy[1:] * (yy[1:] + 1.0))
    AF = 3 * rho[ys] + rho[ys - 1] - rho[ys // 2]
    sv = np.arange(L + 1, S); R3c = np.cumsum(1.0 / sv.astype(float) ** 3)
    R3 = lambda m: R3c[m - (L + 1)]
    St = S - ys
    E1 = R3(St) + (St - 1) / (2.0 * St.astype(float) ** 3)
    a = (ys * (D - AF)).sum() / (ys * E1).sum()
    Deff = D - AF - a * E1
    U = np.cumsum(ys * Deff)
    F = np.cumsum(ys * AF)
    MD = np.cumsum(ys * D); ME = np.cumsum(ys * E1)
    x = ys / S
    bad = []
    def chk(name, cond):
        if not np.all(cond): bad.append((name, int(np.argmin(cond)) + 1))
    chk('C', [CINF * (1 - 0.2946 / S) <= cn <= CINF])
    chk('D(a) low', D >= cn * (phit - 0.6 / S ** 3) - 1e-12 * phit)
    chk('D(a) up', D <= cn * (phit + 0.08 / S ** 3) + 1e-12 * phit)
    chk('D>0', D > 0)
    tail = PHI1 - np.cumsum(ys * phit)
    chk('MD low', MD >= cn * (PHI1 - tail * 0 - np.minimum(1 / (16 * ys), 1) - 0.08 / S) - 1e-15)
    chk('MD up', MD <= cn * (PHI1 + 0.01 / S) + 1e-15)
    chk('E1', (E1 >= 1 / (2 * (L + 1.0) ** 2) - 1e-20) & (E1 <= 1 / (2.0 * L ** 2) + 1e-20))
    chk('a', [4 * cn * PHI1 * (1 - 9 / S) <= a <= 4 * cn * PHI1 * (1 + 3 / S)])
    m8 = ys >= 8
    chk('F(a)', (F <= k * (f_c(x) + 12 / ys) + 1e-15)[m8])
    chk('F(b)', ((4 / 3) * F >= k * ((4 / 3) * f_c(x) - 13 / ys - 23 / S) - 1e-15)[m8])
    # envelopes: lower and upper capacity in region B (y >= 201) in the normalised form used for the 1D check
    T = 2 * U / (ys * (ys + 1.0))
    ZL = R3c[-1]
    mL = (2 / 3) * T + 2 * rho[ys] + (2 / 3) * rho[ys - 1] + (a / 3) * (2 * ZL + (S - 1 - ys) / (S - ys.astype(float)) ** 3)
    W = ZL - R3(S - ys)
    Q = np.zeros(L); Q[1:] = 4 * U[:-1] - 2 * ys[1:] * (ys[1:] - 1.0) * Deff[1:]
    mU = Q / (3 * ys * (ys + 1.0)) + (2 / 3) * rho[ys // 2] + (2 / 3) * a * W
    H = (4 / 3) * PHI1 * (1 + (1 + 3 / S) * x ** 2 * ((1 - x) ** -2 - 1)) - (4 / 3) * (k / CINF) * g_c(x)
    envL = cn * H + k * (13 / ys + 0.67 / np.maximum(ys - 1, 1)) + 1.0 / S
    envU = cn * H + k * 24.4 / np.maximum(ys - 1, 1) + 1.2 / S
    B = ys >= 201
    chk('envL', (ys ** 2 * mL <= envL + 3e-5 * 0 + 1e-12)[B])
    chk('envU', (ys[1:] ** 2 * mU[1:] <= envU[1:] + 1e-12)[B[1:]])
    xt = ys / (S + 1.0)
    capL = (cn / 16) * (1 - 1 / (2 * ys)) * (np.pi * xt) ** 2 / np.sin(np.pi * xt) ** 2
    capU = (cn / 16) * (1 - 3 / (2 * ys)) * (np.pi * xt) ** 2 / np.sin(np.pi * xt) ** 2
    chk('capL', ys ** 2 * phi[ys] >= capL * (1 - 1e-12))
    chk('capU', ys ** 2 * phi[S - ys] >= capU * (1 - 1e-12))
    # positivity envelopes
    Ulow = cn * PHI1 * (1 - 4 * x ** 2 * (1 + 1 / ys) * (1 + 7.1 / S)) - k * f_c(x) - (cn / 16 + 12 * k) / ys - 0.08 * cn / S
    chk('Ulow', (U >= Ulow - 1e-15)[B & (x <= 0.3)])
    print(f"n={n}: kappa_n={kap:.10f} c_n/c_oo-1={cn/CINF-1:+.3e} a/(4 c Phi1)-1={a/(4*cn*PHI1)-1:+.3e} "
          f"max y^2 mL/envL={np.max((ys**2*mL/envL)[B]):.5f} max y^2 mU/envU={np.max((ys[1:]**2*mU[1:]/envU[1:])[B[1:]]):.5f} "
          f"violations: {bad if bad else 'none'}", flush=True)


if __name__ == '__main__':
    for n in [int(t) for t in sys.argv[1].split(',')]:
        run(n)
