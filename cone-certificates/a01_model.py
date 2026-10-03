"""a01: high-precision (non-rigorous) prototype of the SCALED model used in CONE_ALLD_PROOF.md.
Phi(b) = eps b^2 u(b),  sum_{j=1}^J Ch_j(b) u^j = tauh(b),
  Ch_j  = [2 eps^(j-1) b^(2j-1) (kappa_2j(b) - kappa_2j(d-b)) + (pi/2) eps^j b^(2j-1) (Fr^(2j)(b) - Fr^(2j)(d-b))] / (2^j j!),
  tauh  = (pi/2) tau(b)/b,  tau = Dlt(b) - Dlt(d-b),  Dlt = P_{v,r} - F_r  (discrete potential, as in verify_gauss.py).
Checks the root against the certified Phi_* midpoints (logs/phi_d{d}.json) and prints the inner coefficients."""
import sys, json
import mpmath as mpm
from mpmath import mp, mpf, pi, psi
mp.dps = 50
d = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
J = 7
eps = mpf(1) / d
NSER = 90
g = {1: -(4 / pi) * (1 + mpm.log(4 / pi))}
for n in range(1, NSER + 1):
    g[2 * n + 1] = (8 / pi ** 2) * abs(mpm.bernoulli(2 * n)) / (2 * n * mpm.factorial(2 * n + 1)) * pi ** (2 * n + 1) * (mpf(1) / 2 - mpf(4) ** (-n))
IMAX = 2 * NSER + 1


def kap(n, b):
    b = mpf(b)
    return n * psi(n - 1, b + 1) + b * psi(n, b + 1)


def Fr_derivs(b, nmax):
    """[F_r^(k)(b) for k = 0..nmax] via d^2 sum g_i (b)_i/(d)_i with the b-jet of (b)_i."""
    b = mpf(b)
    jet = [mpf(1)] + [mpf(0)] * nmax      # Taylor coefficients of (b+h)_i in h
    den = mpf(1)
    out = [mpf(0)] * (nmax + 1)
    for i in range(1, IMAX + 1):
        c = b + i - 1
        jet = [c * jet[k] + (jet[k - 1] if k else 0) for k in range(nmax + 1)]
        den *= (d + i - 1)
        if i % 2 == 1:
            for k in range(nmax + 1):
                out[k] += g[i] * jet[k] / den * mpm.factorial(k)
    return [d * d * x for x in out]


def gr(x):
    return sum(g[i] * x ** i for i in g)


def gr2(x):
    return 2 / mpm.sin(pi * x / 2) - (4 / pi) / x


# discrete potential P_{v,r} and Dlt at integers
f = [None] + [gr2(mpf(j) / d) for j in range(1, d)]
Pd = d * d * gr(mpf(1))
pre1 = [mpf(0)]
for j in range(1, d):
    pre1.append(pre1[-1] + j * f[j])
suf2 = [mpf(0)] * (d + 1)
for j in range(d - 1, 0, -1):
    suf2[j] = suf2[j + 1] + (d - j) * f[j]
Pvr = [mpf(0)] * (d + 1); Pvr[d] = Pd
for m in range(1, d):
    Pvr[m] = mpf(m) / d * Pd - (mpf(d - m) / d * pre1[m] + mpf(m) / d * suf2[m + 1])
FR = {}


def frd(b):
    if b not in FR:
        FR[b] = Fr_derivs(b, 2 * J)
    return FR[b]


def Dlt(m):
    if m == 0 or m == d:
        return mpf(0)
    return Pvr[m] - frd(m)[0]


def model_u(m):
    b = mpf(m)
    Ch = []
    for j in range(1, J + 1):
        sing = 2 * eps ** (j - 1) * b ** (2 * j - 1) * (kap(2 * j, b) - kap(2 * j, d - b))
        reg = (pi / 2) * eps ** j * b ** (2 * j - 1) * (frd(m)[2 * j] - frd(d - m)[2 * j])
        Ch.append((sing + reg) / (2 ** j * mpm.factorial(j)))
    tau = Dlt(m) - Dlt(d - m)
    th = (pi / 2) * tau / b
    u = th / Ch[0]
    for it in range(30):
        P = sum(Ch[j] * u ** (j + 1) for j in range(J)) - th
        dP = sum((j + 1) * Ch[j] * u ** j for j in range(J))
        u -= P / dP
    return u, Ch, th


if __name__ == '__main__':
    ref = json.load(open(f'logs/phi_d{d}.json'))['Phi']
    A0 = pi / 2 - 1
    for m in [1, 2, 3, 5, 10, 50, d // 4, d // 2 - 1]:
        u, Ch, th = model_u(m)
        Phi = eps * m * m * u
        B = m * kap(2, m)
        print(f"m={m}: Phi model {mpm.nstr(Phi, 20)}  cert-mid {ref[m][:22]}  rel diff {mpm.nstr((Phi - mpf(ref[m])) / Phi, 3)}"
              f" | u={mpm.nstr(u, 12)} A0/B={mpm.nstr(A0 / B, 12)} Ch1={mpm.nstr(Ch[0], 10)} B={mpm.nstr(B, 10)} tauh={mpm.nstr(th, 10)}")
