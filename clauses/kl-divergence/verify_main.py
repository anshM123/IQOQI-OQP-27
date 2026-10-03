"""
verify_main.py -- independent re-check of THEOREM 1 (KL clause fails for every d >= 4) from the stored exact
certificate data only (no solver is called):
   zmodel_cert_A10.json     exact rational local model on Z (Lemma Z)
   blocks_testfactors.json  exact rational test factors for the blocks T1, C2, K3, CC4 (Lemma F)
Arithmetic: Fractions for every exact statement (normalisation, feasibility, cross conditions, tail inequality);
mpmath interval arithmetic (60 digits) for the logarithmic sums.  Code written independently of zcert.py /
blocks_cert.py (different enumeration order and summation; rational lower bound for pi^2 in the tail test).
Also prints float sanity checks of the analytic identities (DKZ closed form from the bases; wrap identity).
usage: python verify_main.py
"""
import itertools
import json
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf

iv.dps = 60
LN2 = iv.log(iv.mpf(2))


def I(x):
    x = Fr(x)
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)


# ------------------------------------------------------------------ Lemma Z: the Z-model
Z = json.load(open("zmodel_cert_A10.json"))
A, B = Z["A"], Z["B"]
t = Fr(Z["t"])
mu = [Fr(x) for x in Z["mu"]]
K0 = [[Fr(x) for x in row] for row in Z["K0"]]
K1 = [[Fr(x) for x in row] for row in Z["K1"]]
assert len(mu) == 2 * A + 1 and all(len(r) == 2 * B + 1 for r in K0 + K1)
assert t > 0 and all(x >= 0 for x in mu) and all(x >= 0 for r in K0 + K1 for x in r)
assert all(sum(r) == 1 for r in K0 + K1)
# exact telescoping: sum_{a > A} 1/(a^2 - 1/4) = sum (1/(a-1/2) - 1/(a+1/2)) = 1/(A + 1/2)
tail_mass = 2 * t * Fr(2, 2 * A + 1)
assert sum(mu) + tail_mass == 1, "total mass must be exactly 1"
print("[Z] exact model: nonnegative, kernels normalised, total mass = 1 exactly")

delta = {"00": Fr(1, 4), "01": Fr(3, 4), "10": Fr(-1, 4), "11": Fr(1, 4)}
KW = A + B


def link_value(link, a, b0, b1):
    return {"00": b0, "10": b0 - a, "01": b1, "11": b1 - a}[link]


# P[link][m] for |m| <= KW, by enumerating all window cells (a, b0, b1) -- product form mu K0 K1
P = {L: {m: Fr(0) for m in range(-KW, KW + 1)} for L in delta}
for ia, a in enumerate(range(-A, A + 1)):
    # links 00, 10 only depend on (a, b0); 01, 11 only on (a, b1)  (marginalise the other kernel: sums to 1)
    for ib, b in enumerate(range(-B, B + 1)):
        w0 = mu[ia] * K0[ia][ib]
        w1 = mu[ia] * K1[ia][ib]
        P["00"][b] += w0
        P["10"][b - a] += w0
        P["01"][b] += w1
        P["11"][b - a] += w1


def tail_far(link, m):
    """tail cells |a| > A: b0 in {0,a}, b1 in {1,a} w.p. 1/2; contribution to P_link(m) from the 'far' choice"""
    a = {"00": m, "10": -m, "01": m, "11": 1 - m}[link]
    return t / (2 * (Fr(a) ** 2 - Fr(1, 4))) if abs(a) > A else Fr(0)


near_val = {"00": 0, "10": 0, "01": 1, "11": 0}
for L in delta:
    for m in range(-KW, KW + 1):
        P[L][m] += tail_far(L, m)
    P[L][near_val[L]] += tail_mass / 2
# exact check: window link laws + far tails beyond KW sum to 1 (far tail beyond KW computed by telescoping)
for L in delta:
    s = sum(P[L].values())
    # far contributions for |m| > KW: a ranges over |a| > KW (or a = 1-m, |m| > KW <=> a <= -KW or a >= KW+2)
    if L in ("00", "01", "10"):
        rest = 2 * (t / 2) * Fr(2, 2 * KW + 1)
    else:
        # a = 1 - m with m > KW -> a <= -KW: sum_{a<=-KW} = 1/(KW - 1/2); m < -KW -> a >= KW + 2: 1/(KW + 3/2)
        rest = (t / 2) * (Fr(2, 2 * KW - 1) + Fr(2, 2 * KW + 3))
    assert s + rest == 1, (L, s + rest)
print("[Z] link laws: exact, each sums to 1 over Z (window part + telescoped far tail)")

M = 3000
PI2 = iv.pi ** 2
T = iv.mpf(0)
for L, dl in delta.items():
    acc = iv.mpf(0)
    for m in range(M, -M - 1, -1):          # reverse order (independent summation)
        Pm = P[L][m] if abs(m) <= KW else tail_far(L, m)
        assert Pm > 0
        Qm = 1 / (2 * PI2 * (I(m) - I(dl)) ** 2)
        acc += Qm * (iv.log(Qm) - iv.log(I(Pm)))
    T += acc / 4
# tail |m| > M: show P >= Q, i.e. t pi^2 (m - delta)^2 >= m'^2 - 1/4 with m' in {m, -m, 1-m}:
# sufficient: h(n) = t*pi2lo*(n - 3/4)^2 - (n + 1)^2 >= 0 for all integers n >= M+1
pi2lo = Fr(986960, 100000)                 # pi^2 = 9.8696044... > 9.8696
assert I(pi2lo) < PI2
c = t * pi2lo
assert c > 1
# h is a quadratic with leading coeff c - 1 > 0, vertex at n* = (3c/4 + 1)/(c - 1); check n* <= M+1 and h(M+1) >= 0
nstar = (Fr(3, 4) * c + 1) / (c - 1)
n = M + 1
assert nstar <= n and c * (n - Fr(3, 4)) ** 2 - (n + 1) ** 2 >= 0
Tbits = T / LN2
print(f"[Z] T_inf <= {float(mpf(Tbits.b)):.12f} bits (sum over |m| <= {M}; tail |m| > {M} has P >= Q, contributes <= 0)")
T_up = Tbits.b

# ------------------------------------------------------------------ Lemma F: blocks
S2 = iv.sqrt(iv.mpf(2))


def qblock(name, x, y, a, b):
    if name == "T1":
        return iv.mpf(1)
    if name == "C2":
        return (1 + (-1) ** ((a + b + x * y) % 2) / S2) / 4
    if name == "K3":
        dl = {(0, 0): Fr(1, 4), (0, 1): Fr(3, 4), (1, 0): Fr(-1, 4), (1, 1): Fr(1, 4)}[(x, y)]
        s = iv.sin(iv.pi * (I(b - a) - I(dl)) / 3)
        return 1 / (54 * s ** 2)
    if name == "CC4":
        return qblock("C2", x, y, a >> 1, b >> 1) * qblock("C2", x, y, a & 1, b & 1)


TF = json.load(open("blocks_testfactors.json"))
Lb, Rmax = {}, {}
for name, dat in TF.items():
    m = dat["m"]
    r = {tuple(map(int, k.split(","))): Fr(v) for k, v in dat["r"].items()}
    assert set(r) == set(itertools.product(range(2), range(2), range(m), range(m)))
    assert all(v > 0 for v in r.values())
    worst = Fr(0)
    for a0, a1, b0, b1 in itertools.product(range(m), repeat=4):
        s = (r[(0, 0, a0, b0)] + r[(0, 1, a0, b1)] + r[(1, 0, a1, b0)] + r[(1, 1, a1, b1)]) / 4
        worst = max(worst, s)
    assert worst <= 1
    # normalisation of q (sanity) and the certified value
    Lv = iv.mpf(0)
    for (x, y, a, b), v in r.items():
        Lv += qblock(name, x, y, a, b) * iv.log(I(v)) / 4
    tot = [sum(qblock(name, x, y, a, b) for a in range(m) for b in range(m)) for x in range(2) for y in range(2)]
    assert all(abs(float(mpf(s.mid)) - 1) < 1e-40 for s in tot)
    Lb[name] = Lv / LN2
    Rmax[name] = {(x, y): max(r[(x, y, a, b)] for a in range(m) for b in range(m)) for x in range(2) for y in range(2)}
    print(f"[F] {name}: test factor feasible (exact max over {m**4} strategies = {float(worst):.12f}); "
          f"L >= {float(mpf(Lb[name].a)):.12f} bits")
for j, k in itertools.product(TF, repeat=2):
    assert Rmax[j][(0, 0)] + Rmax[k][(1, 1)] <= 4 and Rmax[j][(0, 1)] + Rmax[k][(1, 0)] <= 4
print("[F] cross conditions hold for all ordered pairs of block types (exact)")
L4 = Lb["CC4"]
Lr = {1: Lb["T1"], 2: Lb["C2"], 3: Lb["K3"]}
assert all(Lr[k].b < L4.a for k in Lr)
Cmin = min([L4.a] + [((4 * L4 + k * Lr[k]) / (4 + k)).a for k in Lr])
print(f"[F] competitor lower bound for every d >= 4: C(d) >= {float(mpf(Cmin)):.12f} bits (min at d = 5)")
print(f"THEOREM 1 margin: C_min - T_inf >= {float(mpf(Cmin - T_up)):.9f} bits > 0: {Cmin > T_up}")

# ------------------------------------------------------------------ float sanity checks of analytic identities
for d in (3, 4, 7, 10):
    k = np.arange(d)
    al, be = (0.5, 0.0), (0.25, -0.25)
    for x in range(2):
        for y in range(2):
            Ax = np.array([np.exp(2j * np.pi * k * (a + al[x]) / d) for a in range(d)]).T / np.sqrt(d)
            By = np.array([np.exp(-2j * np.pi * k * (b + be[y]) / d) for b in range(d)]).T / np.sqrt(d)
            amp = Ax.conj().T @ (np.eye(d) / np.sqrt(d)) @ By.conj()
            q = np.abs(amp) ** 2
            dl = al[x] - be[y]
            closed = np.array([[1 / (2 * d ** 3 * np.sin(np.pi * (b - a - dl) / d) ** 2) for b in range(d)]
                               for a in range(d)])
            N = 20000   # truncated wrap sum + integral estimate of the remainder (2 / (2 pi^2 N d^2))
            wrap = np.array([[(sum(1 / (2 * np.pi ** 2 * (b - a - dl + n * d) ** 2) for n in range(-N, N + 1))
                               + 1 / (np.pi ** 2 * (N + 0.5) * d ** 2)) / d
                              for b in range(d)] for a in range(d)])
            e1, e2 = np.abs(q - closed).max(), np.abs(q - wrap).max()
            assert e1 < 1e-14 and e2 < 1e-10, (d, x, y, e1, e2)
print("[sanity] DKZ closed form and wrap identity confirmed in floats for d = 3, 4, 7, 10")
