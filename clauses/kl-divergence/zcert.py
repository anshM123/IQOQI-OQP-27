"""
zcert.py -- RIGOROUS d-independent upper bound on the KL strength of DKZ_d (Lemma W + Lemma Z of THEOREM.md).

Input: a numerical Z-model (zmodel2.py output, window |a| <= A, |b| <= B).  It is converted to an EXACT rational
local model on Z:
   a = a1 - a0 has law mu (rational on the window; tail mu(a) = t/(a^2 - 1/4) for |a| > A, t rational),
   given a in the window: b0 ~ K0(.|a), b1 ~ K1(.|a) (rational probability vectors, exact sums = 1),
   given |a| > A:          b0 in {0, a}, b1 in {1, a}, each w.p. 1/2.
Total mass = sum_window mu + 4t/(2A+1) = 1 EXACTLY (telescoping: sum_{a>A} 1/(a^2-1/4) = 1/(A+1/2)).
Link laws (exact rationals for every integer m):
   P00(m) = Pr[b0 = m], P10(m) = Pr[b0 - a = m], P01(m) = Pr[b1 = m], P11(m) = Pr[b1 - a = m].
Target: Q_xy(m) = 1/(2 pi^2 (m - delta_xy)^2), delta = (00: 1/4, 01: 3/4, 10: -1/4, 11: 1/4).
Bound:  T = (1/4) sum_xy sum_{m in Z} Q log(Q/P)
        = (1/4) sum_xy [ sum_{|m| <= M} (interval arithmetic) + R_xy ],
R_xy = sum_{|m| > M} Q log(Q/P) <= 0, proved by checking  P(m) >= Q(m) for |m| > M via
   P_xy(m) = t/(2(m'^2 - 1/4)) with m' in {m, -m, 1-m}, and (|m|+1)^2 <= t pi^2 (|m| - 3/4)^2 for |m| > M.
Output: certified T (upper endpoint), in bits.  Also writes the exact model to zmodel_cert_A{A}.json.
usage: python zcert.py zsol2_A10.npz [M]
"""
import sys
import json
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv, mpf

iv.dps = 40
DELTA = {(0, 0): Fr(1, 4), (0, 1): Fr(3, 4), (1, 0): Fr(-1, 4), (1, 1): Fr(1, 4)}
NEAR = {(0, 0): 0, (1, 0): 0, (0, 1): 1, (1, 1): 0}


def mprime(m, xy):
    return {(0, 0): m, (0, 1): m, (1, 0): -m, (1, 1): 1 - m}[xy]


def rational_model(fn, den=10 ** 12):
    Z = np.load(fn)
    p0, p1, t, A, B = Z["p0"], Z["p1"], float(Z["t"]), int(Z["A"]), int(Z["B"])
    av = list(range(-A, A + 1))
    bv = list(range(-B, B + 1))
    tq = Fr(t).limit_denominator(den)
    tailmass = 4 * tq / (2 * A + 1)
    assert 0 < tailmass < 1
    mu_f = 0.5 * (np.clip(p0, 0, None).sum(1) + np.clip(p1, 0, None).sum(1))
    mu = [Fr(float(x)).limit_denominator(den) for x in mu_f]
    s = sum(mu)
    mu = [x * (1 - tailmass) / s for x in mu]                 # exact normalisation
    K = []
    for p in (p0, p1):
        Kp = []
        for i in range(len(av)):
            row = np.clip(p[i], 0, None)
            row = row / row.sum()
            rq = [Fr(float(x)).limit_denominator(den) for x in row]
            sr = sum(rq)
            Kp.append([x / sr for x in rq])
        K.append(Kp)
    assert all(x >= 0 for x in mu) and all(x >= 0 for Kp in K for row in Kp for x in row)
    assert sum(mu) + tailmass == 1
    assert all(sum(row) == 1 for Kp in K for row in Kp)
    return dict(A=A, B=B, av=av, bv=bv, t=tq, mu=mu, K0=K[0], K1=K[1])


def link_law_window(model):
    """exact rational P_xy(m) for |m| <= A + B (window part + tail atoms + tail far part)."""
    A, B, av, bv, t, mu = model["A"], model["B"], model["av"], model["bv"], model["t"], model["mu"]
    Kw = A + B
    P = {xy: {m: Fr(0) for m in range(-Kw, Kw + 1)} for xy in DELTA}
    for i, a in enumerate(av):
        for j, b in enumerate(bv):
            w0 = mu[i] * model["K0"][i][j]
            w1 = mu[i] * model["K1"][i][j]
            if w0:
                P[(0, 0)][b] += w0
                P[(1, 0)][b - a] += w0
            if w1:
                P[(0, 1)][b] += w1
                P[(1, 1)][b - a] += w1
    atom = 2 * t / (2 * A + 1)            # half of the tail mass
    for xy in DELTA:
        P[xy][NEAR[xy]] += atom
        for m in range(-Kw, Kw + 1):
            mp_ = mprime(m, xy)
            if abs(mp_) > A:
                P[xy][m] += t / (2 * (Fr(mp_) ** 2 - Fr(1, 4)))
    return P


def P_far(model, m, xy):
    mp_ = mprime(m, xy)
    assert abs(mp_) > model["A"]
    return model["t"] / (2 * (Fr(mp_) ** 2 - Fr(1, 4)))


def ivq(x):
    return iv.mpf(x.numerator) / x.denominator


def certify(model, M):
    A, B, t = model["A"], model["B"], model["t"]
    Kw = A + B
    assert M >= Kw
    Pw = link_law_window(model)
    PI2 = iv.pi ** 2
    total = iv.mpf(0)
    per_link = {}
    for xy in DELTA:
        dl = ivq(DELTA[xy])
        S = iv.mpf(0)
        for m in range(-M, M + 1):
            Pm = Pw[xy][m] if abs(m) <= Kw else P_far(model, m, xy)
            assert Pm > 0
            Qm = 1 / (2 * PI2 * (m - dl) ** 2)
            S += Qm * iv.log(Qm / ivq(Pm))
        per_link[xy] = S
        total += S / 4
    # tail |m| > M: P >= Q  <=  (|m|+1)^2 <= t pi^2 (|m| - 3/4)^2
    c = ivq(t) * PI2
    s_lo = iv.sqrt(c).a                      # lower endpoint of sqrt(t pi^2)
    assert s_lo > 1
    need = (1 + mpf(3) / 4 * s_lo) / (s_lo - 1)
    tail_ok = (M + 1) >= need
    return total, per_link, tail_ok, float(need)


if __name__ == "__main__":
    fn = sys.argv[1]
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    model = rational_model(fn)
    total, per_link, tail_ok, need = certify(model, M)
    LN2 = iv.log(iv.mpf(2))
    Tb = total / LN2
    print(f"{fn}: A={model['A']} B={model['B']} t={float(model['t']):.12f} (t pi^2 = {float(model['t'])*np.pi**2:.6f})")
    for xy, S in per_link.items():
        print(f"  link {xy}: sum_|m|<={M} Q log(Q/P) in [{float(mpf(S.a)):.15f}, {float(mpf(S.b)):.15f}] nats")
    print(f"  tail |m| > {M}: P >= Q verified (needs |m| >= {need:.2f}): {tail_ok}  => tail contribution <= 0")
    print(f"  CERTIFIED: T_inf <= {float(mpf(Tb.b)):.12f} bits  (interval width {float(mpf(Tb.b - Tb.a)):.1e})", flush=True)
    out = dict(A=model["A"], B=model["B"], t=str(model["t"]), mu=[str(x) for x in model["mu"]],
               K0=[[str(x) for x in row] for row in model["K0"]], K1=[[str(x) for x in row] for row in model["K1"]])
    with open(f"zmodel_cert_A{model['A']}.json", "w") as f:
        json.dump(out, f)
