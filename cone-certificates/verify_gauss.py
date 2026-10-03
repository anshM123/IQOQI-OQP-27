"""Rigorous (interval) verification of the GAUSSIAN-MODULATION certificate for CONE_d (CONE_PROOF.md, Lemmas R1-R4).

For a given d it encloses, with mpmath.iv (outward rounding):
  F^(2j)(m) (j = 0..4) at the integers m = 1..d-1, where F(b) = E Ghat(d X_b), X_b ~ Beta(b, d-b), split as F = F_s + F_r:
     F_s(b) = (4d/pi) b [psi(b+1) - psi(d+1)]            (exact; polygamma at integers = zeta values - harmonic sums)
     F_r(b) = d^2 sum_{i odd} g_i (b)_i/(d)_i             (g_r(x) = sum g_i x^i, odd, radius 2; tail bounded below)
  tau_m = (P_{v,r} - F_r)(m) - (P_{v,r} - F_r)(d-m),  P_{v,r} = discrete Dirichlet potential of g_r''(m/d) with P(0) = 0, P(d) = d^2 g_r(1);
  Phi_*(m) = the root of  sum_{j=1}^{3} t^j [F^(2j)(m) - F^(2j)(d-m)]/(2^j j!) + R(t) = tau_m  (R = Gaussian-Taylor remainder, enclosed);
  the variogram coefficients at_k(Phi_*) (all k) and the slack w = Delta^2 W, W = (P_v - H(., Phi_*))_S.
The certificate holds for this d if min at_k > 0 and min w > 0 with the margins required by the tail/fixed-point lemma (also checked).
Usage: python verify_gauss.py d [prec_bits]
"""
import sys, time, json
from fractions import Fraction
import mpmath
from mpmath import iv, mp

d = int(sys.argv[1])
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 160
iv.prec = PREC
mp.prec = PREC + 40
t0 = time.time()
PI = iv.pi
ONE = iv.mpf(1)


def ivc(x):
    """interval from an mpmath number computed at extra precision, widened by a relative 2^-(PREC) margin."""
    x = mp.mpf(x)
    e = abs(x) * mp.mpf(2) ** (-PREC) + mp.mpf(2) ** (-2 * PREC)
    return iv.mpf([x - e, x + e])


# ---------------------------------------------------------------- constants
ZETA = {s: ivc(mp.zeta(s)) for s in range(2, 19)}
NSER = int(sys.argv[3]) if len(sys.argv) > 3 else 70     # number of odd Taylor terms of g_r (tail bounded below)
gco = {}                                     # g_i for odd i
gco[1] = -(4 / PI) * (1 + iv.log(4 / PI))
for n in range(1, NSER + 1):
    p, q = mpmath.bernfrac(2 * n)
    Bn = iv.mpf(abs(int(p))) / iv.mpf(int(q))
    fact = iv.mpf(mpmath.factorial(2 * n + 1))
    cn = Bn / (2 * n * fact)
    gco[2 * n + 1] = (8 / PI ** 2) * cn * PI ** (2 * n + 1) * (iv.mpf(1) / 2 - iv.mpf(4) ** (-n))
IMAX = 2 * NSER + 1
# tail bound: |g_i| <= Cg 2^-i for i > IMAX (|B_2n| <= 4 (2n)!/(2pi)^{2n}); (b)_i/(d)_i <= 1 and derivative factors bounded below
def gr_val(x):
    s = gco[1] * x
    xp = x
    x2 = x * x
    for n in range(1, NSER + 1):
        xp = xp * x2
        s += gco[2 * n + 1] * xp
    return s


def gr2(x):
    """g_r''(x) = 2 csc(pi x/2) - (4/pi)/x."""
    return 2 / iv.sin(PI * x / 2) - (4 / PI) / x


# ---------------------------------------------------------------- harmonic sums H^{(s)}_n, n = 0..d+IMAX
HMAX = d + IMAX + 2
H = {s: [iv.mpf(0)] for s in range(1, 18)}
for n in range(1, HMAX + 1):
    for s in range(1, 18):
        H[s].append(H[s][-1] + ONE / iv.mpf(n) ** s)


def polyg(nord, mm):
    """psi^(nord)(mm + 1) for integer mm >= 0, nord >= 1:  (-1)^(nord+1) nord! [zeta(nord+1) - H^{(nord+1)}_mm]."""
    sgn = 1 if (nord + 1) % 2 == 0 else -1
    return sgn * iv.mpf(mpmath.factorial(nord)) * (ZETA[nord + 1] - H[nord + 1][mm])


def kappa(j, mm):
    """d^j/db^j [b psi(b+1)] at b = mm (j >= 2):  j psi^(j-1)(mm+1) + mm psi^(j)(mm+1)."""
    return j * polyg(j - 1, mm) + mm * polyg(j, mm)


# ---------------------------------------------------------------- F_r and its b-derivatives at integers
def bell(L, k):
    L1, L2, L3, L4, L5, L6, L7, L8 = L
    if k == 0:
        return ONE
    if k == 2:
        return L1 ** 2 + L2
    if k == 4:
        return L1 ** 4 + 6 * L1 ** 2 * L2 + 4 * L1 * L3 + 3 * L2 ** 2 + L4
    if k == 6:
        return (L1 ** 6 + 15 * L1 ** 4 * L2 + 20 * L1 ** 3 * L3 + 45 * L1 ** 2 * L2 ** 2 + 15 * L1 ** 2 * L4 + 60 * L1 * L2 * L3
                + 15 * L2 ** 3 + 6 * L1 * L5 + 15 * L2 * L4 + 10 * L3 ** 2 + L6)
    if k == 8:
        return (L1 ** 8 + 28 * L1 ** 6 * L2 + 56 * L1 ** 5 * L3 + 210 * L1 ** 4 * L2 ** 2 + 70 * L1 ** 4 * L4 + 560 * L1 ** 3 * L2 * L3
                + 420 * L1 ** 2 * L2 ** 3 + 56 * L1 ** 3 * L5 + 420 * L1 ** 2 * L2 * L4 + 280 * L1 ** 2 * L3 ** 2 + 840 * L1 * L2 ** 2 * L3
                + 105 * L2 ** 4 + 28 * L1 ** 2 * L6 + 168 * L1 * L2 * L5 + 280 * L1 * L3 * L4 + 210 * L2 ** 2 * L4 + 280 * L2 * L3 ** 2
                + 8 * L1 * L7 + 28 * L2 * L6 + 56 * L3 * L5 + 35 * L4 ** 2 + L8)


FACT = [mpmath.factorial(i) for i in range(10)]


def Fr_derivs(mm):
    """[F_r, F_r'', F_r'''', F_r^(6), F_r^(8)] at b = mm (1 <= mm <= d-1), plus a rigorous tail allowance."""
    out = [iv.mpf(0)] * 5
    ratio = ONE                               # (mm)_i/(d)_i built incrementally
    for i in range(1, IMAX + 1):
        ratio = ratio * iv.mpf(mm + i - 1) / iv.mpf(d + i - 1)
        if i % 2 == 0:
            continue
        g = gco[i]
        # L_s = (d/db)^s log (b)_i at b = mm = (-1)^(s-1) (s-1)! [H^{(s)}_{mm+i-1} - H^{(s)}_{mm-1}]
        L = []
        for s in range(1, 9):
            Ls = H[s][mm + i - 1] - H[s][mm - 1]
            L.append(Ls * (FACT[s - 1] * (1 if s % 2 == 1 else -1)))
        for idx, k in enumerate([0, 2, 4, 6, 8]):
            out[idx] += g * ratio * bell(L, k)
    d2 = iv.mpf(d) ** 2
    # tail i > IMAX (odd i): |g_i| <= 4 2^-i; (mm)_i/(d)_i <= ((mm+i)/(d+i))^i (each factor <= (mm+i)/(d+i)) and <= 1;
    # |Y_k(L)| <= k! max(1, i/mm)^k  (|L_s| <= (s-1)! i/mm^s, Bell generating function), k <= 8
    tail = iv.mpf(0)
    bm = iv.mpf(mm)
    for i in range(IMAX + 2, IMAX + 600, 2):
        r = ((bm + i) / iv.mpf(d + i)) ** i
        r = iv.mpf(min(r.b, 1))
        y = iv.mpf(max(1, i / mm)) ** 8 * 40320
        tail += 4 * iv.mpf(2) ** (-i) * r * y
    tail += iv.mpf(2) ** (-(IMAX + 500))
    res = []
    for idx in range(5):
        res.append(d2 * (out[idx] + iv.mpf([-1, 1]) * tail))
    return res


# ---------------------------------------------------------------- assemble F^(2j)(m)
c4d = 4 * iv.mpf(d) / PI
REGA = {}
for kk in (8, 10, 12, 14, 16):
    ddk = ONE
    for q in range(kk):
        ddk = ddk * iv.mpf(d + q)
    bnd = 8 * iv.mpf(mpmath.factorial(kk)) * iv.mpf(d) ** 2 / ddk      # |F_r^(k)(b)| <= 8 k! d^2/(d)_k on [0,d]
    REGA[kk] = iv.mpf([-bnd.b, bnd.b])
Fv = {}
for mm in range(1, d):
    fr = Fr_derivs(mm)
    Fs0 = c4d * iv.mpf(mm) * (H[1][mm] - H[1][d])   # b[psi(b+1) - psi(d+1)] at b = mm, psi(mm+1) - psi(d+1) = H_mm - H_d
    Fv[mm] = [Fs0 + fr[0],
              c4d * kappa(2, mm) + fr[1],
              c4d * kappa(4, mm) + fr[2],
              c4d * kappa(6, mm) + fr[3],
              c4d * kappa(8, mm) + fr[4],
              c4d * kappa(10, mm) + REGA[10],
              c4d * kappa(12, mm) + REGA[12],
              c4d * kappa(14, mm) + REGA[14]]
print(f"d={d}: F derivatives enclosed [{time.time()-t0:.0f}s]", flush=True)

# ---------------------------------------------------------------- P_{v,r} by prefix sums (Delta^2 P = f on 1..d-1, P(0) = 0, P(d) = d^2 g_r(1))
f = [None] + [gr2(iv.mpf(j) / d) for j in range(1, d)]
Pd = iv.mpf(d) ** 2 * gr_val(ONE)
# P(m) = (m/d) P(d) - sum_j G(m,j) f(j),  G(m,j) = j (d-m)/d (j <= m), m (d-j)/d (j >= m)
pre1 = [iv.mpf(0)]
for j in range(1, d):
    pre1.append(pre1[-1] + iv.mpf(j) * f[j])
suf2 = [iv.mpf(0)] * (d + 1)
for j in range(d - 1, 0, -1):
    suf2[j] = suf2[j + 1] + iv.mpf(d - j) * f[j]
Pvr = [iv.mpf(0)] * (d + 1)
Pvr[d] = Pd
for mm in range(1, d):
    Pvr[mm] = iv.mpf(mm) / d * Pd - (iv.mpf(d - mm) / d * pre1[mm] + iv.mpf(mm) / d * suf2[mm + 1])
FrV = [iv.mpf(0)] + [None] * (d - 1) + [Pd]          # F_r(0) = 0, F_r(d) = d^2 g_r(1)
FRREG = {}
for mm in range(1, d):
    FrV[mm] = Fv[mm][0] - c4d * iv.mpf(mm) * (H[1][mm] - H[1][d])
Dlt = [Pvr[mm] - FrV[mm] for mm in range(d + 1)]      # P_v - F = P_{v,r} - F_r  (Lemma R2)

# ---------------------------------------------------------------- decoupled equations (rigorous remainder)
half = (d - 1) // 2
Phi = {}
FAC8 = iv.mpf(40320)


S8CACHE = {}


def S8(mm, L, tag):
    """rigorous upper bound of sup_{|z| <= L} |F^(12)(mm + z)| (cached per (mm, tag))."""
    key = (mm, tag)
    if key in S8CACHE:
        return S8CACHE[key]
    S8CACHE[key] = _S8(mm, L)
    return S8CACHE[key]


def _S8(mm, L):
    """sup_{|z| <= L} |F^(16)(mm + z)| (order-16 Gaussian remainder):
       |kappa_16(b)| <= 31*14!/(b+1)^15 + 32*15!/(b+1)^16   (|psi^(n)(z)| <= (n-1)!/z^n + n!/z^(n+1));
       |F_r^(16)| <= 8 * 16! d^2/(d)_16."""
    blo = iv.mpf(mm) - L
    sing = c4d * (31 * iv.mpf(mpmath.factorial(14)) / (blo + 1) ** 15 + 32 * iv.mpf(mpmath.factorial(15)) / (blo + 1) ** 16)
    return (sing + abs(REGA[16]).b).b


def trunc_mom(j, t, L):
    """upper bound of E[|sqrt(t) xi|^(2j) 1{|sqrt(t) xi| >= L}] = t^j E[xi^(2j) 1{|xi| >= a}], a = L/sqrt(t):
       int_a^inf x^n e^{-x^2/2} dx <= a^(n-1) e^{-a^2/2}/(1 - (n-1)/a^2)  (a^2 > n-1; integration by parts)."""
    a2 = L * L / t
    n = 2 * j
    if a2.a <= n - 1 + 1:
        return (t ** j * iv.mpf(10) ** 6).b        # useless regime: huge allowance
    a = iv.sqrt(a2)
    val = 2 / iv.sqrt(2 * PI) * a ** (n - 1) * iv.exp(-a2 / 2) / (1 - (n - 1) / a2)
    return (t ** j * val).b


FAC16 = iv.mpf(mpmath.factorial(16))
TCO = [None] + [iv.mpf(2 ** j * mpmath.factorial(j)) for j in range(1, 8)]     # 2^j j!


def HmF(mm, t):
    """enclosure of H(mm, t) - F(mm) = sum_{j=1}^{7} t^j F^(2j)(mm)/(2^j j!) + [order-16 Lagrange remainder, two levels] + [truncation]."""
    L = 3 * iv.mpf(min(mm, d - mm)) / 4
    Fj = Fv[mm]
    main = iv.mpf(0)
    tp = ONE
    for j in range(1, 8):
        tp = tp * t
        main += tp * Fj[j] / TCO[j]
    tt = iv.mpf(t.b) if hasattr(t, 'b') else t
    Lnear = iv.mpf(min(mm, d - mm)) / 2
    err = (2027025 * tt ** 8 * S8(mm, Lnear, 'near') + trunc_mom(8, tt, Lnear) * S8(mm, L, 'far')) / FAC16
    for j in range(1, 8):
        err += abs(Fj[j]).b * trunc_mom(j, tt, L) / iv.mpf(mpmath.factorial(2 * j))
    e = err.b if hasattr(err, 'b') else err
    return main + iv.mpf([-e, e])


for mm in range(1, half + 1):
    tau = Dlt[mm] - Dlt[d - mm]
    c1 = (Fv[mm][1] - Fv[d - mm][1]) / 2
    def G(t):
        ti = iv.mpf(t)
        return HmF(mm, ti) - HmF(d - mm, ti)
    # Newton iterations on midpoints (float side), then a rigorous sign-change enclosure
    c2m = (Fv[mm][2] - Fv[d - mm][2]) / 8
    c3m = (Fv[mm][3] - Fv[d - mm][3]) / 48
    cms = [None] + [(Fv[mm][j] - Fv[d - mm][j]) / TCO[j] for j in range(1, 8)]
    tm = mp.mpf((tau / c1).mid.a)
    for it in range(40):
        fval = mp.mpf((sum(cms[j] * tm ** j for j in range(1, 8)) - tau).mid.a)
        fder = mp.mpf(sum(j * cms[j] * tm ** (j - 1) for j in range(1, 8)).mid.a)
        tm = tm - fval / fder
    a_, b_ = tm, tm
    step = abs(tm) * mp.mpf(2) ** (-PREC // 2) + mp.mpf(2) ** (-PREC)
    while (G(a_) - tau).b >= 0:
        a_ -= step; step *= 2
    step = abs(tm) * mp.mpf(2) ** (-PREC // 2) + mp.mpf(2) ** (-PREC)
    while (G(b_) - tau).a <= 0:
        b_ += step; step *= 2
    Phi[mm] = iv.mpf([a_, b_])
    Phi[d - mm] = Phi[mm]
Phi[0] = iv.mpf(0)
if d % 2 == 0:
    h2 = d // 2
    ext = (15 * Phi[h2 - 1] - 6 * Phi[h2 - 2] + Phi[h2 - 3]) / 10
    Phi[h2] = iv.mpf(mp.mpf(ext.mid.a))                 # a definite (exact) choice: the antisymmetric equation is vacuous at d/2
print(f"   Phi_* enclosed; max width {max(float(mp.mpf(Phi[mm].delta.a)) for mm in range(1, d) if mm != d//2 or d % 2):.2e}; Phi(1) d = {float(mp.mpf(Phi[1].mid.a))*d:.6f} [{time.time()-t0:.0f}s]", flush=True)

# ---------------------------------------------------------------- variogram coefficients
cosv = [iv.cos(2 * PI * iv.mpf(j) / d) for j in range(d)]
min_at = None; argk = None; low = []
for k in range(1, d // 2 + 1):
    s = iv.mpf(0)
    for mm in range(1, (d - 1) // 2 + 1):
        s += Phi[mm] * cosv[(k * mm) % d]
    s = 2 * s
    if d % 2 == 0:
        s += Phi[d // 2] * (1 if k % 2 == 0 else -1)
    wgt = iv.mpf(2) / d if 2 * k != d else iv.mpf(1) / d
    a = -wgt * s
    if min_at is None or a.a < min_at:
        min_at = a.a; argk = k
    if k <= 4:
        low.append(float(mp.mpf(a.mid.a)) * k ** 4 / d)
min_at = mp.mpf(min_at); print(f"   min at_k (lower endpoint) = {float(min_at):+.4e} at k = {argk};  d^2 * min = {float(min_at)*d*d:.4f}; at_k k^4/d (k<=4) = {[round(x,4) for x in low]} [{time.time()-t0:.0f}s]", flush=True)

# ---------------------------------------------------------------- slack: W = (P_v - H(., Phi))_S (rigorous HmF above)
Wv = [iv.mpf(0)] * (d + 1)
for mm in range(1, d):
    a1 = Dlt[mm] - HmF(mm, Phi[mm])
    a2 = Dlt[d - mm] - HmF(d - mm, Phi[d - mm])
    Wv[mm] = (a1 + a2) / 2
w = [Wv[mm + 1] - 2 * Wv[mm] + Wv[mm - 1] for mm in range(1, d)]
wmin = mp.mpf(min(x.a for x in w))
asym = mp.mpf(max(abs(((Dlt[mm] - HmF(mm, Phi[mm])) - (Dlt[d - mm] - HmF(d - mm, Phi[d - mm])))).b for mm in range(1, half + 1)))
print(f"   slack: min w (lower) = {float(wmin):+.4e} (d * min = {float(wmin)*d:.4f});  antisym residual upper = {float(asym):.2e} [{time.time()-t0:.0f}s]", flush=True)

# ---------------------------------------------------------------- tail / fixed-point lemma (CONE_PROOF.md, Lemma R4 + Brouwer)
# eps_tail(m) <= L_m sup|F'| P(E^c);  sup|F'| <= (4d/pi)(H_d + 1) + 8d;  P(E^c) <= 2d exp(-1/(8 Phi(1)^+)) with Phi(1)^+ = Phi(1) + r.
supF1 = (c4d * (H[1][d] + 1) + 8 * iv.mpf(d)).b
c1min = min(((Fv[mm][1] - Fv[d - mm][1]) / 2).a for mm in range(1, half + 1))
r_box = mp.mpf(0)
for it in range(3):                               # fixed point in r (P(E^c) depends on Phi(1) + r only weakly)
    Phi1p = mp.mpf(Phi[1].b) + r_box
    ptail = 2 * d * mp.exp(-mp.mpf(9) / (32 * Phi1p))  # E = {max |eta_r| < 3/4}, Var eta_0 = Phi(1)
    eps_tail = mp.mpf(3) * d / 8 * mp.mpf(supF1) * ptail
    need_r = 8 * eps_tail / mp.mpf(c1min)
    r_box = max(need_r, mp.mpf(10) ** (-30))
# perturbation of at_k by a box displacement: <= (2/d) sum |dPhi| <= 2 r ; slack perturbation <= 4 (|dH| + eps_tail), |dH| <= r sup|F''|/2-ish
supF2 = max(abs(Fv[mm][1]).b for mm in range(1, d))
dslack = 4 * (r_box * mp.mpf(supF2) + eps_tail)
ok_tail = (mp.mpf(min_at) > 2 * r_box) and (wmin > dslack)
print(f"   tail: P(E^c) <= {mp.nstr(ptail, 4)}, eps_tail <= {mp.nstr(eps_tail, 4)}, box radius r = {mp.nstr(r_box, 4)};"
      f" at_k margin {float(min_at):.3e} > 2r; slack margin {float(wmin):.3e} > {mp.nstr(dslack, 3)}")
ok = bool((min_at > 0) and (wmin > 0) and ok_tail)
json.dump(dict(d=d, ok=ok, min_at=float(min_at), argk=argk, wmin=float(wmin), ptail=float(ptail), need_r=float(need_r), secs=time.time() - t0),
          open(f"logs/vg_d{d}.json", "w"))
print(f"   CERTIFIED: {ok}  [{time.time()-t0:.0f}s]")

if __import__('os').environ.get('QD2_DUMP'):
    # optional: midpoints of the certified enclosures of Phi_* (structural diagnostics of D_B only; not part of the certificate)
    json.dump(dict(d=d, Phi=[mpmath.nstr(mp.mpf(Phi[mm].mid.a), 40) for mm in range(d)]), open(f"logs/phi_d{d}.json", "w"))
