"""a13: analytic constants of the slack perturbation and of the F_A tail term, in interval arithmetic (RIGOR_ALLD.md s.6, s.7).
For every d >= 2001 (eps = 1/d <= E1 = 1/2001), 1 <= m <= d/2, t = eps m^2 u with 0 <= u <= U (U = 0.7, as in a10):
 (C+)  Ch+_j(b) := (pi/2) eps^j b^(2j-1) F^(2j)(b)/(2^j j!) = eps^(j-1) { k_j B_2j(b) + (pi/2) x^(2j-1) Gamma^(2j)(x)/(2^j j!) } satisfies
       |Ch+_j| <= eps^(j-1) Cp_j,  Cp_j := k_j (4j - 1 + 2j(2j-1)) + (pi/2) 16.76 (2j-2)!/(2^j j!)    (b >= 1; 0 <= x <= 1)
       [|B_2j(b)| <= 4j-1 + 2j(2j-1) for b >= 1 from |psi^(k)(z)| <= (k-1)!/z^k + k!/z^(k+1);  |Gamma^(2j)| <= 16.76 (2j-2)!].
 (GG4) G(m,t) - G_4(m,t) = sum_{j=5}^{7} F^(2j)(m) t^j/(2^j j!) + R7(m,t),  F^(2j)(m) t^j/(2^j j!) = (2/pi) m Ch+_j(m) u^j, so
       |G - G_4| <= eps^3 GG4,  GG4 := (1/pi) sum_{j=5}^{7} Cp_j U^j E1^(j-5) + Rs_n/(2 pi)   (m eps <= 1/2; one-sided
       |R7(m,t)| <= (m/pi) Rs_n eps^4 with Rs_n of a10 (inner version, valid for every m)).
 (DT)  |d_t G_4(m,t)| = |(2/(pi eps m)) sum_{j<=4} j Ch+_j u^(j-1)| <= d DTG4,  DTG4 := (2/pi) sum_{j=1}^{4} j Cp_j E1^(j-1) U^(j-1).
 (W)   |W - W_e|(m) <= |Pot_delta| + |G - G_4|(m, Phi_*) + |d_t G_4| |Phi_* - Phi_e|
                     <= eps [Dd E1^3/8 + GG4 E1^2 + DTG4 dmax],  with |Phi_* - Phi_e| <= dmax eps^2 (a10) and |delta| <= Dd eps^6.
 (TFA) |A0 eps Delta^4 f(d-b)(m)| <= TFA eps^3 for m <= d/2 (f(c) = c^2 (1/B(c) - 1), c = d - b >= d/2 - 2; Binet Taylor model).
Output logs/alld/constants.json (exact rational upper bounds as strings)."""
import json, math
from fractions import Fraction as Fr
import mpmath
from mpmath import iv
from a02_jets import ivq, ivfact, hi_str, lo_str, Z
from a03_special import PI, A_TAIL
from a05_model import kj, A0
import a10_pointwise as A10
from a08_A2 import TMw, binet_tm

E1 = A10.E1
U = A10.U.b


def Cp(j):
    return kj(j) * (4 * j - 1 + 2 * j * (2 * j - 1)) + PI / 2 * A_TAIL * ivfact(2 * j - 2) / iv.mpf(2 ** j * math.factorial(j))


CP = {j: Cp(j) for j in range(1, 8)}
GG4_main = sum((CP[j] * U ** j * E1 ** (j - 5) for j in (5, 6, 7)), Z) / PI
R7_one = iv.mpf(A10.Rs_n) / (2 * PI)
GG4 = (GG4_main + R7_one).b
DTG4 = (2 / PI * sum((j * CP[j] * E1 ** (j - 1) * U ** (j - 1) for j in (1, 2, 3, 4)), Z)).b
print("Cp_j (|Ch+_j| <= eps^(j-1) Cp_j):", ", ".join(f"{j}: {float(CP[j].b):.6g}" for j in range(1, 8)))
print(f"|G - G_4| <= GG4 eps^3:  GG4 = {mpmath.nstr(GG4_main.b, 8)} (orders 5..7) + {mpmath.nstr(R7_one.b, 6)} (R7) = {mpmath.nstr(GG4, 8)}")
print(f"|d_t G_4| <= DTG4 d:  DTG4 = {mpmath.nstr(DTG4, 8)}  (old hard-coded value 40/pi = {40/math.pi:.6f})")

# F_A tail term: f(c) = w^-2 (1/B - 1), w = 1/c, c >= d/2 - 2 on the stencil (m <= d/2), so w <= Wt := 2 eps/(1 - 4 eps);
# f = sum_{k>=4} c_k w^(k-2) + rem (Binet TM of B_2 with K = 6, |rem| <= rho w^(N-2)), Delta^4 c^-p <= p(p+1)(p+2)(p+3) (c-2)^-(p+4)
# and 1/(c - 2) <= Wt/(1 - 2 Wt).  Each term / eps^2 increases with eps, so eps = E1 is the worst case.
Wt = 2 * E1 / (1 - 4 * E1)
Bt = binet_tm(1, 6, Wt)
fm = Bt.inv1() + (-1)
assert all(abs(fm.c[k]).b == 0 for k in (0, 1, 3))          # 1/B - 1 is even in w and O(w^2)
TFA = Z
for k in range(4, fm.N):
    p = k - 2
    TFA += abs(fm.c[k]) * p * (p + 1) * (p + 2) * (p + 3) * (Wt / (1 - 2 * Wt)) ** (p + 4)
TFA += 16 * fm.rho * Wt ** (fm.N - 2)
# the k = 2, 3 coefficients of 1/B - 1 give the terms c_2 + c_3 w of f: polynomial of degree <= 1 in w is NOT killed by Delta^4 in c,
# so they must be included: c_2 w^0 is constant (killed), c_3 w^1 = c_3/c (Delta^4 c^-1 <= 24 (c-2)^-5).
TFA += abs(fm.c[3]) * 24 * (Wt / (1 - 2 * Wt)) ** 5
TFA_eps3 = (A0 * TFA / E1 ** 2).b
print(f"F_A tail term: |A0 eps Delta^4 f(d-b)| <= {mpmath.nstr(TFA_eps3, 4)} eps^3   (1/B - 1 coefficients c_2 = {mpmath.nstr(fm.c[2].mid, 6)}, c_3 = {mpmath.nstr(abs(fm.c[3]).b, 3)})")

json.dump(dict(Cp={j: hi_str(CP[j]) for j in range(1, 8)}, GG4=hi_str(GG4), DTG4=hi_str(DTG4), R7_one=hi_str(R7_one), SG1=hi_str(A10.SG1),
               Dd=hi_str(A10.Dd), Rs_n=hi_str(A10.Rs_n), TFA_eps3=hi_str(TFA_eps3), U=str(Fr('0.7')), eps_hi=hi_str(A10.EPS1),
               GG4_f=float(GG4), DTG4_f=float(DTG4), TFA_f=float(TFA_eps3)),
          open('logs/alld/constants.json', 'w'), indent=0)
