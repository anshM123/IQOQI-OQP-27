"""a09: D_B(1) and D_B(2) for all d >= 2001 (CONE_ALLD_PROOF.md section 7).
With X = Phi_e - F_A on Z_d (X(0) = 0, X(-1) = X(1)) and, for b = 1..4,
   X(b) = eps A0 b^2 + eps^2 phi_2(b) + eps^3 Yh(b) - A0 eps [f(d-b) - f(d)],   Yh(b) = b^4 R2(eps b, 1/b),
   R2(x, w) = U2(w) + x R3,  R3 in (1/6) range_{x' in [0,x]} d_x^3 u_e(x', w)   (x <= b/2001):
   D_B(1) = 7X(1) - 4X(2) + X(3) = eps^2 A_2(1) + eps^3 [7Yh(1) - 4Yh(2) + Yh(3)] + E1,
   D_B(2) = -4X(1) + 6X(2) - 4X(3) + X(4) = eps^2 A_2(2) + eps^3 [-4Yh(1) + 6Yh(2) - 4Yh(3) + Yh(4)] + E2,
   |E_k| <= A0 eps * 18 * max_{j<=4} |f(d-j) - f(d)|, and by QD2-L12 (t35_polya.py, logs/alld/polya.json:
   f = 1/6 - c2/b^2 + c4/b^4 + E, |E| <= C6/b^6 for b >= 1000, c2 = 13/180, c4 = 683/7560)
   |f(d-j) - f(d)| <= c2((d-4)^-2 - d^-2) + c4((d-4)^-4 - d^-4) + 2 C6/(d-4)^6  =: fd(d)  (d fd(d), d^2 fd(d) decrease).
Output logs/alld/smallm.json: exact lower bounds of D_B(1)/eps^2 and D_B(2)/eps^3 valid for every d >= 2001."""
import json
from fractions import Fraction as Fr
import mpmath
from mpmath import iv
from a02_jets import Jet, Space, Z, ONE, ivq, lo_str, hi_str
from a07_zoneI import u_jet, EPS1
from a05_model import A0
from a03_special import kappa, PI
from a08_A2 import phi2

pol = json.load(open('logs/alld/polya.json'))
assert pol['ok']
C2, C4, C6 = ivq(Fr(pol['c2'])), ivq(Fr(pol['c4'])), ivq(Fr(pol['C6_b1000']))

p2 = {0: Z, 1: phi2(1), 2: phi2(2), 3: phi2(3), 4: phi2(4)}
A21 = 7 * p2[1] - 4 * p2[2] + p2[3]
A22 = -4 * p2[1] + 6 * p2[2] - 4 * p2[3] + p2[4]
print("A_2(1) =", mpmath.nstr(A21.mid, 12), " A_2(2) =", mpmath.nstr(A22.mid, 12))

out = {}
for b in (1, 2, 3, 4):
    w = ONE / iv.mpf(b)
    U0 = u_jet(iv.mpf(0), w, 2, 0, ne=2)
    x1 = iv.mpf(b) * EPS1
    Ub = u_jet(iv.mpf([0, x1.b]), w, 3, 0)
    R3 = Ub[(3, 0)]                               # (1/6) d_x^3 u = U[3,0] (normalized coefficient), over x' in [0, x1]
    R2 = U0[(2, 0)] + iv.mpf([0, x1.b]) * R3
    out[b] = iv.mpf(b) ** 4 * R2
    print(f"b={b}: U2 = {mpmath.nstr(U0[(2,0)].mid, 10)},  Yh in [{mpmath.nstr(out[b].a, 8)}, {mpmath.nstr(out[b].b, 8)}]")
S1 = 7 * out[1] - 4 * out[2] + out[3]
S2 = -4 * out[1] + 6 * out[2] - 4 * out[3] + out[4]
d = iv.mpf(2001)
fd = C2 * ((d - 4) ** -2 - d ** -2) + C4 * ((d - 4) ** -4 - d ** -4) + 2 * C6 / (d - 4) ** 6
E = A0 * 18 * fd                                               # |E_k| <= E(d) * eps,  E(d) = 18 A0 fd(d)
print("S1 = 7Yh(1) - 4Yh(2) + Yh(3) in", mpmath.nstr(S1.a, 6), mpmath.nstr(S1.b, 6))
print("S2 = -4Yh(1) + 6Yh(2) - 4Yh(3) + Yh(4) in", mpmath.nstr(S2.a, 6), mpmath.nstr(S2.b, 6))
# D_B(1)/eps^2 >= A21 - eps |S1| - E(d) d;  D_B(2)/eps^3 >= A22 d + S2 - E(d) d^2  (worst case d = 2001: eps|S1|, d fd(d), d^2 fd(d)
# decrease in d and A22 d increases since A22 > 0)
assert A22.a > 0
c1 = (A21 - abs(S1) / 2001 - E * 2001).a
c2 = (A22 * 2001 + S2 - E * 2001 ** 2).a
ok = bool(c1 > -3 and c2 > 0.25)
print(f"D_B(1)/eps^2 >= {float(c1):.6f}  (need >= -3);   D_B(2)/eps^3 >= {float(c2):.3f}  (need >= 0.25)")
print("SMALL-m CERTIFIED:", ok)
json.dump(dict(ok=ok, DB1_lo=lo_str(c1), DB2_lo=lo_str(c2), DB1_lo_f=float(c1), DB2_lo_f=float(c2),
               A21=[lo_str(A21), hi_str(A21)], A22=[lo_str(A22), hi_str(A22)], eps_hi=hi_str(EPS1)),
          open('logs/alld/smallm.json', 'w'), indent=0)
