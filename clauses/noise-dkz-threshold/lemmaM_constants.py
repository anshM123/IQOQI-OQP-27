"""arb checks of the constants and identities used in the analytic part (d >= 2002) of Lemma M (NOTES.md Sec. 5)."""
import flint
from flint import arb
flint.ctx.prec = 150
pi = arb.pi()
C = arb.const_catalan()
phi = lambda t: 1 / arb(4 * t + 1) ** 2 - 1 / arb(4 * t + 3) ** 2
kinf = 16 * C / pi ** 2
print("kappa_inf = 16C/pi^2 =", kinf.str(12))
print("C - 8/9 =", (C - arb(8) / 9).str(12))
# Delta_max = sum_{t>=1} t phi(t): partial sum to T plus tail bound sum_{t>T} t phi(t) <= sum 1/(15 t^2) <= 1/(15 T)
T = 200000
s = arb(0)
for t in range(1, T + 1):
    s += t * phi(t)
print("sum_{t>=1} t phi(t) in", (s).str(10), "+ tail <=", (arb(1) / (15 * T)).str(5))
Dmax = s + arb(1) / (15 * T)
# identity kappa_d = kappa_inf - 32 Delta_d/(pi^2 S), Delta_d = sum_{n=0}^{S} n Phi(n), vs closed form I_ME/2
for d in [3, 4, 7, 50, 333]:
    S = d - 1
    Delta = arb(0)
    for n in range(d):
        Phi = arb(0)
        for k in range(0, 4000):
            Phi += phi(n + k * d)
        Delta += n * Phi
    kap_closed = arb(0)
    for j in range(1, d):
        kap_closed += arb(d - j) / (pi * j / (2 * d)).cos()
    kap_closed = kap_closed * 2 / (d * (d - 1))
    kap_id = kinf - 32 * Delta / (pi ** 2 * S)
    print(f"d={d}: closed form {kap_closed.str(12)}  identity {kap_id.str(12)}  (truncation of Phi at k<4000: error < 1e-7/d^2)")
S = 2001
print("for S >= 2001: kappa >= kappa_inf - 32*Dmax/(pi^2 S) =", (kinf - 32 * Dmax / (pi ** 2 * S)).str(10))
kmin = kinf - 32 * Dmax / (pi ** 2 * S)
Amax = 8 / (pi ** 2 * kmin)
print("A' = 8/(pi^2 kappa) <=", Amax.str(10), "; c*d = 1 - 1/kappa >=", (1 - 1 / kmin).str(10))
print("(P3) 2 Q(0) - 1 >= 16/(pi^2 kappa_inf) - 1 =", (16 / (pi ** 2 * kinf) - 1).str(10))
gam = arb(99) / 404
print("gamma =", gam.str(10), " z1/S <=", (arb(1) / 2 - gam).str(10))
# regime E final inequality: gamma*(S+3)/S * (2/0.255 - 32*0.12074/0.555/ ... ) computed as in the notes
a_frac = 1 - (arb(1) / 2 - gam)                      # a = S - z > (1/2 + gam) S
Phi_coef = 1 / (15 * a_frac) + arb(1) / 32           # Phi(S-z) <= Phi_coef / (S a^2)
lhs_bad = 32 * Phi_coef / a_frac ** 2 * (arb(1) / 2 - gam) ** 2   # 2(4z+1)(4z+3) Phi(S-z) <= 32 (z+1)^2 * Phi_coef/(S a^2), (z+1) < (1/2-gam) S
main = 2 / (arb(1) / 2 - gam)
print("regime E: (S/(S+3)) * RHS/gamma >=", (main - lhs_bad).str(8), "; gamma*(main - bad) =", (gam * (main - lhs_bad)).str(8), "(> 1 needed)")
# (P2) bound: m_I * d <= 4.04*A'*(C - 8/9) + tiny  vs  c*d
print("(P2): 4.04*A'*(C-8/9) =", (arb(404) / 100 * Amax * (C - arb(8) / 9)).str(8), " < c*d >=", (1 - 1 / kmin).str(8))
