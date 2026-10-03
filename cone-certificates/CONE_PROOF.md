# CONE_d: construction, exact reduction, certificates and the large-d reduction

Notation.  d >= 2, N = 4d, G(u) = -(N^2/(2 pi^2)) Cl2(2 pi u/N), Ghat(u) = G(u) + G(2d - u), so Ghat''(u) = 2 csc(pi u/2d) on (0, 2d).
v_m = Ghat''(m) (m = 1..d-1).  For a d-periodic cell vector ell (ell_r >= 0, sum ell_r = d) with window sums S_r(m) = ell_r + ... + ell_{r+m-1},
u^ell_m = Delta^2_m (1/d) sum_r Ghat(S_r(m))  (QD2-L2).  CONE_d: v in the closed convex cone of {u^ell}.  The two-residue vectors give the
directions t_s = e_s + e_{d-s} (QD2-R2), so CONE_d holds as soon as  u + w = c v  for some mixture u of cell directions, some c > 0 and
some w with w_m = w_{d-m} >= 0.

Potentials.  For a cell process put P(m) := E (1/d) sum_r Ghat(S_r(m)) (m = 0..d); then u = Delta^2 P on 1..d-1, P(0) = Ghat(0), P(d) = Ghat(d).
P_v := the solution of Delta^2 P_v = v on 1..d-1 with P_v(0) = Ghat(0), P_v(d) = Ghat(d).  For W with W(0) = W(d) = 0:
   u + Delta^2 W = v   <=>   P + W = P_v.
Writing X_A(m) = (X(m) - X(d-m))/2, X_S(m) = (X(m) + X(d-m))/2:

LEMMA R1 (reduction).  If a cell process satisfies (i) P_A = (P_v)_A and (ii) W := (P_v - P)_S has Delta^2 W >= 0 on 1..d-1, then CONE_d holds.
Proof.  W is symmetric, W(0) = W(d) = 0 (P and P_v share boundary values), w := Delta^2 W is symmetric and >= 0, and by (i) P + W = P_v,
so u + w = v with w a nonnegative combination of the t_s.  []

Binomial base.  F(b) := E Ghat(d X_b), X_b ~ Beta(b, d - b), b in (0, d); F(0) := Ghat(0), F(d) := Ghat(d).  For ell = d Dir(beta_0..beta_{d-1})
(given beta), S_r(m)/d ~ Beta(B_r(m), d - B_r(m)) with B_r(m) = beta_r + ... + beta_{r+m-1} (aggregation property of the Dirichlet law), so
E[Ghat(S_r(m)) | beta] = F(B_r(m)).

LEMMA R2 (exact singular part).  Ghat = Ghat_s + Ghat_r with Ghat_s(u) = (4d/pi) u log(u/d) and Ghat_r(u) = d^2 g_r(u/d),
g_r(x) = -(8/pi^2)[Cl2(pi x/2) + Cl2(pi - pi x/2)] - (4/pi) x log x, analytic on the complex disc |x| < 2.  With F_s, F_r and P_{v,s}, P_{v,r}
the corresponding parts,  F_s(m) = P_{v,s}(m) = (4d/pi)[m psi(m) + 1 - m/d - m psi(d)]  for every integer 0 <= m <= d.
Proof.  E[X log X] = (b/d)[psi(b+1) - psi(d+1)] (size-biasing), so F_s(b) = (4d/pi) b[psi(b+1) - psi(d+1)]; at integers use m psi(m+1) = m psi(m) + 1
and psi(d+1) = psi(d) + 1/d.  Delta^2[m psi(m)] = 1/m for m >= 1 (with m psi(m) := -1 at m = 0), and Ghat_s(0) = Ghat_s(d) = 0.  []
Hence P_v - F = P_{v,r} - F_r involves only the analytic function g_r.

Gaussian modulation.  Let Phi: {0..d} -> [0, inf) be symmetric with Phi(0) = Phi(d) = 0 and a discrete variogram, i.e.
   at_k(Phi) := -(2/d) sum_{m in Z_d} Phi(m) cos(2 pi k m/d) >= 0  (1 <= k < d/2),   -(1/d) sum_m Phi(m) cos(pi m) >= 0 (k = d/2, d even).
Then c(j) := Delta^2 Phi(j)/2 (periodic second difference) is a positive-definite function on Z_d with sum_j c(j) = 0, and the centred
stationary Gaussian vector eta on Z_d with covariance c has sum_r eta_r = 0 and Var(eta_0 + ... + eta_{m-1}) = Phi(m).
PROCESS Pi_Phi: on E := {max_r |eta_r| < 3/4} take ell = d Dir(1 + eta); on E^c take ell = d Dir(1,...,1).

LEMMA R3 (direction of Pi_Phi).  P(m) = E[F(m + Z(m)); E] + P(E^c) F(m),  Z(m) := eta_0 + ... + eta_{m-1} ~ N(0, Phi(m)).
On E, |Z(m)| < (3/4) min(m, d-m), so m + Z(m) lies in (m/4, (3d+m)/4) intersected with (m - 3(d-m)/4, 7m/4), a subset of (0, d).
Proof.  Rotation averaging + stationarity of (eta, E); on E, B_r(m) = m + Z_r(m) and |Z_r(m)| < 3m/4, and also B_r(m) = d - B_{r+m}(d-m).  []

LEMMA R4 (decoupling).  Put, for 1 <= m <= d-1 and t >= 0, with L_m := (3/4) min(m, d-m),
   H(m, t) := E[F(m + sqrt(t) xi); |sqrt(t) xi| < L_m] + F(m) P(|sqrt(t) xi| >= L_m),   xi ~ N(0,1).
Then |P(m) - H(m, Phi(m))| <= L_m sup_{|z| < L_m} |F'(m + z)| P(E^c),  P(E^c) <= 2d exp(-9/(32 Phi(1))).
Proof.  {|Z(m)| >= L_m} subset E^c (Lemma R3), so the two expressions differ by -E[(F(m+Z) - F(m)) 1{|Z| < L_m} 1_{E^c}].  The bound on P(E^c)
is the union bound with Var eta_0 = Phi(1).  []

Consequently, up to an error of size e^{-c d}, condition (i) of Lemma R1 decouples into ONE scalar equation per m < d/2:
   (D_m)   H(m, Phi(m)) - H(d-m, Phi(m)) = 2 (P_v)_A(m),
and the exact condition (i) follows from the decoupled solution by the fixed-point Lemma B below (Poincare-Miranda on a box of
width O(e^{-cd})).  The monotonicity in Phi(m) that Lemma B needs is NOT assumed: it is certified on the boxes used.

LEMMA B (from the decoupled to the exact equations; Poincare-Miranda).  Write Hc_m(t) := [H(m,t) - F(m)] - [H(d-m,t) - F(d-m)] and
tau_m := Dlt(m) - Dlt(d-m), so that (D_m) reads Hc_m(t) = tau_m.  For a symmetric variogram Phi (Phi(d-m) = Phi(m), Phi(0) = 0, Phi(d/2)
fixed when d is even), condition (i) of Lemma R1 for the process Pi_Phi is exactly
     F_m(Phi) := Hc_m(Phi(m)) + e_m(Phi) - tau_m = 0   (1 <= m < d/2),   e_m(Phi) := [P(m) - H(m,Phi(m))] - [P(d-m) - H(d-m,Phi(m))],
since P(m) - P(d-m) = Hc_m(Phi(m)) + F(m) - F(d-m) + e_m and Dlt = P_v - F.  Let lo_m < hi_m and suppose, on the box
Q := {Phi : Phi(m) in [lo_m, hi_m], 1 <= m < d/2}:
  (B1) at_k(Phi) > 0 for all k and all Phi in Q, so the Gaussian process exists. Then Pi_Phi depends continuously on Phi: the
       Gaussian law is continuous in its covariance, and the integrand of P is bounded and continuous off a null set.
  (B2) |e_m(Phi)| <= 2 eps_t for all Phi in Q, by Lemma R4 with P(E^c) <= 2d exp(-9/(32 max_Q Phi(1))).
  (B3) Hc_m(lo_m) < tau_m - 2 eps_t and Hc_m(hi_m) > tau_m + 2 eps_t for every m.
Then some Phi^# in Q satisfies F_m(Phi^#) = 0 for all m, i.e. condition (i) holds exactly for Pi_{Phi^#}.
Proof.  F = (F_m) is continuous on the box Q by (B1).  On the face Phi(m) = lo_m, (B2)-(B3) give F_m < 0; on Phi(m) = hi_m, F_m > 0.  The
Poincare-Miranda theorem gives a zero in Q.  []
(B3) is obtained from a certified sign change and a certified derivative bound. Suppose Hc_m(a_m) < tau_m < Hc_m(b_m) and
inf_{[a_m - rho, b_m + rho]} Hc_m' >= c > 0 with c rho >= 2 eps_t. Then lo_m = a_m - rho and hi_m = b_m + rho satisfy (B3).  Condition (ii)
of Lemma R1 for Phi^# then follows from the slack certified on Q up to 4(eps_t + rho sup|d_t H|).
APPLICATIONS (certified).
  * 201 <= d <= 2000 -- FINAL CERTIFICATES: verify_cert.py d -> logs/cert_g_d{d}.json (one script, one precision (160 bits),
    one code version (sha256 recorded in each file), one box per d), audited by audit_cert_g.py (logs/audit_cert_g_final.log:
    1800/1800 OK).  The script finds the root boxes [a_m, b_m], widens them by r (a power of two, rounded outward) and certifies ON
    THE WIDENED BOX: min at_k, min slack, inf Hc_m' >= c1min/4 (condition (D)), and (B3) both via (D) and directly at the faces;
    factorials/binomials/Bernoulli numbers are exact, zeta values are rigorous Euler-Maclaurin enclosures, P(E^c) and eps_t are kept
    as logarithms, and every bound is stored as an exact decimal string.  Minimum margins: d^2 min at_k >= 0.0632 (even d),
    0.1264 (odd d); d min Delta^2 W >= 0.660; (D) ratio >= 4.0009; face margins >= 10^16.7 x 2 eps_t.  Details: RIGOR_GAUSS.md.
    (Superseded earlier pipeline: verify_gauss.py + verify_fixedpoint.py -> logs/vg_d*.json, logs/fp_d*.json; kept for comparison.)
  * d >= 2001 (a12_fp_alld.py -> logs/alld/fp_alld.json).  On every box of the a10 scan, F'(u) >= Fp >= 0.152 for u in
    [0, U + 1e-3]; in the half-boxes x >= 0.45 this holds after division by (1 - 2x) >= 1/d.  Here F(u) = (pi/(2m))[Hc_m(eps m^2 u) - tau_m],
    so Hc_m' >= (2/(pi eps m)) 0.152/d >= 0.19/d.  Take the IVT interval of section 8 widened by rho = 10.5 d eps_t <= 10^(-363).
    The at_k margin (0.1187 eps^2) and the slack margin (0.6168 eps) absorb 2 rho and 4(eps_t + rho d^2).

CERTIFICATES (2026-10-01).  verify_gauss.py turns the above into a rigorous certificate for one d at cost O(d^2): interval enclosure of
Phi_* (decoupled equations with an exact order-14 Gaussian expansion and an order-16 Lagrange remainder), interval DFT, slack, and the
tail/Brouwer lemma (box radius r = 8 eps_tail / min c_1; margins min at_k > 2r, w > 4(r sup|F''| + eps_tail)).  All 201 <= d <= 1000 are
CERTIFIED (logs/vg_d*.json); with the LP certificates (certs/, d <= 200): CONE_d for 2 <= d <= 1000.

LARGE-d REDUCTION (QD2-L11, QD2-L12, LOG.md section 8).  With eps = 1/d, A0 = pi/2 - 1, F_A(m) = A0 eps [f(m) + f(d-m) - f(d)] and
D_B = Delta^4 (Phi_* - F_A) (periodic centred differences):
   8 d s^4 at_k(Phi_*) >= 16 A0 (A_min - 0.1445/(d-1)) eps s^4 - 4 gamma eps^2 s^2 + beta (1 - 4 eps) eps^2,   A_min >= 0.10548,
whenever D_B(1) >= -gamma eps^2 and D_B(m) >= beta eps^3 (2 <= m <= d/2).  The boundary term is positive by Polya/Fejer because
a(m) = 1/6 - f(m) is convex (QD2-L12, rigorous).  Positive definiteness for large d therefore reduces to the POINTWISE statement QD2-C2
(D_B(1) >= -3 eps^2, D_B(m) >= eps^3, slack >= 0), which holds numerically with true constants gamma = 2.756, beta ~ 9.8 and has explicit
leading terms D_B(m) = eps^2 A_2(m) + eps^3 A_3(m) + ..., A_2 = Delta^4 phi_2 (QD2-L10/N17).

REMAINING (the analytic core): for the solution Phi_* of (D_m), prove (PD) at_k(Phi_*) > 0 for all k with a margin, and (SL) Delta^2 W >= 0
with a margin, for all d >= d0.  Numerics (t27/t28): d = 41, 60, ... : all at_k > 0 with high-frequency floor d^2 at_k ~ 0.13 and low-k
at_k k^4/d ~ 0.0168; slack d Delta^2 W in [0.63, 0.87].
