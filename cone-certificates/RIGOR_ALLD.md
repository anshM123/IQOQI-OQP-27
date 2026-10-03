# RIGOR_ALLD: the d >= 2001 part of CONE_d, made complete (proofs, code, re-run)

Status 2026-10-02.  Scope: every item that the audit of the analytic regime (formal-conjectures/OQP27/STATUS_L4.md s.7.3, gaps
G6, G7; Q_chain_check/REPORT.md item 5 and G4) lists for d >= 2001 as "on paper only", "sketched", "hard-coded" or as a code gap.
Paths are relative to iqoqi/programs/oqp27B_all/QD2/.  Notation as in CONE_ALLD_PROOF.md (s.0, s.2) and CONE_PROOF.md.
Tags: PROVED (written proof below), CERTIFIED (interval arithmetic; script + archived log), NUMERICAL (evidence only).
Reproduce: `python run_alld.py 12` (all scripts, logs in logs/alld/, then `audit_alld.py` -> logs/alld/audit_alld.log).

## 0. Summary

| item (audit) | before | now | where |
|---|---|---|---|
| identity I2, b^3 U1 = phi_2 | first-order sketch + jets at 5 values of b | PROVED (s.2); exact symbolic check, independent 90-digit numerics (17 values of b), interval jets (162 values) | s.2; a14_identities.py, logs/alld/identities.json |
| identity I1; also W0 (omega(0,w) = -(1-2/pi)), the Tt + EMx form of tauh_e, W_e = b omega and its symmetry | on paper | PROVED (s.2), same three checks | s.2; a14 |
| Lemma P, QD2-L11 | on paper | PROVED (s.3) | s.3 |
| Fejer/Polya step of QD2-L12 | on paper | PROVED (s.4); t35_polya.py made rigorous and logged | s.4; logs/alld/polya.json, t35_polya.log |
| A_min >= 0.105487899757 | hard-coded, no log | CERTIFIED A_min >= 0.10548789975773862... (exact rational in polya.json), read by the audit | t35_polya.py |
| constants of a10 | on paper | every constant derived (s.5) and computed in interval arithmetic; defects corrected (s.1, items 2, 3, 7) | a10_pointwise.py, logs/alld/pointwise.json |
| \|G - G_4\| <= 137.7 eps^3 (200 in code) | numerical / hard-coded | CERTIFIED GG4 = 138.103 (orders 5..7: 137.744; R7: 0.359) | a13_constants.py, logs/alld/constants.json |
| \|d_t G_4\| <= (40/pi) d | hard-coded | CERTIFIED DTG4 = 11.5703 (< 40/pi = 12.73) | a13_constants.py |
| section-4 decomposition, zone bookkeeping | on paper | PROVED (s.6); the audit checks coverage, overlaps and eps-ranges EXACTLY | s.6; audit_alld.py |
| monotonicity in d of the tail lemma | on paper | PROVED (s.8); the audit evaluates every margin as a function of d | s.8 |
| G6 (53-bit factorials/binomials) | 57/80 factorial and 305/938 binomial intervals missed the integer | exact integers with outward rounding everywhere; test_exact.py | s.9 |
| G7 (float decisions) | floats in audit and stores | every decision is an exact rational or interval comparison | s.10 |
| re-run | | ALL-D CERTIFIED (s.11) | logs/alld/ |

## 1. Defects found while doing this (all fixed; none changes a conclusion)

1. Coverage hole at d = 2001 (G7).  For x in [0.011, 0.03] the outer D_B sweep and the outer slack sweep split eps in pieces with
   cut points computed as `mpmath.mpf(EPS1.b)`, which ROUNDS the upper end of 1/2001 to 53 bits, below 1/2001 (by 1.6e-20).  So
   Q_O and the slack density were certified there for eps <= 1/2001 - 1.6e-20, i.e. not for d = 2001 itself.  Now the cut
   points are thin 120-bit values >= 1/2001 shared by adjacent pieces (a06 `eps_pieces`), and every zone log stores its eps range
   exactly; the audit checks eps_hi >= 1/2001 for every file.
2. a10, outer remainder constant: the claim "b - 10 sqrt(t) >= 0.813 x d" is false; the correct constant is
   1 - 10 sqrt(0.7/2001) = 0.812964 < 0.813.  Now computed as an interval (`c813`).
3. a10, inner remainder bounds Rs_n, dRs_n omitted the F_r part of F^(16) and every exponentially small term (far window
   m/2 < |Z| < 3m/4, truncation |Z| >= 3m/4, boundary terms of d/dt H) was replaced by an unproved "1e-30 allowance" or
   "(1 + 1e-5)" factor; the Euler-Maclaurin defect series was truncated at l < 40 without a tail bound; the Cauchy majorant MA
   skipped the term i = 2401 and used float(1.9) < 1.9 as the radius.  All are now explicit (s.5).
4. a09 used |E| <= 0.409/b^6 (QD2-L12) at b = d - j >= 1997, but t35 certified it only for b >= 3000.  t35 now certifies
   C6 <= 0.408788 for b >= 1000 and a09 reads that value.
5. t35: the convexity tail check at m = M0 used the expansion at w = 1/(M0 - 1) outside its range [0, 1/M0] (now at m = M0 + 1);
   zeta(3) was an mpmath float value widened by 2^-300 (now enclosed by the alternating series
   (5/2) sum (-1)^(k+1)/(k^3 C(2k,k)), exact rational partial sums).
6. a04 `poch_tail`: the far-tail bound n^q <= ((1 + nE)/E)^q holds only for q >= 0 but was used with q = -2, -1 for the
   coefficients (0,0), (1,0) of S (tail too small by a factor ~(N2 E)^-2; the omitted mass is < 10^-300).  Now q := max(q, 0).
   The Euler-Maclaurin series tails (i >= 2001, n >= 3000) are now bounded geometrically instead of a 1e-100 allowance.
7. Model-root identity in the jets: `implicit_root_jet` now verifies that the Krawczyk enclosure R contains the model root u_e
   (either R lies in (0,1), or the polynomial has no zero on [0,1] minus R, by interval evaluation with bisection).  The a10
   uniqueness scan now also covers x in [0.5, 0.501] (box [0.49, 0.501]), where a06/a11 evaluate the model.
8. G6 (s.9) and the hard-coded constants of audit_alld.py (s.10).

## 2. The model identities  [PROVED]

Fix b >= 1, w = 1/b.  Along the ray eps = x w (0 <= x <= x0, eps <= 1/2001) the model coefficients of CONE_ALLD_PROOF.md s.2 are
   Ch_j(x, w) = eps^(j-1) { k_j [B_2j(1/w) - (x/(1-x))^(2j-1) B_2j(1/v)] + (pi/2) x^(2j-1) S^(2j)(x, eps)/(2^j j!) },  v = eps/(1-x),
   tauh_e(x, w) = (pi/2) tau_e(b)/b,   tau_e(b) = [Pt - F_r](b) - [Pt - F_r](d - b),
with S^(2j) = d_x^(2j) S at fixed eps, S(x, eps) = sum_n (g_n - a_n) P_n(x, eps), P_n = prod\_{k<n} r_k, r_k = (x + k eps)/(1 + k eps).

LEMMA M1 (regularity).  Let 0 < X < 1, 0 < E <= 1/2001, p := (1 - X)/E.  On the box [0, X] x [0, E] the series
S = sum (g_n - a_n) P_n, Tt = sum (g_n - a_n) Qt_n, Tg = sum g_n Qt_n (Qt_n = (x^n - P_n)/(eps x)) and all their termwise
derivatives d_x^a d_eps^c with a + 2c <= p - 3 converge absolutely and uniformly.  Hence S, Tt, Tg are C^(p-3) there and may be
differentiated termwise.  (For X = 1/2, E = 1/2001: p >= 1000.)
Proof.  Majorants: at any point of the box the Taylor coefficients of r_k in (h, h') (increments of x, eps) are dominated by those
of R_k + h + (1 + h) sum\_{g>=1} k^g h'^g, R_k := (X + kE)/(1 + kE) <= 1 (d_x r_k = 1/(1+k eps) <= 1, d_x^2 r_k = 0,
|d_eps^g r_k|/g! = k^g (1-x)/(1+k eps)^(g+1) <= k^g, |d_x d_eps^g r_k|/g! <= k^g).  In the product over k < n at most a + c
factors are differentiated; the undifferentiated ones contribute at most prod\_{k=a+c}^{n-1} R_k (R_k increases in k), and the
remaining combinatorial sum is at most [h^a](1+h)^n [h'^c] prod_k (1 - k h')^(-1) = C(n,a) h_c(0,..,n-1).  Hence
   |d_x^a d_eps^c P_n| <= n^(a+c) (n+c)^c prod\_{k=a+c}^{n-1} R_k                                            (Leibniz bound)
(a04 `poch_tail`).  Since log R_k <= -(1-X)/(1+kE), prod\_{k=N}^{n-1} R_k <= ((1+NE)/(1+nE))^p.  With |g_n - a_n| <= 34/n^2
(n >= 200; |g_n| <= (8 pi/3)/(2^n n(n-1)), |a_n| <= 16.76/(n(n-1))) the n-th term is O(n^(a+2c-2-p)), summable when a + 2c <= p - 2.
For Qt_n use Qt_n = -int_0^1 int_0^1 (d_x d_eps P_n)(t x, s eps) ds dt (both P_n(x,0) - P_n(x,eps) and d_eps P_n(0,.) vanish
appropriately), which costs one more x- and eps-derivative.  []

LEMMA M2 (Qt along the ray).  For eps = x w and n >= 1:  Qt_n(x, xw) = x^(n-2) [1 - prod\_{k<n} (1 + k w)/(1 + k w x)]/w
(r_k = x (1 + kw)/(1 + kwx)).  Hence Qt_1 = 0, Qt_2 = -(1-x)/(1+wx) = -1 + (1+w) x + O(x^2), Qt_3 = -(3+2w) x + O(x^2), and
Qt_n(x, xw) = O(x^2) with d_x Qt_n(x, xw)|\_0 = 0 for n >= 4.  (Also Qt_0 = 0 and the recursion
Qt\_{n+1} = Qt_n r_n - x^(n-1) n (1-x)/(1 + n eps) used by a04.)  []

LEMMA M3 (Binet at large argument).  For j >= 1 and K >= 2, B_2j(1/v) = 1 - beta_j1 v^2 + Rt with |Rt^(l)| <= C v^(2K-l)
(a03: polygamma remainder bound for real arguments, Lah transfer); so v -> B_2j(1/v) is C^(2K-1) on [0, v0] with
B_2j(1/v) = 1 + O(v^2).  []

PROPOSITION T (the form used by a04/a05).  For 0 < x < 1:  (pi/2) tau_e/b = (pi/2)(Tt + EMx),
   EMx = sum\_{k=1,2} aEM_k eps^(2k-1) [g^(2k)(x)/x - (g^(2k)(1-x) - g^(2k)(1))/x - 2 g^(2k)(1)],  aEM = (-1/12, 1/240), g = g_r.
Proof.  Write p = g + sum_k aEM_k eps^(2k) g^(2k).  Pt(b) = d^2 [p(x) - x (p(1) - g(1))], F_r(b) = d^2 Gamma(x),
F_r(d-b) = d^2 Gamma(1-x) with Gamma(x) = sum g_n P_n and Gamma(1-x) := sum a_n P_n (X\_{d-b} = 1 - X_b in law,
g(1-y) = sum a_n y^n).  Then, since d^2/b = 1/(eps x),
   tau_e/b = (1/(eps x)) { [p - Gamma](x) - [p - Gamma](1-x) + (1 - 2x)(p(1) - g(1)) }.
Split p - Gamma = (g - Gamma) + (p - g): (g(x) - Gamma(x)) - (g(1-x) - Gamma(1-x)) = sum (g_n - a_n)(x^n - P_n), giving Tt; the rest
is sum_k aEM_k eps^(2k) [g^(2k)(x) - g^(2k)(1-x) + (1-2x) g^(2k)(1)]/(eps x) = EMx.  (CONE_ALLD_PROOF.md s.2 wrote T without the
linear term (1-2x)(p(1) - g(1)); the formula EMx and the code include it.)  []

PROPOSITION E (expansions at x = 0, fixed w).  As x -> 0+:
 (a) Ch_1 = B(b) - (pi/2) x + O(x^2);  (b) Ch_2 = (w B_4(b)/2) x + O(x^2);  (c) Ch_3, Ch_4 = O(x^2);
 (d) tauh_e = A0 + (pi/2) [-(1 + pi/12) + t1c w] x + O(x^2),  t1c = -(2/3 + 5 pi/72 + 1/(3 pi)),  A0 = pi/2 - 1.
Proof.  Special values from the closed form g_r''(y) = 2 csc(pi y/2) - 4/(pi y): g_r'' = (pi/6) y + O(y^3), so g_3 = pi/36, g_2 = 0;
g_r''(1) = 2 - 4/pi, g_r'''(1) = 4/pi, hence a_2 = g_r''(1)/2 = 1 - 2/pi, a_3 = -g_r'''(1)/6 = -2/(3 pi).
(a) j = 1 (k_1 = 1): by M3, (x/(1-x)) B_2(1/v) = x + O(x^2) (v = O(x)); by M1 (C^1) S''(x, xw) = S''(0,0) + O(x) and
S''(0,0) = sum (g_n - a_n) d_x^2 P_n(0,0) = 2 (g_2 - a_2) = -2 a_2 because P_n(x, 0) = x^n.  So
Ch_1 = B - x + (pi/4) x (-2 a_2) + O(x^2) = B - x - A0 x + O(x^2) = B - (pi/2) x + O(x^2).
(b) j = 2 (k_2 = 1/2): eps = x w and the bracket equals B_4(b) + O(x^3).  (c) eps^(j-1) = O(x^2) times bounded brackets.
(d) By Proposition T, tauh_e = (pi/2)[Tt(x, xw) + EMx(x, xw)].  By M1 and M2 (termwise differentiation; only n = 2, 3 contribute
to orders x^0, x^1):  Tt = (g_2 - a_2) Qt_2 + (g_3 - a_3) Qt_3 + O(x^2) = a_2 + [-a_2 (1 + w) - (g_3 - a_3)(3 + 2w)] x + O(x^2).
EMx = -(x w/12) [6 g_3 - 6 a_3 - 4 a_2] + O(x^2) (g''(x)/x -> 6 g_3, (g''(1-x) - g''(1))/x -> -g'''(1) = 6 a_3, -2 g''(1) = -4 a_2;
the k = 2 term is O(x^3)).  So tauh_e(0) = (pi/2) a_2 = A0 and
   d_x tauh_e(0) = (pi/12) [(-6 a_2 - 18 g_3 + 18 a_3) + w (-4 a_2 - 15 g_3 + 15 a_3)] = (pi/2)[-(1 + pi/12) + t1c w]. []

THEOREM I (identities I1, I2).  u_e(0, w) = A0/B(b) (I1) and b^3 d_x u_e(0, w) = phi_2(b) (I2), where
   phi_2(b) = -(pi/2)(1 + pi/12) b^3/B + (pi/2) t1c b^2/B + (pi/2) A0 b^3/B^2 - (A0^2/2) b^2 B_4/B^3   (a08_A2.py).
Proof.  P(u; x) := sum\_{j<=4} Ch_j(x) u^j - tauh_e(x) is C^1 in (u, x) near x = 0 (M1, M3).  At x = 0, P = B u - A0 with
B = b kappa_2(b) = 2b sum\_{k>=0} (k+1)/(b+1+k)^3 > 0 (kappa_n(b) = (-1)^n n! sum_k (k+1)/(b+1+k)^(n+1)); the Binet bound with K = 2
(|Rt| <= mu(2) b^-4, mu(2) = (|B_4|/4!)(5! + 2 \* 4!) = 7/30) gives B >= 1 - 1/6 - 7/30 = 3/5 > A0 for b >= 1.  So the root is
U0 = A0/B in (0, 1) and P_u = B > 0.  By the implicit function theorem there is a unique C^1 root branch u(x) through U0;
for small x it lies in (0, 1), where the model root u_e is the unique root (a10 certificate), so u = u_e.  Differentiating,
U1 = d_x u_e(0) = [d_x tauh_e - d_x Ch_1 U0 - d_x Ch_2 U0^2]/B
   = [(pi/2)(-(1 + pi/12) + t1c w) + (pi/2) A0/B - (w B_4/2) A0^2/B^2]/B,
and b^3 U1 (w = 1/b) is exactly phi_2(b).  []

PROPOSITION W (slack model).  W_e(b) := Dlt_e(b) - G_4(b, Phi_e(b)) equals b omega(x, w) with
   omega = Tg + sum_k aEM_k eps^(2k-1) [g^(2k)(x)/x - g^(2k)(1)] - (2/pi) sum\_{j<=4} Ch+\_j u_e^j     (a11),
W_e(d - b) = W_e(b), and omega(0, w) = -(1 - 2/pi) for every w (W0).
Proof.  Dlt_e = Pt - F_r, so Dlt_e/b = (1/(eps x))[p(x) - x (p(1) - g(1)) - Gamma(x)] = Tg + EM-part as in Proposition T.
F^(2j)(b) t^j/(2^j j!) with t = eps b^2 u equals (2/pi) b Ch+\_j u^j (Ch+\_j = (pi/2) eps^j b^(2j-1) F^(2j)(b)/(2^j j!)), so
G_4/b = (2/pi) sum Ch+\_j u^j.  Symmetry: W_e(b) - W_e(d-b) = tau_e(b) - sum\_{j<=4} c_j(b) Phi_e(b)^j = 0 (model equation).
At x = 0: eps = 0, Tg(0,0) = sum g_n Qt_n(0,0) = g_2 (-1) = 0 (M2), the EM part vanishes, Ch+\_1 = B, Ch+\_j = 0 (j >= 2),
u_e = A0/B, so omega(0, w) = -(2/pi) A0 = -(1 - 2/pi).  []

VERIFICATION (a14_identities.py, logs/alld/a14_identities.log, identities.json):
 * Part S (sympy, exact): Lemma M2 for n <= 6 (also the exact factorisation), the a04 recursion (n <= 6), the special values
   g_3 = pi/36, g_5 = 7 pi^3/28800 (= Bernoulli formula of a03), g_r''(1), g_r'''(1); Propositions E(a)-(d) with generic symbols
   g_i, a_n, B_2j; then I1, I2 (b^3 U1 - phi_2 simplifies to 0) and W0.
 * Part N (mpmath, 90 digits, implementation independent of a02-a11: g_i from zeta, a_n from mpmath.taylor of the closed form
   of g_r'', B_2j from psi, Pochhammer polynomials expanded, tauh_e from its DEFINITION via Pt and F_r): the model equation is solved
   at x = k 1e-5 (k = 1..8) for 17 values of b in [1, 1000]; degree-7 extrapolation gives U0, U1.  Max relative errors:
   I1 1.1e-29, I2 6.2e-25 (extrapolation-limited), and |definition - (Tt + EMx)| 4.0e-42 relative (Proposition T).
 * Part J (interval jets of a07 at thin x = 0): the enclosures of U0(w), U1(w) intersect A0/B and phi_2/b^3 at 161 values of b
   in [1, 1000] and at w = 0; omega(0, w) encloses -(1 - 2/pi) at 41 values.
 * a01_model.py (prototype, exact discrete tau, Gaussian order 7): the model reproduces the certified Phi\_\* midpoints at d = 1000
   to relative 1e-18..1e-30 and at d = 2000 to 1e-19..1e-34 (logs/alld/a01_model_d1000.log, a01_model_d2000.log).

## 3. QD2-L11 and Lemma P  [PROVED]

Let X be symmetric on Z_d with X(0) = 0, th = 2 pi k/d, s = sin(th/2), Xhat(th) = sum\_{m in Z_d} X(m) cos(m th),
at_k(X) = -(2/d) Xhat (1 <= k < d/2), -(1/d) Xhat (k = d/2); w_k = 1 (k < d/2), 1/2 (k = d/2).
(i) Symbol: the periodic Delta^4 has symbol (2 - 2 cos th)^2 = 16 s^4 and sum_m Delta^4 X(m) = 0, so
   S_X(th) := sum\_{m=1}^{d-1} Delta^4 X(m)(1 - cos m th) = -16 s^4 Xhat(th) = 8 d s^4 at_k(X)/w_k.
(ii) Boundary layer.  F_A(m) = A0 eps [f(m) + f(d-m) - f(d)], f(0) = 0, a(m) = 1/6 - f(m).  Using cos(d th) = 1 and
sum\_{m=1}^{d-1} cos(m th) = -1 (k != 0): -Xhat(F_A) = A0 eps [a(0) + 2 sum\_{m=1}^{d-1} a(m) cos(m th) + a(d)].  With
A(th) := a(0) + 2 sum\_{m>=1} a(m) cos(m th) >= A_min and a(m) >= 0 (QD2-L12):
   S\_{F_A}(th) >= 16 A0 eps s^4 [A_min - 2 sum\_{m>=d} a(m)] >= P eps s^4,   P := 16 A0 (A_min - 0.1446/(d-1)),
since m^2 a(m) <= 0.0723 for all m >= 1 (t35) and sum\_{m>=d} m^-2 <= 1/(d-1).
(iii) Remainder.  D_B := Delta^4 (X - F_A) is symmetric; if D_B(1) >= -gamma eps^2 and D_B(m) >= beta eps^3 (2 <= m <= d/2), then
the terms m = 1, d-1 give >= -2 gamma eps^2 (1 - cos th) = -4 gamma eps^2 s^2 and the others (1 - cos m th >= 0) give
>= beta eps^3 sum\_{m=2}^{d-2} (1 - cos m th) = beta eps^3 (d - 2 + 2 cos th) >= beta eps^2 (1 - 4 eps).  So
   S_X(th) >= P eps s^4 - 4 gamma eps^2 s^2 + beta eps^2 (1 - 4 eps)                              (QD2-L11)
LEMMA P.  If moreover Phi = Phi_e + delta with Phi_e as X above and |delta(m)| <= delta_max (delta(0) = 0), then for all k
   at_k(Phi) >= w_k [(eps^2/8)(P - 4 gamma^2/(beta d (1 - 4/d))) - 2 delta_max].
Proof.  at_k(Phi_e) = w_k S/(8 d s^4) >= w_k (eps^2/8)[P - 4 gamma eps y + beta eps (1 - 4 eps) y^2] (y = 1/s^2), and
min_y [-4 gamma eps y + beta eps (1-4eps) y^2] = -4 gamma^2 eps/(beta (1 - 4 eps)).  |at_k(delta)| <= (2/d)(d-1) delta_max
< 2 delta_max (k < d/2) and <= (1/d)(d-1) delta_max < 2 w_k delta_max (k = d/2).  []
Every term is monotone in d (P increases, 4 gamma^2/(beta (d - 4)) decreases), so the audit evaluates at d = 2001.

## 4. QD2-L12: positivity, convexity, Fejer/Polya  [PROVED; CERTIFIED by t35_polya.py]

a(m) = 1/6 - f(m), f(m) = m^2 (1/B(m) - 1), f(0) = 0.
(i) Certified (t35, 240 bits): a(m) > 0 and Delta^2 a(m) > 0 for 1 <= m <= 3000 (psi'(m+1) = zeta(2) - H_m^(2),
psi''(m+1) = -2(zeta(3) - H_m^(3)), zeta(3) by the alternating Apery-type series with exact partial sums); for m >= 3001 from
f = 1/6 - c2 w^2 + c4 w^4 + E, c2 = 13/180, c4 = 683/7560, |E| <= C6 w^6 on w <= 1/3000 (C6 = 0.408787; Binet remainder
|rho| <= (11/30) b^-8; exact polynomial algebra with Fractions):  Delta^2 a(m) >= 6 c2/m^4 - (20 c4 + 4 C6)/(m-1)^6 > 0 (Jensen for
the convex s^-4, Peano kernel for s^-6; the ratio is monotone in m, checked at m = 3001 where the stencil has w <= 1/3000);
a(m) >= (c2 - c4 w^2 - C6 w^4) w^2 > 0; m^2 a(m) <= c2 + C6 w^4 < 0.0723 (and max\_{m<=3001} m^2 a(m) = 0.0722222 <= 0.0723).
So a is positive, convex, a(m) -> 0, and sum_L L^2 Delta^2 a(L) < oo (Delta^2 a = O(L^-4)).
(ii) Fejer/Polya.  With D(L) = a(L) - a(L+1) >= 0 (a convex and -> 0) and D(L) -> 0: a(m) = sum\_{k>=m} D(k) and
D(k) = sum\_{L>=k+1} Delta^2 a(L), so (Tonelli) a(|m|) = sum\_{L>=1} Delta^2 a(L) (L - |m|)\_+ for every m in Z.  Then
   A(th) = sum\_{m in Z} a(|m|) e^(i m th) = sum\_{L>=1} Delta^2 a(L) K_L(th),  K_L(th) = sum\_{|m|<L} (L - |m|) e^(i m th)
         = |sum\_{k<L} e^(i k th)|^2 >= 0
(interchange justified by sum_L Delta^2 a(L) L^2 < oo), and K_1 = 1, so A(th) >= Delta^2 a(1) = 2 f(1) - f(2) for every th.
(iii) Value (certified): A_min >= 2 f(1) - f(2) = 0.105487899757738626396586152741564423407851... (f(1) = 1/(pi^2/3 - 2 zeta(3)) - 1,
f(2) = 1/(pi^2/6 + 1 - 2 zeta(3)) - 4, both checked against these closed forms).  The audit reads the exact rational from polya.json.

## 5. The pointwise lemma: every constant of a10  [PROVED + CERTIFIED]

Setting: d >= 2001, eps <= E1 = 1/2001, 1 <= m < d/2, t = eps m^2 u, 0 <= u <= Uu <= U = 0.7 (Uu = R_hi + 1e-3 with R_hi >= u_e the
upper end of the box's Krawczyk enclosure; Uu <= U checked per box),
L = 3m/4 for both sides c in {m, d-m}.  F(u) = sum\_{j<=7} Ch_j u^j + Rs(u) - tauh_m, Rs = (pi/(2m))[R7(m,t) - R7(d-m,t)],
Es := tauh_m - tauh_e(m).  Gaussian expansion with truncation (Lemma R4): for c in {m, d-m},
   H(c,t) - F(c) = E[(F(c+Z) - F(c)) 1{|Z|<L}] = sum\_{j<=7} F^(2j)(c) t^j/(2^j j!) + R7(c,t),
   R7(c,t) = -sum\_{j=1}^{7} F^(2j)(c) T_2j/(2j)! + E[F^(16)(c + th Z) Z^16/16!; |Z| < L],  T_2j = E[Z^2j; |Z| >= L],
and, by the heat equation d_t phi_t = (1/2) phi_t'' and two integrations by parts on [-L, L],
   d_t R7(c,t) = (1/2) E[F^(16)(..) Z^14/14!; |Z|<L] - (1/2) sum\_{j=0}^{6} F^(2j+2)(c) T_2j/(2j)! + Bd,
   |Bd| <= F1(d) (a^2 + 1) a phi(a)/L,  a = L/sqrt(t),  F1(d) = sup\_(0,d) |F'| <= (4d/pi)(H_d + 1) + d SG1,
SG1 = sum_i i |g_i| <= 1.88838 (certified), H_d <= log d + 1.
Ingredients (all computed in a10 Part A, interval arithmetic, exact integers):
 * |g_r^(n)(y)| <= n! MA/(9/10)^n on [0,1] (Cauchy on |z - y| = 9/10 inside |z| <= 19/10; MA = 4.0032 >= sum |g_i| (19/10)^i =
   4.003162, all odd i <= 2399 summed plus a geometric tail from i = 2401).
 * Euler-Maclaurin defect |delta(k)| <= Dd eps^6, Dd = 235.5917: the eps^0, eps^2, eps^4 terms cancel exactly
   (1/240 - 1/144 + 1/360 = 0); the l-sum is summed for l < 40, the tail l >= 40 bounded geometrically (ratio <= 2 (eps/r)^2).
   Discrete Green function: |Pot| <= max|delta| m(d-m)/2 <= Dd eps^4/8, so |Es| <= (pi/8) Dd eps^4/m; for the divided equation
   (x >= 0.45) |Pot(m) - Pot(d-m)| <= (d - 2m)(d - 1) Dd eps^6 gives |Es|/(1-2x) <= (pi/2) Dd eps^4 (eps/x).
 * psi-bounds: |psi^(k)(z)| <= (k-1)!/z^k + k!/z^(k+1) (z > 0); (c+1)^15 |kappa_16(c)| <= KT = 16\*14! + 16\*15!/(5/4) + 15! + 16!/4
   (c >= 1/4); (c+1)^(2j-1) |kappa_2j(c)| <= K2j = 2j(2j-2)! + j(2j-1)! + (2j-1)! + (2j)!/4 (c >= 1).
 * |F_r^(n)| <= 16.76 (n-2)! d^(2-n) (0 <= d_x^n P_i <= n! C(i,n), sum_i |g_i| C(i,n) <= 16.76/(n(n-1))).
 * Gaussian tails: E[xi^n; |xi| >= a] <= 2 a^(n-1) phi(a)/(1 - (n-1)/a^2) (a^2 > n+1; I_n = a^(n-1) phi(a) + (n-1) I\_(n-2),
   I\_(n-2) <= I_n/a^2), E[xi^0; ..] <= 2 phi(a)/a; decreasing in a.  a >= a_rho = 1/(2 sqrt(E1 U)) = 26.73 (|Z| > m/2) and
   a >= a_L = 3/(4 sqrt(E1 U)) = 40.10 (|Z| >= 3m/4).
Inner version (every m; near window |Z| <= m/2, c + z >= m/2):
   |Rs|/eps^4 <= Rs_n = E1^3 [4 KT 2^15 + pi 16.76 14! 2^-15] 15!! U^8/16! + TR_I = 2.254173,
   |dRs/du|/eps^4 <= dRs_n = E1^3 [2 KT 2^15 + (pi/2) 16.76 14! 2^-15] 13!! U^7/14! + DTR_I = 25.76198,
where TR_I, DTR_I (far window, truncation, boundary terms) are <= 5.0e-136, 1.2e-136.
Outer version (x >= 0.015; near window |Z| <= 10 sqrt t, c + z >= c813 m with c813 = 1 - 10 sqrt(E1 U) = 0.8129638 (not 0.813),
far window |xi| > 10 with the explicit G16(10), G14(10)):  Rs_nO = 0.0015363, dRs_nO = 0.017557 (exp-small parts <= 1.7e-330).
Monotonicity in d: every exp-small term has the form s^q (log s)^r exp(-c s) (s = 1/eps = d) with q <= 12, r <= 1 and
c = 9/(32 U) = 0.40 (truncation, boundary) or c = 1/(8 U) = 0.18 (inner far window), so c s >= 357 >> q + r; such a term decreases
in s for s >= 2001 (also after multiplication by s, as needed for the divided equation), so its value at E1 bounds all d >= 2001.
Per box (a10 `check_box`, all interval arithmetic): uniqueness (U1) Ch_1 - 2|Ch_2| - 3|Ch_3| - 4|Ch_4| > 0, (U2) tauh > 0,
(U3) Ch_1 + .. + Ch_4 > tauh, (U4) u_e in the Krawczyk enclosure R; residual |F(u_e)| <= num eps^4 with
num = sum\_{j=5}^{7} |Ch'\_j| E1^(j-5) R_hi^j + (Rs + Es bounds); Fp = Ch_1 - sum\_{j>=2} j |Ch_j| Uu^(j-1) - dRs eps^4 > 0 on [0, Uu];
du = (num/Fp) eps^4 with du + 1e-6 <= 5e-4 and u_e > du + 1e-6 (du + 1e-6 < R_lo, or P_e < 0 on [0, du + 1e-6]), so that
[u_e - du - 1e-6, u_e + du + 1e-6] lies in [0, Uu] (the 1e-6 covers the widening by rho in Lemma B, s.8); then IVT: a root u\_\* in
[u_e - du, u_e + du], |Phi\_\* - Phi_e| = eps m^2 du <= (K \* scale) eps^2 (scale = b_hi^2 E1^3 for b-boxes, x_hi^2 E1 otherwise).
Box plan: b in [1,30] (62 boxes, x <= E1 b), w in [0, 1/30] with x <= 0.015 (4 boxes), x in [0.015, 0.45] (87 boxes),
x in [0.45, 0.5] and [0.49, 0.501] (6 boxes, divided by 1 - 2x): 159 boxes covering {0 <= eps <= 1/2001, b = x/eps >= 1,
x <= 0.501} -- every point where a06, a07, a09, a11 evaluate the model (coverage checked by the audit).
RESULT: see s.11.

## 6. Section-4 decomposition and zone bookkeeping  [PROVED; checked exactly by the audit]

(i) Peano kernels: for g in C^4[m-2, m+2], Delta^4 g(m) = int\_{-2}^{2} g''''(m+s) M_4(s) ds (M_4 the centred cubic B-spline, >= 0,
mass 1); Delta^2 g(m) = int\_{-1}^{1} g''(m+s)(1 - |s|) ds.  (Checked numerically to 1e-40.)
(ii) At fixed eps, b -> (x, w) = (eps b, 1/b) gives d_b = w th, th = x d_x - w d_w, and (w th)(w^-k g) = w^(1-k)(th + k) g;
hence d_b^4 [b^4 R] = (th+1)(th+2)(th+3)(th+4) R =: Lambda(R), d_b^2 [b^2 g] = (th+1)(th+2) g; on functions of w alone th = -w d_w;
th (x g) = x (th + 1) g; th commutes with x -> s x.  (a07 also checks its operator table on monomials.)
(iii) Taylor in x at fixed w (u_e is C^3 along the segment, M1 and the IFT with P_u > 0 certified by a10):
u_e = U0 + x U1 + x^2 R2, R2 = U2(w) + x R3, R3 = int_0^1 ((1-s)^2/2) d_x^3 u_e(sx, w) ds in (1/6) hull(d_x^3 u_e).  With I1, I2:
   Phi_e(b) = eps A0 b^2/B + eps^2 phi_2(b) + eps^3 b^4 R2(x, w),   eps A0 b^2/B - F_A = eps A0 b^2 - A0 eps [f(d-b) - f(d)].
So for m >= 3 with stencil inside the inner zone:  D_B(m) = eps^2 A_2(m) + eps^3 int Lambda(R2)(x_s, w_s) M_4 ds - A0 eps Delta^4 f(d-.)
>= eps^3 (min Lambda(R2) - TFA) (A_2 >= 0 for m >= 2, a08), and with stencil inside the outer zone
D_B(m) = eps^3 int Q_O(x_s, eps) M_4 ds - A0 eps Delta^4 f(d-.) >= eps^3 (min Q_O - TFA),  Q_O = d_x^4 [x^2 (u_e - A0/B)] (fixed eps).
(iv) F_A tail (a13): f(c) = c^2 (1/B(c) - 1), c = d - b >= d/2 - 2 on the stencil (m <= d/2); Binet Taylor model of 1/B - 1 in
w = 1/c <= Wt = 2 eps/(1 - 4 eps) with remainder, Delta^4 c^-p <= p(p+1)(p+2)(p+3)(c-2)^-(p+4):  |A0 eps Delta^4 f(d-.)| <= 2.023e-11 eps^3.
(v) Slack: W_e = b omega, omega = omega0 + x omega1(w) + x^2 rho2 with omega0 = -(1 - 2/pi) constant (W0), so
Delta^2 W_e(m)/eps = int [(1-D)(2-D) omega1 + x (th+2)(th+3) rho2](x_s, w_s)(1 - |s|) ds (inner, D = w d_w), = int Q_W (1-|s|) ds with
Q_W = d_x^2 [x omega] (outer), and Delta^2 W_e(1)/eps = -2 omega1(1) + 4 omega1(1/2) + eps[-2 rho2(eps,1) + 8 rho2(2eps,1/2)].
(vi) Zones (x = eps b): outer D_B and slack: x in [XO, XE] = [0.011, 0.501], every eps in [0, 1/2001]; inner: b >= 1 with
x <= XA = 0.013 (files: b in [1, 20], w = 1/b in [0, 1/20]).  For m <= d/2 the top stencil point is (d/2 + 2) eps <= 1/2 + 2/2001
<= XE.  If (m + 2) eps > XA then (m - 2) eps > XA - 4/2001 >= XO (exact: 13/1000 - 4/2001 >= 11/1000); for the slack the same
with 2/2001.  m = 1, 2 (D_B) and m = 1 (slack) are separate certificates (a09, a11 m1).  The audit checks with Fractions: exact
coverage of [0.011, 0.501], [1, 20], [0, 1/20] by the stored box endpoints, eps_hi >= 1/2001 in every file, XA, the two overlap
inequalities, and the coverage of the a10 uniqueness domain (b-boxes [1, 30], w-boxes [0, 1/30] x [0, 0.015], x-boxes
[0.015, 0.501]).

## 7. Slack perturbation constants  [PROVED + CERTIFIED: a13_constants.py]

|W - W_e|(m) <= |Pot_delta(m)| + |G - G_4|(m, Phi\_\*) + |G_4(m, Phi\_\*) - G_4(m, Phi_e)| (1 <= m <= d/2), where
G(m,t) - G_4(m,t) = sum\_{j=5}^{7} F^(2j)(m) t^j/(2^j j!) + R7(m,t) and F^(2j)(m) t^j/(2^j j!) = (2/pi) m Ch+\_j(m) u^j.
 * |Ch+\_j| <= eps^(j-1) Cp_j, Cp_j = k_j (4j - 1 + 2j(2j-1)) + (pi/2) 16.76 (2j-2)!/(2^j j!) (b >= 1: |B_2j(b)| <= 4j - 1 + 2j(2j-1)
   from the psi bounds; |Gamma^(2j)| <= 16.76 (2j-2)!): Cp = 18.163, 16.082, 54.163, 315.61, 2565.43, 26485.7, 329912 (j = 1..7).
 * |G - G_4| <= eps^3 [(1/pi) sum\_{j=5}^{7} Cp_j U^j E1^(j-5) + Rs_n/(2 pi)] = 138.103 eps^3 (m eps <= 1/2; one-sided
   |R7(m,t)| <= (m/pi) Rs_n eps^4).
 * |d_t G_4| <= (2/(pi eps m)) sum\_{j<=4} j Cp_j eps^(j-1) U^(j-1) <= DTG4 d, DTG4 = 11.5703 (mean value theorem between Phi_e
   and Phi\_\*, both with u <= Uu <= U).
 * So max |W - W_e|/eps <= DTG4 dmax + GG4 E1^2 + Dd E1^3/8, and Delta^2 W >= eps (s_min - 4 (DTG4 dmax + GG4 E1^2 + Dd E1^3/8)).

## 8. Tail lemma and fixed point for every d >= 2001  [PROVED; evaluated by the audit]

On the Poincare-Miranda box Q (Lemma B of CONE_PROOF.md: root intervals of s.5 widened by rho), Phi(1) <= eps phi1c,
phi1c = u_max(b in [1, 1.05]) + dmax E1 + 1e-6 (the 1e-6 eps absorbs rho; checked a posteriori).  Then (Lemma R4, union bound)
   log P(E^c) <= log(2d) - 9 d/(32 phi1c),   log eps_t <= log(3d/8) + log F1(d) + log P(E^c),
   inf Hc_m' >= c := (4/pi) Fp_min/d    (Hc_m' = (2/(pi eps m)) F'(u), F' >= Fp (1 - 2x) >= Fp/d, eps m <= 1/2),
   rho := 2 eps_t/c,   sup |d_t H| <= (1/2) sup|F''| + |Bd| <= (2 pi/3) d + 8.38 + (exp-small) <= d^2,
and the needed margins are at_k-margin eps^2 > 2 rho, slack-margin eps > 4 (eps_t + rho d^2), rho <= 1e-6 eps.
Why these suffice.  The Poincare-Miranda zero Phi# lies in Q, so |Phi#(m) - Phi_e(m)| <= dmax eps^2 + rho.  (B1): at_k(Phi) >=
w_k [atk eps^2 - 2 rho] > 0 on Q (Lemma P with delta_max = dmax eps^2 + rho).  Slack of the exact process: with
W(m) = Dlt(m) - G(m, Phi#(m)) - e'\_m (|e'\_m| <= eps_t, Lemma R4), |W - W_e| <= |Pot| + |G - G_4|(m, Phi#) +
DTG4 d (dmax eps^2 + rho) + eps_t (u# <= u_e + du + rho/(eps m^2) <= Uu <= U, so the bounds of s.7 apply at Phi#), hence
Delta^2 W >= eps (s_min - pert) - 4 (eps_t + DTG4 d rho) >= eps (s_min - pert) - 4 (eps_t + rho d^2) (DTG4 = 11.6 < d).
Monotonicity: write each margin as M(d) = const + (9/(32 phi1c)) d - sum of at most 8 terms of the form log d or log(log d + c'),
so M'(d) >= 9/(32 phi1c) - 8/d > 0 for d >= 2001 (9/(32 phi1c) = 0.436); since log(eps_t + rho d^2) is the log of a sum of
exp-terms with negative derivative, the same holds for it.  Hence d = 2001 is the worst case for every d >= 2001; the audit checks
the margins there with intervals and asserts 8/2001 < 9/(32 phi1c).

## 9. G6: exact integers  [fixed; tested]

All factorials, binomials, falling factorials, Lah and Stirling numbers, Bernoulli-based coefficients and rational constants now
enter intervals as exact Python integers/Fractions with outward rounding (`a02_jets.ivq, ivfact, ivbinom, ivff, lah`):
a03 (FACT table, g_i, a_n, polygamma, Binet beta/rho, tight_1d), a04 (poch_tail, EM parts), a05 (k_j, (2j+k)!/k!, 2^j j!),
a06/a11 (Taylor-model binomials), a07 (operator coefficients, Stirling numbers by exact recursion), a08, a10 (all of Part A),
a13, t35 (Fractions; zeta(3) series).  Old code: 57/80 of the factorial intervals and 305/938 of the binomial intervals sampled
did not contain the integer (first failure 23!), and 3/49 Binet coefficients beta_jk were wrong (relative 4.7e-17, from
int(mpmath.factorial(.)) at 53 bits).  test_exact.py (logs/alld/test_exact.log): every helper and table contains the exact value
(factorials n < 200, binomials up to C(2403, 260), falling factorials, decimal constants, Lah identity, exact beta_jk, rho_jl >=
exact rational, k_j, g_i / a_n / psi^(n) against 60-digit references, grid coverage, KT, K2j, 8 pi/3 < 8.38): PASS.

## 10. G7: no float decisions  [fixed]

 * Box endpoints: exact decimal grids (`grid_boxes`), stored as exact rationals; eps ranges stored exactly (the eps-piece rounding
   of s.1.1 removed).
 * Every certified bound is stored as the exact rational value of the interval endpoint (strings); floats only for display.
 * audit_alld.py: coverage with Fractions and no tolerance (the old `cover` accepted gaps up to 1e-12); Lemma P, the slack
   perturbation and the tail/fixed-point margins in interval arithmetic; gamma, beta, A_min, GG4, DTG4, Dd, TFA, SG1, dmax, Fp_min,
   u_max all read from the logs (old: gamma = 2.7652, 206.88, A_min, 200 eps^3, 40/pi, 235.6, 1.6, 0.15, 1.9 hard-coded).
 * a10/a12: all per-box decisions are interval comparisons (they already were for most; the stored maxima/minima were nearest-
   rounded floats).

## 11. Re-run (2026-10-02) and final audit

Procedure.  The old logs are kept unchanged in logs/alld/archive_pre_rigor/ (the old scripts in backup_pre_rigor/).  After the fixes,
the whole pipeline was run once (some jobs re-launched by hand after the last fixes of s.1.7), then ONCE MORE FROM SCRATCH with the
final code by `python run_alld.py 12` (34 jobs: a01 (d = 1000, 2000), a06 x 9, a07 x 6, a08, a09, a10, a11 x 9, a12, a13, a14, t35,
test_exact; 34/34 jobs exit code 0, 828 s wall on 12 parallel jobs).  All certificate logs in logs/alld/ are from that single final
run; run_alld.log lists every job, exit code and wall time; the final audit (below) is logs/alld/audit_alld.log (copied to
logs/audit_alld_final.log).  Python 3.14.3, mpmath 1.3.0
(gmpy backend), sympy 1.14.0; iv.prec = 120 (a08: 160, t35: 240, audit: 200).

Results (all lower bounds certified for every eps in [0, 1/2001], i.e. every d >= 2001; boxes on exact decimal grids):

| certificate | range | boxes | lower bound |
|---|---|---|---|
| Q_O (outer D_B), a06 | x in [0.011, 0.013] / [0.013, 0.015] (eps split) | 8 / 8 | 7.419184 / 8.942842 |
| | [0.015, 0.0225] / [0.0225, 0.03] (eps split) | 15 / 15 | 9.119011 / 10.058640 |
| | [0.03, 0.10] / [0.10, 0.30] / [0.30, 0.40] | 28 / 40 / 20 | 9.149155 / 11.405461 / 12.696331 |
| | [0.40, 0.42] / [0.42, 0.501] | 8 / 16 | 13.925813 / 11.880465 |
| Lambda(R2) (inner D_B, x <= 0.013), a07 | b in [1, 2] / [2, 5] / [5, 20] | 20 / 30 / 60 | 6.022431 / 9.033183 / 8.922009 |
| | w = 1/b in [0.01, 0.05] / [0.001, 0.01] / [0, 0.001] | 20 / 18 / 1 | 8.237888 / 8.698330 / 8.782405 |
| slack density Delta^2 W_e/eps, a11 outer | x in [0.011, 0.0205] / [0.0205, 0.03] | 5 / 5 | 0.839377 / 0.831819 |
| | [0.03, 0.27] / [0.27, 0.501] | 24 / 23 | 0.701703 / 0.651054 |
| a11 inner | b in [1, 2] / [2, 5] / [5, 20]; w in [0, 0.05] | 20 / 30 / 30 / 10 | 0.862121 / 0.853527 / 0.837126 / 0.826098 |
| a11, m = 1 | | | 0.910044 |
| a09 | D_B(1)/eps^2, D_B(2)/eps^3 | | -2.765192, 206.884 |
| a08 | A_2(1) in [-2.75594562462218, -2.75594562462217]; A_2(m) > 0 for all m >= 2 | | |
| a10 | \|Phi\_\* - Phi_e\|/eps^2 (159 boxes, unique model root on the whole domain) | 159 | <= 6.6468e-4 (box x in [0.45, 0.46]) |
| a10/a12 | min F' (fixed-point derivative bound); u_e on b in [1, 1.05] | 159 | 0.152041; <= 0.645042 |
| a13 | GG4, DTG4, F_A tail | | 138.1028, 11.5703, 2.023e-11 |
| t35 | A_min | | 0.1054878997577386... |
| a14 | I1, I2, W0, (T/x) | | symbolic exact; numerics 1.1e-29, 6.2e-25, 4.0e-42; jets consistent at 162 points |
| test_exact | G6 | | PASS |
| a01 (prototype) | model vs certified Phi\_\* (d = 1000, 2000) | | relative 1e-18 .. 1e-34 |

Assembly (audit_alld.py): gamma = 2.765192, beta = min(7.419184, 6.022431, 206.884) - 2.03e-11 = 6.022431, P >= 0.962733394,
at_k(Phi) >= 0.1186944 w_k eps^2 for every k and every d >= 2001 (also on the whole Poincare-Miranda box); slack
Delta^2 W >= (0.651054 - 0.030900) eps = 0.620154 eps; tail lemma at d = 2001 (worst case): log P(E^c) <= -864.18,
log eps_t <= -847.31, inf Hc' >= 9.67e-5, log rho <= -837.37; log-margins 819.3 (at_k vs 2 rho), 812.7 (slack vs
4(eps_t + rho d^2)), 816.0 (rho vs 1e-6 eps).  Compared with the pre-fix audit: at_k 0.1186948 -> 0.1186944 (dmax 6.645e-4 ->
6.6468e-4), slack 0.6169 -> 0.6202 (perturbation 0.0341 -> 0.0309 with the certified GG4, DTG4), outer slack minimum 0.6509 ->
0.6511 (slightly different grid).  No conclusion changed.

ONE AUDIT FOR EVERY d >= 2.  audit_alld.py now also covers the two other regimes, read-only:
 * 2 <= d <= 200 (QD2-T1): every certs/cert_d{d}.json is checked exactly (q = 16, cells of d integers >= 1 with sum 16 d, one positive
   weight per cell, positive certified minimum weight) and must have a matching 'VERIFIED True' record of verify_cone.verify
   (160-bit intervals) in logs/verify\_\*.log (same support size, same certified bound).  `python audit_alld.py --reverify-lp 10`
   additionally re-runs verify_cone.verify on all 199 stored certificates (lp_reverify.py); done once on 2026-10-02: 199/199
   re-verified, no failure, every certified bound reproduced (logs/alld/audit_alld_reverify_lp.log, also ALL-D CERTIFIED).
 * 201 <= d <= 2000: audit_alld.py calls audit_cert_g.py unchanged (unified certificates logs/cert_g_d{d}.json of verify_cert.py,
   exact decimal strings, code hash checked; write-up RIGOR_GAUSS.md) and requires 1800/1800 OK.  (The older vg_d\*/fp_d\* files
   are no longer used.)

FINAL AUDIT OUTPUT (python audit_alld.py, logs/alld/audit_alld.log = logs/audit_alld_final.log):
```
D_B zones: outer [0.011, 0.501] min Q_O >= 7.419184;  inner (x <= 0.0130, b >= 1) min Lambda(R2) >= 6.022431
slack: min density (Delta^2 W_e / eps) >= 0.651054
m = 1, 2: D_B(1) >= -2.765192 eps^2, D_B(2) >= 206.884 eps^3;  pointwise |Phi_* - Phi_e| <= 6.6468e-04 eps^2
constants (a13): |G - G_4| <= 138.1028 eps^3, |d_t G_4| <= 11.5703 d, Dd = 235.5916, F_A tail <= 2.023e-11 eps^3;  A_min >= 0.105487899758 (t35)
Lemma P: gamma = 2.765192, beta = 6.022431, P >= 0.962733394;  at_k >= w_k eps^2 * 0.1186944
slack: Delta^2 W / eps >= 0.651054 - 0.030900 = 0.620154
tail lemma (d = 2001, decreasing in d): log P(E^c) <= -864.18, log eps_t <= -847.31;  fixed point: Fp_min >= 0.15204, Hc' >= 9.6744e-05, log rho <= -837.37
   log-margins (> 0 needed): at_k vs 2 rho 819.3, slack vs 4(eps_t + rho d^2) 812.7, rho vs 1e-6 eps 816.0
d >= 2001: CERTIFIED
2 <= d <= 200 (LP certificates, QD2-T1): 199/199 valid with a matching VERIFIED record; min d * certified weight = 0.0816
   [audit_cert_g] verify_cert.py sha256 = ff56740d15d40a07c99deb6433fb1b0f40b5a2d5b356b3ec9da0270ff1fab6a7
   [audit_cert_g] certificates 201..2000: 1800/1800 OK; missing 0 []; failed 0 []
   [audit_cert_g] margins (lower endpoints; argmin d):  d^2 min at_k = 0.0631932 (even d, d = 2000), 0.126387 (odd d, d = 1999);  d min Delta^2 W = 0.660025 (d = 201)
   [audit_cert_g]   (D): min inf Hc'/(c1min/4) = 4.00099 (d = 2000);  min log10[c_D r/(2 eps_t)] = 0.616942 (d = 201);  min log10[|face value|/(2 eps_t)] = 16.7768 (d = 201)
   [audit_cert_g]   tails: max log10 eps_t = -31.1695 (d = 201);  min log10[min Delta^2 W/(4 eps_t)] = 28.0838 (d = 201);  truncation-moment fallbacks used: 0
201 <= d <= 2000 (cert_g, audit_cert_g.py): ALL CERTIFIED
FAILS: none
ALL-D CERTIFIED (every d >= 2)
```
