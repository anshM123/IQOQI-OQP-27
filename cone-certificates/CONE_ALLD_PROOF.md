# CONE_d for all d > 2000: proof of QD2-C2 (D_1 = 2000)

Status (2026-10-01; rigour pass and re-run 2026-10-02): PROVED, computer-assisted (interval arithmetic) -- CONE_d holds for EVERY d >= 2001
(QD2-C2 with D_1 = 2000).
Together with QD2-T1 (d <= 200) and QD2-T2 (201 <= d <= 2000), CONE_d holds for all d >= 2, i.e. QD2-C1 is PROVED (computer-assisted).
Complete proofs of every step, the code fixes of 2026-10-02 (G6, G7, constants) and the re-run: RIGOR_ALLD.md.
Reproduce: python run_alld.py 12 (all scripts, ~25 min) or python audit_alld.py ->  'ALL-D CERTIFIED' (reads logs/alld/\*.json; section 12).  Tags: PROVED (analytic), CERTIFIED (interval arithmetic, script + log),
NUMERICAL (non-rigorous evidence only).  Notation as in CONE_PROOF.md and LOG.md sections 7-8.

## 0. Setting
d >= 2001, eps = 1/d, A0 = pi/2 - 1, kappa_n(b) = d^n/db^n [b psi(b+1)], B(b) = b kappa_2(b), f(b) = b^2 (1/B(b) - 1), f(0) = 0.
F(b) = F_s(b) + F_r(b), F_s(b) = (4d/pi) b [psi(b+1) - psi(d+1)], F_r(b) = d^2 sum\_{i odd} g_i (b)\_i/(d)\_i  (g_r = sum g_i x^i).
c_j(b) = [F^(2j)(b) - F^(2j)(d-b)]/(2^j j!),  tau_m = Dlt(m) - Dlt(d-m),  Dlt = P\_{v,r} - F_r  (CONE_PROOF.md, Lemma R2).
For 1 <= m < d/2 the decoupled equation (D_m) of CONE_PROOF.md is  Hc_m(t) = tau_m,  Hc_m(t) := [H(m,t) - F(m)] - [H(d-m,t) - F(d-m)],
H the truncated Gaussian average of Lemma R4.  Phi\_\*(m) := a root of (D_m) (existence: section 8), Phi\_\*(d-m) = Phi\_\*(m), Phi\_\*(0) = 0,
and for even d, Phi\_\*(d/2) := Phi_e(d/2) (the antisymmetric equation is vacuous there; any value is admissible).
F_A(m) = A0 eps [f(m) + f(d-m) - f(d)],  D_B[X] := Delta^4 (X - F_A) (periodic centred 4th difference on Z_d).

## 1. Reduction to a smooth model plus a pointwise error (Lemma P)  [PROVED]
LEMMA P.  Let Phi = Phi_e + delta on Z_d, both symmetric with value 0 at m = 0, |delta(m)| <= delta_max.  If
   D_B[Phi_e](1) >= -gamma eps^2   and   D_B[Phi_e](m) >= beta eps^3  (2 <= m <= d/2),
then for 1 <= k <= d/2, with P := 16 A0 (A_min - 0.1446/(d-1)) and w_k = 1 (k < d/2), 1/2 (k = d/2):
   at_k(Phi) >= w_k [ (eps^2/8) (P - 4 gamma^2/(beta d (1 - 4/d))) - 2 delta_max ].
Proof.  at_k is linear and |at_k(delta)| <= w_k (2/d) sum_m |delta(m)| <= 2 w_k delta_max.  For Phi_e, QD2-L11 (with QD2-L12) gives
8 d s^4 at_k(Phi_e)/w_k = S(theta) >= P eps s^4 - 4 gamma eps^2 s^2 + beta eps^2 (1 - 4 eps) (s = sin(pi k/d)); with y = 1/s^2 >= 1,
S/(8 d s^4) = (eps^2/8)[P - 4 gamma eps y + beta eps (1 - 4 eps) y^2] >= (eps^2/8)[P - 4 gamma^2 eps/(beta (1 - 4 eps))].  []
(The m = 1 and m = d-1 terms both carry D_B(1); sum\_{m=2}^{d-2} (1 - cos m theta) = d - 2 + 2 cos theta >= d - 4.)
(0.1446/(d-1) = 2 \* 0.0723/(d-1) bounds the tail 2 sum\_{m>=d} a(m) of QD2-L12.)
NUMBERS.  A_min >= 0.105487 (QD2-L12), so P >= 0.96273 for d >= 2001.  Sufficient targets: gamma = 3, beta = 1/4, delta_max = eps^2/20 give
   at_k(Phi) >= w_k eps^2 { [0.96273 - 36/(0.25 \* 2001 \* 0.998)]/8 - 1/10 } = 0.011 w_k eps^2 > 0,
i.e.  D_B[Phi_e](1) >= -3 eps^2,  D_B[Phi_e](m) >= eps^3/4 (m >= 2),  |Phi\_\* - Phi_e| <= eps^2/20 at integers, plus the slack condition and
the tail lemma (sections 9-10).  The values actually certified are much better (section 11: gamma = 2.765192, beta = 6.0224,
delta = 6.6468e-4 eps^2, at_k >= 0.11869 w_k eps^2).  Complete proofs of Lemma P and QD2-L11: RIGOR_ALLD.md s.3; of QD2-L12 (Fejer/Polya,
A_min >= 0.1054878997577, certified by t35_polya.py, logs/alld/polya.json): RIGOR_ALLD.md s.4.

## 2. The smooth model Phi_e  [definitions]
For real b in (0, d), x = b/d, w = 1/b = eps/x, v = 1/(d-b) = eps/(1-x):
  Gamma(x, eps) := F_r(b)/d^2 = sum\_{i odd} g_i P_i(x, eps),  P_n := prod\_{k<n} (x + k eps)/(1 + k eps)  (= E X^n, X ~ Beta(b, d-b));
  F_r^(n)(b) = d^(2-n) d_x^n Gamma;  Gamma(1-x, eps) = sum_n a_n P_n(x, eps) with a_n := (-1)^n g_r^(n)(1)/n!  (X\_{d-b} = 1 - X_b in law);
  B_2j(b) := b^(2j-1) kappa_2j(b)/(2j-2)!  (Binet functions, B_2j(b) -> 1);  k_j := 2 (2j-2)!/(2^j j!).
  Ch_j(b) := (pi/2) eps^j b^(2j-1) c_j(b)
          = eps^(j-1) { k_j [B_2j(b) - (x/(1-x))^(2j-1) B_2j(d-b)] + (pi/2) x^(2j-1) d_x^2j S(x,eps)/(2^j j!) },  S := Gamma(x) - Gamma(1-x).
  Euler-Maclaurin interpolant of P\_{v,r}:  Pt(b) := d^2 [p(x) - x (p(1) - g_r(1))],  p := g_r - (eps^2/12) g_r'' + (eps^4/240) g_r''''
  (p(0) = 0 since g_r is odd; Pt(0) = 0, Pt(d) = d^2 g_r(1) as for P\_{v,r}).  tau_e(b) := [Pt - F_r](b) - [Pt - F_r](d-b),
  tauh_e := (pi/2) tau_e/b = (pi/2) [Tt + EMx]  with the cancellation-free forms (a04_regular.py):
     Tt = sum_n (g_n - a_n) Qt_n,  Qt_n := (x^n - P_n)/(eps x),  Qt\_{n+1} = Qt_n r_n - x^(n-1) n (1-x)/(1 + n eps),  Qt_0 = Qt_1 = 0;
     EMx = sum\_{k=1,2} aEM_k eps^(2k-1) [g^(2k)(x)/x - (g^(2k)(1-x) - g^(2k)(1))/x - 2 g^(2k)(1)],  aEM = (-1/12, 1/240).
  (Derivation, RIGOR_ALLD.md Prop. T: T := eps tau_e = [(p - Gamma)(x) - (p - Gamma)(1-x) + (1 - 2x)(p(1) - g_r(1))]/eps;
   g_r(x) - Gamma = sum g_n (x^n - P_n), g_r(1-x) - Gamma(1-x) = sum a_n (x^n - P_n), and the Euler-Maclaurin part, including the
   linear term, gives EMx after division by x.)
MODEL.  u_e(b) := the root in (0, 1) of  sum\_{j=1}^{4} Ch_j(b) u^j = tauh_e(b)  (unique: section 3), and  Phi_e(b) := eps b^2 u_e(b).
Equivalently Phi_e(b) is the root t of  sum\_{j<=4} c_j(b) t^j = tau_e(b)  (multiply by (2/pi) b).  Since c_j and tau_e are antisymmetric
under b -> d-b, Phi_e(d-b) = Phi_e(b).  On Z_d:  Phi_e(m) as above for 1 <= m <= d-1, Phi_e(0) := 0.
CHECK [NUMERICAL, a01_model.py, a04 test]: with J = 7 and the discrete tau the model reproduces the certified Phi\_\* (d = 1000) to 1e-18
relative; tauh_e - (pi/2) tau_m/m ~ 2e-17 at d = 1000.

## 3. Inner identities  [PROVED: RIGOR_ALLD.md s.2 (Lemmas M1-M3, Props. T, E, W, Thm. I); CHECKED: a14_identities.py]
At fixed b, as eps -> 0 (x = eps b):  B_2j(d-b) = 1 + O(eps^2), x/(1-x) = eps b + O(eps^2), S'' = g_r''(x) - g_r''(1-x) + O(eps),
g_r''(0) = 0, g_r''(1) = 2 - 4/pi, g_r'''(1) = 4/pi, g_3 = pi/36.  Hence
  Ch_1 = B(b) - (pi/2) eps b + O(eps^2),  Ch_2 = eps b^3 kappa_4(b)/4 + O(eps^2),  Ch_j = O(eps^2) (j >= 3),
  tauh_e = A0 + eps (pi/2)[-(1 + pi/12) b + t1c] + O(eps^2),  t1c = -(2/3 + 5pi/72 + 1/(3pi))
(Heuristic route via the discrete tau: Dlt(b) = eps[-3 g_3 b^2 - (5/2) g_3 b + g_r''(1) b/12] + O(eps^2), Dlt(d-b) = -(g_r''(1)/2) b
 + eps[(g_r''(1)/2)(b^2 + b) + (g_r'''(1)/6)(3b^2 + 2b) - (b/12)(g_r''(1) - g_r'''(1))] + O(eps^2).  The PROOF works with the model
 itself, tauh_e = (pi/2)(Tt + EMx), Ch_j as defined above: RIGOR_ALLD.md Prop. E.)
Therefore u_e(b) = U0 + eps b U1 + O(eps^2) with
  (I1)  b^2 U0 = A0 b^2/B(b) = phi_1(b),   (I2)  b^3 U1 = phi_2(b)  (the explicit function of QD2-L10, a08_A2.py).
Checks (a14_identities.py, logs/alld/identities.json): exact sympy derivation of the expansions and of b^3 U1 - phi_2 = 0; an
independent 90-digit implementation (model solved at x = 1e-5..8e-5, 17 values of b in [1, 1000]) gives I1 to 1e-29 and I2 to
6e-25 relative; interval jets at x = 0 contain A0/B and phi_2/b^3 at 161 values of b and at w = 0; omega(0, w) = -(1 - 2/pi).

## 4. Exact decomposition of D_B  [PROVED; details and the zone bookkeeping: RIGOR_ALLD.md s.6]
Write u_e(x, w) (x = eps b, w = 1/b) and Taylor-expand in x at fixed w:  u_e = U0(w) + x U1(w) + x^2 R2(x, w).  Then
  Phi_e(b) = eps A0 b^2/B(b) + eps^2 phi_2(b) + eps^3 b^4 R2(x, w),  and  eps A0 b^2/B(b) = eps A0 b^2 + A0 eps f(b),
so, since Delta^4 kills the quadratic eps A0 b^2 (also with the even extension at m = 1, 2):
  D_B[Phi_e](m) = eps^2 A_2(m) + eps^3 Delta^4[b^4 R2](m) - A0 eps Delta^4[f(d-b)](m),     A_2 := Delta^4 phi_2 (even extension).
For m >= 3 the stencil lies in [1, d-1] and  Delta^4 g(m) = int\_{-2}^{2} g''''(m+s) M_4(s) ds  (M_4 = cardinal B-spline, >= 0, mass 1), and
  d_b^4 [b^4 R2] = Lambda(R2),  Lambda := (th+1)(th+2)(th+3)(th+4),  th := x d_x - w d_w   (d_b = w th at fixed eps).
OUTER FORM (no x-expansion, used for x >= 0.011):  eps^(-3) Delta^4[Phi_e - eps A0 b^2/B](m) = int Q_O(x_s, eps) M_4(s) ds,
  Q_O := d_x^4 [x^2 (u_e - A0/B(1/w))] at fixed eps;  and Delta^4[eps A0 b^2/B - F_A] = -A0 eps Delta^4 f(d-b).

## 5. Outer zone  x in [0.011, 0.501]  [CERTIFIED: a06_zoneO.py; logs/alld/zoneO\_\*.json]
For every box x in [x_lo, x_hi] and every eps in [0, 1/2001] (all d >= 2001; eps = 0 included), Q_O(x, eps) is enclosed by a Taylor
model: thin centre jets (x_c, eps_c) up to order 4+K-1 in x and 1 in eps, x-remainder of order K = 3 from jets over (x-box, eps_c), and
the eps^2 remainder from jets over the full box; model root by Krawczyk, root jets by implicit differentiation; for x < 0.03 the eps-range
is split geometrically (w = eps/x then moves little per piece; cut points are 120-bit values reaching 1/2001 exactly -- the earlier
53-bit cut points stopped 1.6e-20 below 1/2001, RIGOR_ALLD.md s.1); for x_hi > 0.4201 the remainder jets use the box enlarged to [x_lo, 1/2] and
the exactly antisymmetric coefficients are divided by (1-2x) (coefficient shift, valid since Ch_j(1/2) = tauh_e(1/2) = 0 exactly).
RESULT (re-run 2026-10-02, RIGOR_ALLD.md s.11): Q_O >= 9.149 on [0.03, 0.501] (pieces: [0.03,0.10] 9.149, [0.10,0.30] 11.405,
[0.30,0.40] 12.696, [0.40,0.42] 13.926, [0.42,0.501] 11.880, [0.011,0.013] 7.419, [0.013,0.015] 8.943, [0.015,0.0225] 9.119,
[0.0225,0.03] 10.059 (eps split below 0.03)).  Overall: Q_O >= 7.419184 on [0.011, 0.501].
Hence for every stencil inside x >= 0.011:  D_B[Phi_e](m) = eps^3 int Q_O M_4 - A0 eps Delta^4 f(d-b) >= eps^3 (min Q_O - 2.03e-11)
(F_A tail term certified by a13_constants.py).

## 6. Inner zone  x <= x_A = 0.013, b >= 1  [CERTIFIED: a07_zoneI.py; logs/alld/zoneI\_\*.json (each box records its x-range)]
Lambda(R2) = lam2(U2)(w) + x Lambda'(R3) (section 4), lam2 = (1-D)(2-D)(3-D)(4-D) = 24 - 24D + 12D^2 - 4D^3 + D^4 (D = w d_w) acting on
U2(w) = d_x^2 u_e(0,w)/2 (thin x = 0, Taylor model of order K = 3 in w), and x Lambda'(R3) in [0, x1] (1/6) range(Lambda'(d_x^3 u_e)).
Boxes: b in [1,2] step 0.05, [2,5] step 0.1, [5,20] step 0.25, then w in [0.01,0.05] step 0.002, [0.001,0.01] step 0.0005, [0, 0.001].
RESULT: Lambda(R2) >= 6.022 (b in [1,2]), >= 9.033 ([2,5]), >= 8.922 ([5,20]), >= 8.238 (w in [0.01,0.05]), >= 8.698 ([0.001,0.01]),
>= 8.782 (w in [0, 0.001], i.e. b >= 1000).  Overall: Lambda(R2) >= 6.022.  lim\_{w,x -> 0} Lambda(R2) = 9.8259.
Since A_2(m) >= 0 (m >= 2, a08), for 3 <= m with stencil in x <= 0.013:  D_B(m) >= eps^3 (min Lambda(R2) - 2.03e-11) >= 6.0224 eps^3.

## 7. m = 1, 2  [CERTIFIED: a09_smallm.py; logs/alld/smallm.json]
D_B(1) = 7X(1) - 4X(2) + X(3), D_B(2) = -4X(1) + 6X(2) - 4X(3) + X(4) (X(-1) = X(1), X(0) = 0), with X(b) = eps A0 b^2 + eps^2 phi_2(b)
+ eps^3 b^4 R2(eps b, 1/b) - A0 eps [f(d-b) - f(d)].  A_2(1) = -2.7559456246, A_2(2) = 0.0994231923; the eps^3 brackets lie in
[17.6, 18.5] and [7.9, 10.9].  For all d >= 2001:  D_B(1) >= -2.765192 eps^2  and  D_B(2) >= 206.884 eps^3  (the F_A term uses
|E| <= C6/b^6 at b = d - j >= 1997, certified by t35 for b >= 1000: C6 = 0.408788).

## 8. Pointwise lemma: |Phi\_\*(m) - Phi_e(m)| <= 6.6468e-4 eps^2  [CERTIFIED: a10_pointwise.py; logs/alld/pointwise.json;
## every constant derived in RIGOR_ALLD.md s.5]
Scaled exact equation (D_m) (u = t/(eps m^2), multiplied by (pi/2)/m): F(u) := sum\_{j=1}^{7} Ch_j(m) u^j + Rs(u) - tauh_m = 0, where
Rs = (pi/2)[R7(m,t) - R7(d-m,t)]/m is the Gaussian remainder beyond order 7 including the truncation |Z| < 3m/4 (Lemma R4), and
tauh_m - tauh_e(m) = Es = -(pi/2)[Pot_delta(m) - Pot_delta(d-m)]/m, Pot_delta = P\_{v,r} - Pt (discrete potential of the Euler-Maclaurin
defect delta = g_r''(k/d) - Delta^2 Pt(k), zero boundary values).  The model gives F(u_e) = sum\_{j=5}^{7} Ch_j u_e^j + Rs(u_e) - Es.
Analytic bounds (eps <= 1/2001, u <= 0.7):
  |g_r^(n)| <= n! MA/0.9^n on [0,1] (MA = 4.0032 >= sum |g_i| 1.9^i)  =>  |delta| <= Dd eps^6, |Pot_delta| <= Dd eps^4/8, |Es| <= (pi/8) Dd eps^4/m;
  |psi^(k)(z)| <= (k-1)!/z^k + k!/z^(k+1);  |F_r^(n)| <= 16.76 (n-2)! d^(2-n) (since 0 <= d_x^n P_i <= n! C(i,n) on [0,1] and
  |g_i| <= 8.38/(2^i i(i-1)));  (c+1)^15 |kappa_16(c)| <= KT (c >= 1/4)  =>  |Rs| <= Rs_n eps^4, |dRs/du| <= dRs_n eps^4 with
  Rs_n = 2.254173, dRs_n = 25.76198 (inner), Rs_nO = 0.0015363, dRs_nO = 0.017557 (outer, c813 = 1 - 10 sqrt(0.7/2001) = 0.8129638),
  with the F_r part of F^(16) and every exponentially small term (far window, truncation, boundary terms of d/dt H) bounded
  explicitly (<= 5e-136 resp. 2e-330); Dd = 235.5917 (EM series with a geometric tail bound).
Box scans (value enclosures of Ch'\_j = Ch_j/eps^(j-1), j <= 7, and of u_e by Krawczyk) over b in [1,30] x eps in [0, eps1], b >= 30 with
x <= 0.015 (w-boxes), and x in [0.015, 0.501] x eps in [0, eps1] (x >= 0.45: all coefficients divided by (1-2x); then |Es^\*|, |Rs^\*| <= d |.|);
159 boxes, exact grids; the union covers the whole model domain (checked by audit_alld.py).
On each box: du <= K eps^4 with K = [sum\_{j=5}^{7} |Ch'\_j| eps1^(j-5) U^j + Rs_n + Es_n]/F'\_min, F'\_min = Ch_1 - sum\_{j>=2} j|Ch_j| U^(j-1)
- dRs_n eps^4 > 0 (U replaced by the box's root bound + 1e-3), and |Phi\_\* - Phi_e| = eps m^2 du <= (K x_hi^2 eps1) eps^2 (resp.
(K b_hi^2 eps1^3) eps^2 for b-boxes); dmax := the maximum of these ratios over all boxes is used by Lemma P and the slack.
The same scan certifies that the model root is unique in (0,1): Ch_1 - 2|Ch_2| - 3|Ch_3| - 4|Ch_4| > 0, tauh_e > 0, sum\_{j<=4} Ch_j > tauh_e
(divided versions near x = 1/2), so u_e is a well-defined C^K function (K ~ 1000, RIGOR_ALLD.md Lemma M1) and the jets of
sections 5-6 enclose its derivatives (each Krawczyk enclosure is checked to contain u_e: a05 implicit_root_jet, a10 (U4)).
Existence of Phi\_\*(m): by the IVT on [u_e - du, u_e + du] (F continuous, F' >= F'\_min there).  RESULT: all 159 boxes ok;
max |Phi\_\* - Phi_e|/eps^2 <= 6.6468e-4 (box x in [0.45, 0.46]); u_e <= 0.645042 on b in [1, 1.05]; min F' >= 0.152041.

## 9. Slack: Delta^2 W > 0  [CERTIFIED: a11_slack.py; logs/alld/slackW\_\*.json, slack_m1.json]
For the decoupled solution, the antisymmetric equation gives the one-sided form W(m) = Dlt(m) - G(m, Phi\_\*(m)) (1 <= m <= d/2),
W(d-m) = W(m), W(0) = 0, where G(b,t) = H(b,t) - F(b).  Model: W_e(b) := Dlt_e(b) - G_4(b, Phi_e(b)) = b omega (a11 docstring), symmetric
(by the model equation), with omega(0, w) = -(1 - 2/pi) EXACTLY (so the O(1) part of W_e is linear and Delta^2 W_e = O(eps);
proof RIGOR_ALLD.md Prop. W, checks a14).
  Delta^2 W_e(m)/eps = int L_W(x_s,w_s) M_2(s) ds (inner, m >= 2),  = int Q_W(x_s,eps) M_2(s) ds (outer),
  Delta^2 W_e(1)/eps = -2 omega1(1) + 4 omega1(1/2) + O(eps)  (explicit enclosure).
Perturbation: |W - W_e|(m) <= |Pot_delta| + |G - G_4|(m, Phi\_\*) + |d_t G_4| |Phi\_\* - Phi_e| = O(eps^3) (orders j = 5..7 bounded by
|Ch+\_j| <= eps^(j-1)[k_j (4j-1 + 2j(2j-1)) + (pi/2) 16.76 (2j-2)!/(2^j j!)], the order-16 remainder as in section 8, and |Phi\_\* - Phi_e| <=
K eps^5 m^2 from section 8; CERTIFIED (a13_constants.py, logs/alld/constants.json): |G - G_4| <= 138.103 eps^3 (137.744 from orders
5..7 + 0.359 from R7) and |d_t G_4| <= 11.5703 d, so |d_t G_4| |Phi\_\* - Phi_e| <= 11.5703 \* 6.6468e-4 eps; RIGOR_ALLD.md s.7),
so Delta^2 W(m) >= eps (min density) - 4 max |W - W_e| > 0 with a margin of order eps.

## 10. Tail / fixed-point (Lemma B) margins for all d >= 2001  [PROVED, elementary + a12_fp_alld.py]
[Note: the constants in the next four lines (0.66 eps, 0.426 d, at_k >= 0.09 eps^2) are from an earlier stage. They remain
valid but are weaker than the certified values used now, which are in the paper (Proposition prop:regimeIII) and in
logs/alld/audit_alld.log: Phi(1) <= 0.6451 eps, log P(E^c) <= -864 at d = 2001 (decreasing in d), and
at_k >= 0.1186944 w_k eps^2.]
Phi\_\*(1) <= Phi_e(1) + eps^2/20 <= 0.66 eps (u_e <= 0.65 on b in [1, 1.05], section 8 scan), hence
P(E^c) <= 2d exp(-9/(32 Phi(1))) <= 2d exp(-0.426 d),  eps_tail <= (3d/8) sup|F'| P(E^c),  sup|F'| <= (4d/pi)(H_d + 1) + 8d,
r = 8 eps_tail/min c_1 with min\_{m<d/2} c_1(m) >= (4/pi) Ch\*\_min/d (Ch_1 = (1-2x) Ch\*\_1, d - 2m >= 1).  For d >= 2001 these are
< 10^(-300); the margins of Lemma P (at_k >= 0.09 eps^2) and of section 9 (Delta^2 W >= c eps) exceed 2r and 4(r sup|F''| + eps_tail).
FIXED POINT (CONE_PROOF.md, Lemma B; added 2026-10-01 by the main session).  The step from the decoupled equations (D_m) to the exact
equations is Poincare-Miranda on the IVT intervals of section 8, widened by rho.  It needs a certified lower bound for the derivative
of Hc_m on the boxes; a12_fp_alld.py records Fp >= 0.152041 (min over the 159 a10 boxes, logs/alld/fp_alld.json), i.e.
F'(u) >= 0.152 on [0, U + 1e-3] (F'(u)/(1 - 2x) >= 0.152 in the half-boxes), hence Hc_m' >= (2/(pi eps m)) 0.152/d >= 0.19/d, and
rho = 2 eps_tail d/0.19 <= 10^(-363) (d >= 2001, decreasing in d).  The at_k and slack margins absorb 2 rho and 4(eps_tail + rho d^2)
(|d_t H| <= (1/2) sup|F''| + |Bd| <= (2 pi/3) d + 8.38 + exp-small <= d^2).  Monotonicity in d of every margin: RIGOR_ALLD.md s.8.
audit_alld.py checks this in interval arithmetic; the same single run also audits 2 <= d <= 200 (LP certificates) and 201 <= d <= 2000
(it calls audit_cert_g.py on the unified certificates logs/cert_g_d{d}.json of verify_cert.py).

## 11. Assembly: CONE_d for every d >= 2001  [PROVED, computer-assisted; audit_alld.py]
Fix d >= 2001.  (1) Section 8: for 1 <= m < d/2 the decoupled equation (D_m) has a root Phi\_\*(m) with |Phi\_\*(m) - Phi_e(m)| <=
6.6468e-4 eps^2; set Phi\_\*(d-m) = Phi\_\*(m), Phi\_\*(0) = 0, Phi\_\*(d/2) = Phi_e(d/2).  (2) Sections 4-7 and A_2 >= 0 (a08):
D_B[Phi_e](1) >= -2.765192 eps^2 and D_B[Phi_e](m) >= beta eps^3 for 2 <= m <= d/2 with beta = min(inner 6.022431, outer 7.419184,
m = 2: 206.884) - (F_A tail 2.03e-11) = 6.022431.  (3) Lemma P with gamma = 2.765192, beta = 6.022431, P >= 0.962733394 (A_min from t35):
at_k >= w_k eps^2 [(P - 4 gamma^2/(beta d (1-4/d)))/8 - 2 \* 6.6468e-4] >= 0.1186944 w_k eps^2 > 0 for all k (on the whole Poincare-
Miranda box, up to 2 rho).  (4) Section 9: Delta^2 W(m) >= (0.651054 - 0.030900) eps = 0.620154 eps for all m.  (5) Section 10:
tail and fixed-point margins hold with log-margins > 800 (d = 2001 is the worst case, RIGOR_ALLD.md s.8).  Hence, by Lemma B, the
Gaussian-modulated Dirichlet process of CONE_PROOF.md (Lemmas R1-R4) satisfies (i) and (ii) of Lemma R1, i.e. CONE_d holds.  With
QD2-T1 (2 <= d <= 200) and QD2-T2 (201 <= d <= 2000):  CONE_d HOLDS FOR EVERY d >= 2 (QD2-C1).
SLACK RESULTS (density Delta^2 W_e/eps, lower bounds): outer [0.011,0.0205] 0.8394, [0.0205,0.03] 0.8318 (eps split), [0.03,0.27] 0.7017,
[0.27,0.501] 0.6511; inner b in [1,2] 0.8621, [2,5] 0.8535, [5,20] 0.8371, w in [0,0.05] 0.8261; m = 1: 0.9100.  Perturbation
4 max|W - W_e|/eps <= 4 (11.5703 \* 6.6468e-4 + 138.103/2001^2 + 235.59/(8 \* 2001^3)) = 0.0309.  Hence Delta^2 W(m) >= 0.620 eps.

## 12. Files, scripts, logs
Scripts (QD2/): a02_jets.py (interval jets; exact-integer helpers ivq/ivfact/ivbinom/ivff, exact grids), a03_special.py (g_i, a_n,
polygamma, Binet), a04_regular.py (Pochhammer sums, Euler-Maclaurin parts, rigorous tails), a05_model.py (model coefficients, Krawczyk
root, implicit-root jets), a06_zoneO.py (outer D_B), a07_zoneI.py (inner D_B), a08_A2.py (A_2), a09_smallm.py (m = 1, 2),
a10_pointwise.py (pointwise lemma, all analytic constants, root uniqueness), a11_slack.py (slack), a12_fp_alld.py (fixed-point
derivative bound), a13_constants.py (|G - G_4|, |d_t G_4|, F_A tail), a14_identities.py (I1, I2, W0, T/x: sympy, independent
numerics, jets), t35_polya.py (QD2-L12, A_min), test_exact.py (G6 tests), run_alld.py (driver), audit_alld.py (exact coverage + all
margins; also audits d <= 200 and, via audit_cert_g.py, 201..2000), lp_reverify.py (optional re-verification of the d <= 200 LP
certificates), a01_model.py (non-rigorous prototype, used only for cross-checks).
Logs (logs/alld/, one run of run_alld.py, 2026-10-02): zoneO\_{0a1,0a2,0b1,0b2,1,2,3a,3b,3c}, zoneI\_{b1,b2,b3,w1,w2,w3},
slackW\_{O0a,O0b,O1a,O1b,I1,I2a,I2b,I3}, slack_m1, A2, smallm, pointwise, fp_alld, constants, polya, identities (.json, exact rational
bounds as strings) and the .log of every job; test_exact.log, a01_model_d{1000,2000}.log, run_alld.log, audit_alld.log.
Superseded logs (before the fixes of RIGOR_ALLD.md): logs/alld/archive_pre_rigor/.
NUMERICAL cross-check (a01 prototype, exact discrete tau, Gaussian order 7, d = 4000): d^2 D_B(1) = -2.7514; d^3 D_B(m) = 407.1, 47.1,
15.2, 11.0, 9.93, 9.90, 10.23, 13.39 for m = 2, 3, 4, 5, 8, 20, 100, 1000 -- consistent with the certified lower bounds.
Scope note: the reduction CONE_d => (\*) => F <= F_DKZ is QD2-L1/R1; Lemmas R1-R4 and Lemma B (fixed point) of CONE_PROOF.md are used;
their margin conditions are verified in section 10 for all d >= 2001 and by verify_cert.py / audit_cert_g.py for 201 <= d <= 2000.

REMARK (what exactly is proved vs. the original formulation of QD2-C2).  The 4th-difference bounds D_B(1) >= -2.765192 eps^2 and
D_B(m) >= 6.0224 eps^3 are certified for the smooth model Phi_e; the actual decoupled solution satisfies |Phi\_\* - Phi_e| <= 6.6468e-4 eps^2
pointwise, and this perturbation is absorbed at the level of the variogram coefficients (Lemma P: |at_k(delta)| <= 2 max|delta|), not of
4th differences.  So the literal pointwise statement "Delta^4(Phi\_\* - F_A)(m) >= eps^3" is not claimed (it is not needed): what is proved is
the conclusion QD2-C2 was designed for, namely at_k(Phi\_\*) >= 0.11869 w_k eps^2 > 0 for all k, the slack Delta^2 W > 0, and the tail margins,
for every d >= 2001; hence CONE_d.
