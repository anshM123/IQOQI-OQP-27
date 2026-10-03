# RE-VERIFICATION REPORT on Q_2bmv/PROOF.md, sections 0-5 (Theorem 1 = explicit 2BMV density; Theorem 2 = strip inequality (*))

Scope of the re-verification: analytic check of every step of s.0-5, plus independent numerics (own code, files rf_* in this folder;
nothing in Q_2bmv/ was edited or imported).  Verdicts: OK / GAP (fixable, fix given) / WRONG.

Status: COMPLETE -- verdict in section D.

## A. Analytic checks

### 1. Lemma 1 (pencil facts) -- OK
(a) OK.  (b) OK: Im x != 0 forces <v,(P-tau)v> = 0, i.e. |Pv|^2 = tau, and then |(P-tau)v|^2 = (1-tau)^2 tau + tau^2 (1-tau)
= tau(1-tau).  (c) OK (semidefinite g - s with <v,(g-s)v> = 0 gives (g-s)v = 0, then x(P-tau)v = 0 with x != 0).  (d) OK.
(e) OK: g - s - x(P-tau) = -(P-tau)[x - (P-tau)^{-1}(g-s)], so c_tau = det(tau - P) = (tau-1)^{M-r} tau^r, which equals the
stated (-1)^M (1-tau)^{M-r} (-tau)^r; root sums Tr[(P-tau)^{-1}(g-s)] agree because (P-tau)^{-1} commutes with B and
Tr[B X P] = Tr[P X B] = 0.  (f) OK.  Cosmetic: the coefficients of p are polynomials in (s,tau) (no 1/tau needed); what
matters is c_tau != 0 on (0,1).  Numerically (rf_01, 40 digits, via determinants): leading coefficient = formula and the
x^{M-1} coefficients of p and q agree to input precision (1e-15..1e-21); q real-rooted (|Im y| <= 1e-27).

### 2. Lemma 2 (Jensen-type identity) -- OK
Antiderivative v log(1+v^-2) + 2 arctan v checked (derivative = log(1+v^-2); limits 0 and pi), so int (1/2)log(1+b^2/u^2) = pi|b|.
C = O(x^-2) at infinity needs exactly sum alpha_i = sum y_i (given).  m_L(a) = (L-a)log(L-a) + (L+a)log(L+a) - 2L, m_L'' = 2L/(L^2-a^2),
m_L(a) - m_L(0) = a^2/L + O(a^4/L^3): correct, so int_{-L}^{L} C -> 0, and C in L^1 gives int_R C = 0.

### 3. Lemma 3 (real slices) -- OK
(a) OK (above all eigenvalues U = Tr(g_d - xi P) - Tr(g - xi P) = 0).  (b) OK: int e^{aw}U = a^-2 sum_j (e^{a lambda_j} - e^{a lambda^0_j}),
and sum_j e^{a lambda^0_j} = Tr_B e^{aBgB} + e^{-a xi} Tr_P e^{aPgP}, i.e. D(a, a xi)/a^2.  (c) OK, convention checked:
with fhat(sigma) = int f e^{-i sigma w} dw (the convention of s.3), p.v. 1/(pi w) has transform -i sgn(sigma), so
H = (1/pi) p.v. int f(u)/(w-u) du has multiplier -i sgn(sigma) as stated; the pairing of lambda_j with lambda^0_j gives
(1/pi) log|prod(w - lambda_j)/prod(w - lambda^0_j)| (sign checked on a single interval).  H N_xi is in L^1 and L^2 (log
singularities, O(w^-2) decay since sum lambda_j = sum lambda^0_j).

### 4. Section 2 (entireness, growth bound, Paley-Wiener-Schwartz) -- OK
* D entire, D(0,t) = 0 and dD/da(0,t) = 0 (e^{-tP} = B + e^{-t}P): correct.  G = D/a^2 entire on C^2: correct; for joint
  holomorphy one line suffices, G(a,t) = int_0^1 (1-u) d_a^2 D(ua,t) du (cosmetic).
* Growth: with a = -i zeta_1, t = i zeta_2 one has Re a = Im zeta_1 = eta_1, Re t = -Im zeta_2 = -eta_2, so the Hermitian part of
  X = ag - tP is eta_1 g + eta_2 P: correct.  ||e^X|| <= e^{lambda_max(Re X)} (Gronwall), numerical-range argument gives
  lambda_max <= H_K(eta); the P- and B-terms are bounded via the points (mu,1), (beta,0) of K.  |D| <= 2M e^{H_K(eta)}: correct.
* |zeta_1| < 1: maximum principle on |z| = 2 gives |Ghat| <= (2M/4) e^{H_K(Im z, eta_2)} <= (M/2) e^{H_K(eta) + 3 c_K}, using
  |Im z - eta_1| <= 3 and the Lipschitz bound of H_K in eta_1 with constant c_K = max(|lmin|,|lmax|): correct.
* PWS: Hormander Thm 7.3.1 uses uhat(zeta) = u(e^{-i<x,zeta>}) and the estimate C(1+|zeta|)^N e^{H_K(Im zeta)}, K convex compact;
  here N = 0 and K is the rectangle [lmin,lmax] x [0,1].  e^{-i(zeta_1 s + zeta_2 tau)} = e^{as - t tau} for (a,t) = (-i zeta_1, i zeta_2):
  correct, so (2.1) holds on all of C^2.  The order of T is not asserted (and is not needed).  Correct use.

### 5. Section 3 (the heart) -- OK
* (3.1): phi = psihat with psi(k) = (2pi)^-2 phihat(-k), hence T(phi) = T(psihat) = That(psi) = (2pi)^-2 int That(k) phihat(-k) dk,
  with That = Ghat on R^2 (Hormander 7.1.14); Ghat bounded on R^2 (H_K(0) = 0) so the integrand is L^1.  Correct.
* k = (sigma, -sigma xi): Jacobian det[[1,0],[-xi,-sigma]] = -sigma, |.| = |sigma|; bijective onto {k_1 != 0}.  Fubini from L^1.  Correct.
* (i) Ghat(sigma, -sigma xi) = G(-i sigma, -i sigma xi) = D(a, a xi)/a^2 with a = -i sigma, = Uhat_xi(sigma) by Lemma 3(b).  Correct.
* (ii) phihat(-sigma, sigma xi) = int int phi e^{i sigma(s - xi tau)} = psihat_xi(-sigma).  Correct.
* (iii) Nhat = i sigma Uhat (U AC, compact support), so |sigma| Uhat = -i sgn(sigma) Nhat = (H N_xi)^, which is in L^2 (N_xi in L^2,
  H unitary).  Bilinear Parseval int f g = (2pi)^-1 int fhat(sigma) ghat(-sigma) (f in L^2, g in S, complex) gives the stated
  identity; w = s - xi tau is a translation for fixed tau.  Constants: (2pi)^-2 * 2pi * (1/pi) = 1/(2pi^2).  Correct.
* (iv) g - xi P - (s - xi tau) = g - s - xi(P - tau).  Correct.
* Fubini: for (s,tau) in [-S,S] x [delta,1-delta] all roots lie in |x| <= R = (||g|| + S)/delta (Lemma 1(a)); the near bound
  (log singularities, uniformly integrable) and far bound |log|p/q|| <= 2M R^2/xi^2 (uses |log|1-z| + Re z| <= |z|^2 for |z| <= 1/2 and
  equal root sums) are correct and uniform.  Then Lemma 2 applies (Lemma 1(d),(e)).  Correct.
* NUMERICAL (rf_01, own code): (1/2pi^2) int_R log|p_{s,tau}/q_{s,tau}| dxi with p, q evaluated as DETERMINANTS equals
  F(s,tau) = (1/2pi) sum|Im x_i| to 1e-20..6e-20 absolute at 15 random (s,tau), M = 3..6, scales 1..30, with 0, 2 and 4
  non-real roots (F values 0 .. 79).

### 6. Section 4 (no singular part on tau = 0, 1) -- OK
* supp(T - F) is in K minus the open strip = L_0 u L_1 (two disjoint compact segments).  Compact support => finite order; after a
  cutoff on each piece, Schwartz's structure theorem for distributions supported in a hyperplane (Hormander Thm 2.3.5) gives
  T - F = sum_{k<=N} [alpha_k(s) delta^(k)(tau) + beta_k(s) delta^(k)(tau-1)], alpha_k, beta_k in E'(R).  Correct.
* <delta^(k)(tau), e^{-t tau}> = (-1)^k (-t)^k = t^k and <delta^(k)(tau-1), e^{-t tau}> = t^k e^{-t}.  Correct.
* t -> +inf (a real): Lemma 4 gives D(a,t) -> 0; DCT for int int e^{as - t tau}F (F in L^1, the line tau = 0 is null).  A polynomial in
  t tending to 0 vanishes, so A_k(a) = 0.  t -> -inf likewise gives B_k(a) = 0.  A_k, B_k entire, zero on R\{0} => alpha_k = beta_k = 0.
  Correct.
* Lemma 4: correct (the shift to A >= 1 is exactly what makes beta_k + eps_t the top r eigenvalues of the form <Bv,(A+eps_t)Bv>;
  the max over |p| gives eps_t = ||A||^2/(t - ||A||); mu_{r+1} <= ||A|| - t by min-max with ran P).

### 7. Section 5 (Theorem 2) -- OK
* Lemma 5: series identity correct; contour: f(u + 2i) = e^{2 kappa} f(u), poles iX and i(2 - X) with residues e^{kappa X}/(i pi sin pi X)
  and -e^{kappa(2-X)}/(i pi sin pi X); int f = 2 sinh(kappa(1-X))/(sinh kappa sin pi X); continuation to |Re a| < pi correct.
* Lemma 6: K_X(Y - w) = (1/2) Re cot(pi(z - iw)/2) (checked: Re cot(A+iB) = sin 2A/(cosh 2B - cos 2A)); exp(-i pi z - pi lam) has argument
  -pi X in (-pi,0), off the cut; the series evaluation for Y < lam and the identity theorem are correct; boundary values correct
  (at x = 0, y > lam the Li2 argument is on the cut and the limit from inside the strip is used: Im Li2(r - i0) = -pi log r gives
  h = y - lam; the statement says "continuous boundary values", so this is consistent).
* (a): e^{-ia(X-1)} = e^{ag + iaP} (eigenvalues e^{a y_k} e^{ia(1-x_k)}), e^{ia(X*-1)} = e^{ag - iaP}: correct; B-terms cancel in
  D(a,-ia) - D(a,ia) = 2i sin a (rhohat - sigmahat): correct; Theorem 1 at t = -+ia, Lemma 5 with X = 1 - tau
  (sin(a tau)/sin a = int e^{-au} K_{1-tau}(u) du): correct; Tonelli for real a.  V finite/continuous/O(e^{-pi|w|}): correct
  (int K_{1-tau} = tau, sup_s F <= C/sqrt(tau(1-tau)), K_{1-tau}(u) = sin(pi tau)/(2(cosh pi u + cos pi tau)) <= C sin(pi tau) e^{-pi|u|} for |u| >= 1).
* (b): rhohat - sigmahat = O(a^2) => equal mass (M - r) and first moment (sum y_k(1-x_k) = Tr PgP); W, W' = O(e^{-pi|w|}) at both ends;
  int e^{aw}W = a^-2(rhohat - sigmahat) for real 0 < |a| < pi; analytic continuation to the imaginary axis and Fourier uniqueness give
  W = V.  Correct.  (c), (d): correct ((d) uses G(0,t) = ||BgP||_F^2 (1 - e^{-t})/t, which I re-derived from the Duhamel formula).

## B. Independent numerics (own code: rf_core.py; logs rf_*.log)

Method.  F(s,tau) from eig of J S(g - s) S (J = P - B, S = |P - tau|^{-1/2}; similar to (P-tau)^{-1}(g-s)); round-off imaginary
parts of REAL roots (measured <= 1.3e-14 x max|x|) zeroed below 1e-12 x max|x|.  Branch points of F in s located exactly as the
critical values of the Hermitian eigenvalue curves x -> spec(g - x(P - tau)) (critical points obey |x| <= ||g-s||/sqrt(tau(1-tau)),
by the Lemma 1(b) argument); s-integral by vectorised adaptive G7/K15 in theta (s = s_a + (s_b - s_a)(1 - cos theta)/2 removes the
square-root edges); tau-integral by adaptive GK21.  D(a,t) by mpmath expm (30 digits).  NOTE for anyone re-implementing: a
fixed-order Gauss rule between branch points is NOT enough -- F has complex singularities (complex zeros of the x-discriminant)
close to the real s-axis; this cost 1e-4..4e-3 errors before switching to adaptive quadrature.
* Sanity (rf_00): M = 2 closed form of Remark 4.4 reproduced to 2e-14; branch points exact.
* tau-marginal sum rule (Corollary (i)): int F(s,tau) ds = ||BgP||_F^2 to 1e-13..1e-16 at tau = 1e-4 .. 1 - 1e-4 (M = 3,4,5).
* 8(i) Theorem 1 at complex (a,t) (rf_02): M = 3,4,5, EVERY rank r = 1..M-1 (9 instances), 7 complex (a,t) each incl. purely
  imaginary a (Fourier) and t = 4i, -6 + i: worst relative error 6.8e-13.
  Stress (rf_02b): t03 configuration (spec g up to 77.4) at 6 (a,t): <= 1e-14; M = 4 with t = +-30, 60 + 5i, -45 + 10i (D ~ 1e18) and
  a = 4 - 2i: <= 4.4e-13; M = 6 (r = 3 and r = 1, scale 3): <= 3.7e-15.
* Item 5 (rf_01): back-projection integral = F to ~1e-20 (see A.5).
* Lemma 5 (rf_03b, 30 digits, tails summed exactly): int e^{-au}K_X = sin(a(1-X))/sin a to 1e-29..1e-34 for X in [0.01, 0.999] and
  complex a with |Re a| up to 3.14.  Lemma 6 (rf_03 lem): h_lam = Poisson integral to <= 6e-27 (incl. Y - lam = 38.5).
* Misc (rf_04): Lemma 4 limits converge like O(1/t) (as eps_t predicts); max F/bound = 0.61 <= 1 over 40 random instances
  (scales 1..100); F = 0 off (lmin,lmax); #non-real roots <= 2 min(r,M-r) (Remark 4.2) everywhere; equality case: defect = 0
  (1e-16) for [B,g] = 0 and ~ eps^2 > 0 when the off-diagonal block is eps.
* 8(ii)/(iii) Theorem 2, defect(lam) [mpmath: eig(B + ig) at 40 digits, Li2 with inversion] vs V(lam) [own quadrature; tau = sin^2 phi,
  kernel evaluated on exact offsets s - lam in the overflow/cancellation-free form; tau cut to [1e-13, 1 - 1e-11], omitted pieces
  bounded analytically by < 1e-14 for the lam used].  All V(lam) > 0.  |defect - V| (absolute):
    t03 (Q_fresh/t03_CM_counterexample_M3.npy: d[0] = rank 1, d[1] = gmax 25, d[2:11] unitary params, d[11:20] g params;
         spec g = -2.952, 0.597, 77.355; spec PgP = -2.234, 68.705), 13 lam in [-6, 80] (rf_03_t03a/b.log):
         <= 6e-15 for lam <= 8.5 and lam = 30, 75, 77.4, 80; 5e-14 at lam = 68.405; 1.3e-12 at lam = 68.7 (0.0047 from spec PgP:
         slice integrand ~ (1-tau)^{-1/2} down to 1 - tau ~ 1e-8; hardest case).
    spec(-40, 3, 100) M=3 r=2: <= 4.5e-14;  spec(-60, -59.5, 12, 95) M=4 r=2: <= 2.8e-13;  spec(-150, 1, 2, 150) M=4 r=1: <= 3.9e-13;
    clustered spec(-30, 0, .001, .002, 88) M=5 r=3: <= 1.2e-13  (rf_03_big.log);
    M = 6: r = 3 (scale 1): <= 3.1e-15;  r = 2 (scale 8, spec -22..26): <= 1.6e-14  (rf_03_m6.log).

## C. Finding about the author's s.6 (numerics section; outside the requested scope but relevant to the evidence)
Q_2bmv/q03_defect_check.log contains two mismatches that PROOF.md s.6 does not report: r3_2big at lam = 59.23852
(defect 35.93915282919448 vs their V 35.93669124435634, diff 2.46e-3; s.6 quotes only "spec g with 150: 3.9e-11", the other lam
of that configuration), and c4_2 (diff 4.9e-8 and 1.4e-8).  I rebuilt both configurations with identical RNG calls
(rf_05_author_outliers.py; ||BgP||^2 = 297.214138 for c4_2 reproduces their q08 value) and recomputed V with my code:
    r3_2big lam = 0.38291: diff -9.6e-14;  lam = 59.23852: defect 35.93915282919443, V 35.93915282919436, diff +7.1e-14.
    c4_2   lam = 40.00060: diff +2.4e-15;  lam = 39.70066: diff +2.8e-15.
So these were quadrature failures in q03 (grid-based transition finder / non-adaptive handling), NOT counterexamples.  The theorem
survives; but s.6 should be corrected to state these runs honestly (or replace them by the values above).

## D. Verdict

OVERALL: CORRECT.  Theorem 1 (D(a,t) = a^2 int int e^{as - t tau} F, F = (1/2pi) sum|Im x_i| >= 0) and Theorem 2 (the strip
inequality (*) for every M, with defect = int int K_{1-tau}(s - lam) F >= 0, equality iff [B,g] = 0) are proved by s.0-5 as
written.  Every item 1-7 checked: OK.  I found no WRONG step and no substantive GAP.  Signs, conventions (Fourier transform,
Hilbert multiplier -i sgn sigma, PWS supporting function, the (a,t) <-> zeta map, Jacobian |sigma|, the factor 1/(2pi^2)) are all
consistent, and the numerics confirm every identity to 1e-12..1e-20 (Theorem 1 at 82 complex (a,t) on 13 instances incl. M = 6
and the t03 configuration; Theorem 2 at 51 (instance, lam) pairs on 9 instances incl. spectra to +-150, clustered spectra, M = 6,
t03, and the author's two outlier configurations).

Cosmetic points (optional; none affects validity):
 1. s.2 Step 0: write G(a,t) = int_0^1 (1-u) d_a^2 D(ua,t) du to make joint holomorphy of D/a^2 explicit.
 2. Lemma 1(f): the coefficients of p_{s,tau} are polynomials in (s,tau); continuity of the roots uses c_tau != 0 on (0,1).
 3. Theorem 2 / Lemma 6(5): say explicitly that at x = 0, y > lam the Li2 argument lies on the cut and h is the limit from inside the
    strip (Im Li2(r - i0) = -pi log r gives h = y - lam); boundary eigenvalues occur only if B and g share an eigenvector.
 4. s.4: cite Hormander Thm 2.3.5 with its order statement (alpha_k of order <= N - k); fine as is.
 5. s.6: correct the reporting of q03 (Section C above).
Log provenance: rf_00_sanity.log was produced with the first, fixed-order Gauss rule (its 1e-4..4e-3 marginal errors for M >= 3 are
that quadrature defect, explained in B); rf_03_lem.log's Lemma 5 lines with 1e-8..1e-9 errors are tail-quadrature artefacts for
|Re a| near pi, superseded by rf_03b_lemma5.log; rf_03_big/m6 ran with the earlier V_lams (no tau = sin^2 substitution), which
was adequate there.  All other logs are from the final rf_core.py.
Not checked (outside scope): s.6-8 (Theorem 3, Lemmas 8-9, literature/priority), and the downstream claims Q-T1/Q-T2 and
"27B for all d" in s.0 Corollary (iv) and s.8.

Status: COMPLETE (2026-10-02).
