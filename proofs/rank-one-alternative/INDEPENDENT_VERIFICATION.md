# Re-verification report on Q_r1/PROOF.md  ((*) for rank-one B, all M; corank <= 3; all M <= 5)

Re-verification scripts: Q_r1/rv_*.py (logs rv_*.log).  PROOF.md was not edited.
Verdict scale per item: OK / GAP (fixable) / WRONG (counterexample).

OVERALL VERDICT: CORRECT WITH FIXABLE GAPS.  I found no mathematical error and no counterexample.  Every step
was checked by hand, and every lemma was checked numerically, including extreme regimes and 50-60 digit
arithmetic.  The gaps are expository: an unstated order of limits in Lemma 6, a one-line continuity
justification in Cor. 5.1, and small wording points.  None changes a statement.  The list with fixes is at the end.
Verdicts: F1-F5 OK | 1 OK | 2 OK | 3 OK | 4 OK | 5 OK | 6 OK (order of limits) | 7 OK | 8 OK (Cor 5.1 gap) |
9 OK | 10 no violation.

## Preliminary remarks
- PROOF.md cites `verify_r1.py` / `verify_r1.log` as cross-checks; neither file exists in Q_r1 (only r01..r08).
  Documentation gap: remove the citation or add the files.

## Standing facts (F1)-(F5)  -- OK
Checked against the definition of h at 30-40 digits (rv_01_lemma12.py / .log): |h - def| <= 2e-15, (F2) err 1e-15,
(F4) h_x - i h_y = phi' err 2e-15, (F3) boundary values at x = 0+ (both signs of y) and x = 1 agree to 12 digits,
(F5) min_y (h - p y) = Phi_c(x,p) to 9e-42 (60 random (x,p)), and h - p y - Phi_c >= 0 on a y-grid.
Minor: (F3) says "phi'(x+iy) = O(1 + |y|)"; false near nu = 0 (log singularity).  Only used for |y| = R large in
Lemma 6, where it is true.  Wording fix: "O(1 + |y|) for |nu| >= 1".

## Item 1. Lemma 1 (a),(b),(c) -- OK
Analytic check: all sign conventions are right.  A = g - i s vv* = -i(s vv* + ig), zeta_k = y_k - i x_k;
(zeta - t)/(conj zeta - t) = conj(w)/w with w = (y-t) + i x, arg w = pi/2 + arctan((t-y)/x) = pi*omega(t;nu): so
R(t) = exp(-2 pi i F(t)); Cramer gives det(PgP - t)|ranP = G(t) det(g - t).  (c): |R| > 1 on the upper half plane,
G Herglotz, G = -1/z + O(z^-2); the numerator N(z) = prod(conj zeta - z) + prod(zeta - z) has degree M and its M
roots are the M distinct real points F in Z + 1/2, so N = 2 prod(s_i - z) and det(g - isvv* - z) = prod(zeta_k - z)
exactly (multiplicities included).  Explicit residues: p_i = 1/(pi s F'(s_i)).
Numerics (rv_01): 400 random (g, v, s), s in (0.02, 1], scales 0.1-300, clustered spectra: |gamma - spec PgP|/scale
<= 4e-11, |R(t) - exp(-2 pi i F(t))| <= 1.3e-12, |R - (1-isG)/(1+isG)| <= 1.2e-13; converse construction on 300
random nu (incl. s < 1, clustered y, x_k ratios up to 1e6): p_i > 0, |sum p_i - 1| <= 1e-13, spec matches nu to 1e-12.
Remark (not an error): "all x_k > 0" already forces v cyclic for g (an eigenvalue with x = 0 has an eigenvector z
with <v,z> = 0, hence g z = y z), so the "General case" paragraph of (b) is vacuous.

## Item 2. Lemma 2 (trace identity) -- OK
Algebra checked (sum x y = (1/2) Im Tr X^2 = s<v,gv>).  The extension to configurations with atoms is fine via the
atom argument (an atom contributes y to both sides; Lemma 4's multiset identity), with no circularity.
Numerics (rv_01): 400 general configurations (30% atoms x = 0, coincident y, s < 1): error <= 2.8e-12 x scale.

## Item 3. Lemma 3 (easy cases) -- OK
(i) uses only h >= (1-x)y_+ (F2) and 1 - x_k - alpha x_k = 1 - x_k/s >= 0 (x_k <= s in C_M(s)); (ii) is (i) applied to
conj(nu) after the exact rewrite T = sum h(conj nu_k) - alpha S_- (Lemma 2 + F2).  Both correct.
Numerics (rv_02_lemma345.py/.log): 2995 configurations with all gamma <= 0: min T = 0; 2997 with all gamma >= 0:
min T = -1.1e-12 (rounding); the rewrite identity holds to 7e-13 x scale; sum h >= alpha S_+ on all 6000.

## Item 4. Lemma 4 (boundary points) -- OK
The multiset identity min(floor F, M-1) = min(floor F', M-2) + 1{t >= y_m} is correct: F' < M-1 everywhere
(strictly increasing, mass M-1), so the left min is floor F' for t < y_m and floor F' + 1 <= M-1 for t >= y_m.
Numerics (rv_02): 0 failures on 165,248 t-values (including t exactly at atoms and coincident atoms);
|T(nu) - T(nu')| <= 1.2e-11; x_m = 1, s = 1 gives |T| <= 7e-15.

## Item 5. Lemma 5 (near-boundary bound) -- OK (one unstated condition)
(a) |h_x| <= R + 1 + (1/pi) log(1/t) is right; integrating gives eta(R+1) + (eta/pi)(log(1/eta) + 1), which is
    <= eta(R + 1 + log(1/eta)) only when log(1/eta) >= 1/(pi-1), i.e. eta <= 0.627.  True since eta <= s/2 <= 1/2,
    but the proof should say so.
(b) correct: |S'| <= s'R <= sR, so (eta/(s s')) s R = eta R/s' <= 2 eta R/s, total <= 3 eta R/s <= 4 eta R/s.
(c) correct, constant included (1 + (2R+1)^2 <= 4(R+1)^2, s' >= s/2).  The sqrt(eta) is genuine: if an integer level
    of F'' sits at y_m, the quantile moves by about sqrt(eta/(pi (F'')')), where (F'')' is the density of F''.
Numerics (rv_02): 4000 random + structured cases (integer level of F'' placed at y_m) and 60 Nelder-Mead runs
maximising |T(nu) - T(nu^0)|/E(eta): max ratio 0.030.  Part (a) alone reaches 0.99 of its bound (y_m = R, where
h ~ (1-x) y), still valid; parts (b), (c) <= 0.41, 0.03.

## Item 6. Lemma 6 (zero count <= J+1) -- OK (write-up should fix the order of limits)
Bookkeeping redone independently (counterclockwise boundary of {delta < x < 1, |y| < R}):
  bottom (x: delta -> 1, f ~ (eps pi/2) e^{pi R} e^{i pi x}): +pi;  right (x = 1: Im f = (1/pi) sum c_j/(1+(y-g_j)^2) + a > 0,
  Re f -> -oo at both ends; needs J >= 1 or a > 0): 0;  top (f ~ (eps pi/2) e^{pi R} e^{-i pi x}): +pi;
  left, y: R -> 0+ (f -> r(y) - i; pole passages: 1/(u - i delta) sweeps the upper half plane): 0 + J pi + (J-1) pi + pi
  = 2J pi;  corner: 0;  left, y: 0- -> -R (f real-analytic across, passing right of a real zero of order p: -p pi): -Z pi.
  Total (2J + 2 - Z) pi, so #zeros(S) = J + 1 - Z/2 <= J + 1, Z even.  I agree with every sign.
Precision needed in the write-up (not an error): the limits must be taken as  R fixed -> corner radius rho and pole
radii fixed -> delta -> 0 -> rho -> 0 -> R -> oo.  Both thresholds can be astronomically small:
  - the corner contributes 0 (and [g_1, 0+] contributes pi) only once rho << exp(pi C0), where
    C0 = -(1/pi) sum c_j/g_j - mu + eps pi is the value at 0 of f(nu) + (1/pi) log(i pi nu); this is ~e^{-600} when
    sum c_j/g_j ~ 600.  Observed (c_1/g_1 = 62, exp(pi C0) ~ 3e-26): with the left side at x = 1e-8..1e-14 the upper-left
    side gives 3.02 pi instead of 2J pi = 4 pi and the lower-left side -1.02 pi instead of -2 pi (the zero of r_- at
    y ~ -1e-26 is not resolved); the totals agree, as they must;
  - each pole carries one zero of f in S at nu ~ i g_j + (c_j/pi)(1 - i r_j)/(1 + r_j^2) (r_j = Re of the rest of f at i g_j),
    i.e. at x ~ c_j/(pi r_j^2); with r_j ~ eps cosh(pi g_j) this was observed at x = 2e-30 (case below).  A contour at
    delta = 1e-12 misses it; the proof's delta -> 0 limit is correct.
Numerics (rv_03_lemma6.py; logs rv_03_lemma6_{A,B,C}.log): 1800 instances in 12 regimes -- random; first pole at
1e-6..1e-2; c_j in [1e2,1e5]; c_j in [1e-7,1e-3]; c_j spread over 11 decades; |mu| up to 1e4 (both signs); a up to 1e3;
eps down to 1e-14; poles clustered at spacing 1e-6; mu << 0 with a > 0; poles far up (g ~ 16) -- J = 1..8.
  (A) adaptive winding number with the left side at x = 1e-100 evaluated in exact local coordinates (u = y - g_j near
      poles; a lower-left contour at x = 1e-8, which can only exclude axis zeros): count <= J + 1 in ALL 1800 cases;
      count = J + 1 in 415 cases (the bound is sharp), J - 1 in 5.
  (B) the exact formula count = J + 1 - Z/2, with Z = number of sign changes of r_- on (-R,0) counted independently
      (plus the forced crossing in (-1e-12, 0) when r_-(-1e-12) < 0): holds in all 1800 cases.
  (C) Newton from ~1e4 grid starts + local Newton in w = nu - i g_j (finds the pole-attached zeros at x ~ 1e-30):
      never more zeros in S than (A).  The 23 apparent excesses were zeros of r_- ON the axis: re-solved at 50 digits
      they have |Re| <= 3e-54 and r_- changes sign there (rv_03b_newton_extra.py / .log).

## Item 7. Lemma 7 (interior local minima) -- OK
- Majorant: for j not in I, -(gamma_j)_+ <= 0; gamma_j > 0 persists nearby for j in I; if S(nu) > 0 then S > 0 nearby
  (a = alpha), if S(nu) <= 0 then -alpha S_+ <= 0 = -a S.  So T_eps <= T~ near nu with equality at nu: correct.
  Numerics (rv_04_lemma7.py/.log, 60 digits): 0 violations in 60 random perturbations; T~ - T_eps = 0 exactly at nu.
- Lagrange / bookkeeping: grad_{nu_k} gamma_j = -grad omega(gamma_j; nu_k)/F'(gamma_j) (IFT, F' > 0 as all x_k > 0);
  holomorphic derivatives phi', pi cos(pi z), (i/pi)/(z - i gamma), -iz (for xy = Re(-i z^2/2)), 1 are all right, so
  f is EXACTLY of Lemma 6's form with g_j = gamma_j (j in I, distinct and > 0), c_j = 1/F'(gamma_j) > 0, a >= 0, eps > 0.
  Numerics: |d_x T~ - i d_y T~ - f_0(nu_k)| <= 1.6e-48 (12 configurations, M = 3..6, s < 1 and a > 0 included).
- Multiplicity: correct, including the error order.  The roots-of-unity sum kills every Taylor order not divisible
  by n in each harmonic term (h + eps u, omega(t; .), xy, x), so Delta F(t) = O(|eta|^n) uniformly near the gamma_j
  (|nu* - i gamma_j| >= x* > 0) together with its t-derivatives; the IFT then gives
  Delta gamma_j = -Delta F(gamma_j)/F'(gamma_j) + O(|Delta F|^2 + |Delta F'| |Delta F|) = ... + O(|eta|^{2n}),
  so freezing c_j and gamma_j at nu costs only O(|eta|^{2n}).  The -mu Re z term drops out (sum_q w^q = 0).
  Numerics at 60 digits, coincident clusters (M,m) = (4,2),(4,3),(5,3),(6,4), every n = 2..m, |eta| = 1e-2..1e-4:
  |[T~(pert) - T~(nu)] - Re[f^{(n-1)}(nu*) eta^n]/(n-1)!| / |eta|^{2n} stays in [0.04, 2.0] (bounded, as claimed).
- Consistency run: 150 Nelder-Mead minimisations of T_eps (M = 3..5, eps = 1e-3..1e-1, s <= 1) found NO interior
  local minimum (every run drifts to some x_k -> 0, the Lemma 4 branch).  Consistent with Lemma 7, but weak evidence
  on its own; the real support is the exact bookkeeping checks above plus Lemma 6.

## Item 8. Main theorem (Section 5) -- OK, one small GAP (Corollary 5.1 justification)
(a) Face points: L = M + alpha is right (|h_y| <= 1; each gamma_j nondecreasing and 1-Lipschitz in y_k by the shift
    argument F_new(t+e) >= F_old(t); |dS/dy_k| = x_k).  Penalty drop >= eps pi sin(pi x) sinh(pi(R-t)) t (MVT for cosh);
    sin(pi x) >= 2 min(x, 1-x) gives eta_R.  Numerics (rv_05_main.py/.log): 5000 random (incl. atoms, coincident y):
    0 monotonicity / 0 Lipschitz failures, max |dT|/(L e) = 0.46; 120 numerical minimisations of T_eps on K_R:
    every face point satisfies sin(pi x) <= 0.011 * L/(eps pi sinh(pi R)).
(b),(c),(d): correct.  Lemma 5 is applicable at every step (current s >= 1 - eta_R resp. s - M eta_R, so eta_R <= s/2
    for R large; E must be read with the current s and size, harmless).  M' >= 1 in (c).
Degenerations -- all covered: escaping points are excluded by working on K_R (only face points occur, (a)-(c));
    x_k -> 1 with s < 1 is impossible (x_k <= s); x_k = s < 1 forces the other x's to 0 (Lemma 4); kinks gamma_j = 0
    and S = 0 are handled by the one-sided majorant T~ (gamma_j = 0 is put outside I, a = 0 when S <= 0), which is
    legitimate because T~ >= T_eps nearby with equality at nu; coincident points by the multiplicity argument;
    coincident quantiles cannot occur in (d) (F continuous, strictly increasing).  I found no missing case.
GAP (minor): Corollary 5.1 cites Lemma 5 for continuity at x_m = 0, but Lemma 5 compares nu with a configuration of
    DIFFERENT total s, so it gives continuity only after an extra induction over deleted points with joint continuity
    in (nu, s).  Cleaner fix: sigma_nu depends weakly-continuously on nu (Cauchy(y,x) -> delta_y as x -> 0), and the
    integer quantiles of a strictly increasing F are continuous under weak convergence (F^{-1} is continuous); with
    h continuous on S-bar this gives continuity of T on C_M(s) in one line.

## Item 9. Corollaries 1-3 -- OK
Duality step: (F5) gives h(x+iy) - p y >= Phi_c; the infimum equals Phi_c (stationary point; checked to 9e-42).  At the
    edges p = 0 and p = 1-x (0 < x < 1) there is no stationary point: the inf (= 0 = Phi_c) is only approached as
    y -> -oo resp. +oo (for x = 0 it is attained at y = 0).  Harmless, because after the sum over k separates only
    "inf <= Phi_c" is needed.  Wording only.
Cyclic symmetry: Tr(X T(Y)) = -Tr(Y T(X)) for all X, Y and Tr T(Y) = 0 give Tr(A iT(B)) = Tr(B iT(C)) = Tr(C iT(A)),
    sign change under transposition: correct (numerically 1.7e-16 on 500 random PVMs, rv_06_cor.py/.log).
Rank-one construction: g = diag(y) + iT(B) is Hermitian, B + ig = B - T(B) + i diag(y) is upper triangular with
    diagonal B_kk + i y_k (err 3e-17); Tr(PgP)_+ >= Tr(Ag) since 0 <= A <= P.  Correct.
Corank <= 3: in a Schur basis of B + iG one has G = diag(y) + iT(B) (err 4e-14 x scale), Q <= P, (Q, B, P-Q) is a PVM,
    rank Q + rank(P-Q) = rank P <= 3 forces one rank <= 1, then Cor. 2 and (F5).  Correct.  400 cases (corank 0..3,
    scales up to 300, one eigenvalue x20): every step's slack >= -8e-15 (rounding); (*) slack >= -4e-11 at matrix
    norms up to ~6000, i.e. relative 1e-14 (rounding).
Note on the REMARK in s.6: "(*) for all M is EQUIVALENT to the dual form for PVMs with all ranks >= 2" uses the
    converse half of Q-L12 ((*) => dual form), which is not proved in PROOF.md; cite it.

## Item 10. End-to-end numerics -- no violation
All searches: L-BFGS-B followed by Nelder-Mead from random, clustered-spectrum, one-huge-eigenvalue and
large-coupling starts; g = gmax*tanh(params), gmax in {3, 30, 300} (matrix norms up to ~1300).  Every point with a
negative (or < 1e-9) double-precision value was re-evaluated at 50 digits (rv_10_mpcheck.py/.log): 55 such points
among the 109 saved worst points, and 0 of them is negative.
- (*) for rank-one B, M = 3..8 (rv_07_e2e.py, logs rv_07_rank1_{A,B,C}.log; 12-30 starts per (M, gmax), 2 objectives):
    scale-free objective D/min(R2, |g_o|_1) (R2 = exact second-order prediction): minimum 0.0147 (M=5, gmax=300);
    per M the minima are 0.017-0.070 (M=3), 0.018-0.064 (4), 0.015-0.059 (5), 0.019-0.065 (6), 0.016-0.076 (7),
    0.024-0.067 (8).  Absolute objective D/max(1,|g|): the minimisers are commuting (decoupled) points with D = 0 up to
    rounding; the most negative double values (-3e-9 at |g| ~ 1000) are +3e-12 .. +2.5e-10 at 50 digits.
- Known hard configuration Q_fresh/t03_CM_counterexample_M3.npy (rank 1, eig g = -2.95, 0.60, 77.36)
  (rv_08_cm_config.py/.log): defect = 0.184793647815593... at 50 digits (double agrees to 3e-12; the 1-D functional T
  of PROOF.md gives the same value, 0.1847936478154).  Along g_d + t g_o the defect is NOT monotone (0.1914 at t = 0.96,
  0.1801 at t = 1.04 -- the known CM failure) but stays >= 0.18; along t g it rises from 0.034 to 1.85.  Local
  adversarial minimisation from this point (gmax 25, 100, 300): min D/min(R2,|g_o|_1) = 0.012.
- (*) for ALL projections at M = 5, ranks 1..4 (rv_07_allM5.log, 40 starts per gmax): min scale-free ratio 0.0098
  (rank 1, gmax 300), 0.0185 (rank 2, gmax 30), 0.068 (gmax 3); no negative value at 50 digits.
- Dual form for PVMs with a rank-one outcome (every slot), M = 5, 6, 7 (rv_07_dual.log, rv_07_dual2.log; 60 starts per M
  and seed): max |Tr(A iT(B))| / sum_k Phi = 0.72708 (M=5, ranks (2,2,1)), 0.74858 (M=6, (2,3,1)), 0.77178 (M=7,
  (3,3,1)); all three maxima are reproduced to 6 digits by an independent seed.  All < 1.
- Extra (not requested, but the induction needs it): s < 1 statement T >= 0 in matrix form (rv_09_sub.py/.log, M = 2..6,
  gmax 3/30/300): all negative double values are positive at 50 digits.  Restricted to the non-trivial region (quantiles
  of both signs, all x_k >= 0.02 s or 0.1 s; rv_11_mixed.py/.log, M = 3..5; the M = 6 leg was stopped): smallest T among runs that respect the
  constraint is 7.4e-3 (M = 3, gmax 3, x_min = 0.02 s); the minima grow with gmax and x_min (e.g. 0.13 for M = 4,
  gmax 300, x_min = 0.02 s; 1.49 at x_min = 0.1 s).  Runs that ended on the constraint boundary approach reducible
  configurations, where T -> 0+ (Lemma 4 + Lemma 3).  Examples: T = 8.1e-13 at a near-atom point (unconstrained run);
  T = 1.5e-10, 9.7e-11 and 3.9e-10 for three gmax-300 runs that broke the x_min barrier.  All values are at 50 digits.

## Gaps and suggested fixes (none affects any statement)
G1 (Cor. 5.1, used for compactness in s.5): continuity of T at points with x_m = 0 is not what Lemma 5 gives, because
   nu^0 lies in C_M(s - x_m), not C_M(s).  Fix: sigma_nu is weakly continuous in nu (Cauchy(y,x) -> delta_y), and the
   integer quantiles of a strictly increasing F are continuous under weak convergence.  Alternatively, keep Lemma 5 and
   add joint continuity in (nu, s) with induction over the deleted points.  Lemma 2's general case should likewise
   cite the atom argument (Lemma 4's multiset identity), not Lemma 5.
G2 (Lemma 6): state the order of limits.  Fix R (large, avoiding zeros of r_-).  Then fix the pole radii and a corner
   radius rho small enough that, on the corner piece, Re f > 0 dominates (this needs rho << exp(pi C0) with
   C0 = -(1/pi) sum c_j/g_j - mu + eps pi, which can be ~e^{-600}); also small enough that the pole term dominates
   on the pole pieces.  Only then let delta -> 0, then rho -> 0, then R -> oo.  It is worth adding that each pole
   carries a zero of f at x ~ c_j/(pi r_j^2), which is why delta -> 0 (not a fixed small delta) is essential.
G3 (Lemma 5(a)): the final inequality uses log(1/eta) >= 1/(pi-1), i.e. eta <= 0.627; add "since eta <= s/2 <= 1/2".
G4 ((F3)): "phi'(x+iy) = O(1 + |y|)" fails near nu = 0; restrict it to |nu| >= 1 (only |y| = R is used).
G5 (Cor. 2): at p = 0 or p = 1 - x the infimum over y is not attained ("equality at the stationary point" does not
   apply there); write "inf_y = Phi_c", which holds by limits.
G6 (Remark, s.6): the claimed EQUIVALENCE of (*) for all M with the dual form for all-ranks->=2 PVMs needs the converse
   half of Q-L12; cite it, or say "implied by".
G7: PROOF.md cites verify_r1.py / verify_r1.log, which are not in Q_r1.
G8 (cosmetic, Lemma 1(b)): "all x_k > 0" is equivalent to v being cyclic for g, so the "General case" paragraph is
   vacuous and can be dropped.

Not gaps (checked because the brief asked):
- Lemma 7's O(|eta|^{2n}) error is right, even though F and gamma_j move with the perturbation.
- The Lemma-6 form of f is exact: a >= 0, the c_j > 0, the g_j distinct and > 0.
- J_> + 1 <= M - 1 is right.
- The face-point constant L = M + alpha is right.
- Every degeneration of the minimiser is covered.
