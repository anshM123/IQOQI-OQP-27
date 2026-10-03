# Re-verification report: the reduction chain from (*) and CONE_d to the CGLMP bound, and rigidity (OQP 27B, max-ent clause)

Scripts and logs: this folder (k00_core.py ... k10_Fcheck.py with .log files; spot/ holds verbatim copies of QD2/verify_gauss.py and
QD2/verify_fixedpoint.py, sha256-identical, with private logs).  All re-implementations are independent (no programme imports);
nothing under QD2/ was written.

## Overall verdict: CORRECT
No wrong step, no counterexample, no mathematical gap.  Items 1, 2, 3, 4, 6: OK.  Item 5: the logic is OK (Lemma B gives EXACT cone
membership; all d >= 2 are covered).  One certificate-bookkeeping gap G2 (203 <= d <= 600) with a mechanical fix, confirmed at
d = 203, 300, 600.  The fixed-point sweep completed during the review (audit_alld.py: ALL-D CERTIFIED, 1800/1800).

## Item 1 -- strategy -> clock model -> Q-configuration -> linear form: OK
Re-derived by hand: Lemma 2.1 (including the shift by one in the (B1, A2) term); the Fourier coefficients c_n = -1/(1-w^{-n});
Theorem 2.3(1) via 4 c_n z^{-n} = -h_n and i h_{d-m} = conj(h_m); Theorem 2.3(2) (the twirl rho has rho^{4d} = id; the ladder
Z = W^4 gives M = 4D and V_k^4 = 1); the projection form F = <A,B>/2 - d/2; N(d) = d, N(2d-m) = N(m); F = sum_{m<d} csc(pi m/2d) N(m).
Numerics (k01, 80 random strategies, d = 3..8, D = 2..6 including D < d and rank-deficient measurements): I_d direct vs via F(V)
5.6e-15; direct vs the N(m) linear form 1.0e-14; twirl/basis residuals 4.8e-14; other identities <= 1.5e-13.  Conventions: the CGLMP
measurements give I_ME(d) to 2e-15 for d = 2..8 (also DKZ (x) 1_2); gradient ascent never exceeds I_ME; at (d,D) = (3,4) the best
value found is 2.6547 < I_ME(3) = 2.8729, as rigidity predicts.

## Item 2 -- continuum theorem Q-T1: OK
Harmonicity: the operator constraint keeps the numerical range of Re H(z) in (0,1) (also with zero-length cells), so the spectrum
stays in the open strip where phi_lam is holomorphic.  Boundary values for step fields: the closed-form Herglotz function is
continuous up to the boundary except at cell endpoints, where the conjugate function has log singularities; the domination is in
every L^p, h_lam <= (y-lam)_+ + C; dominated convergence gives int u*_lam = M h_lam(1/4).  Concavity step correct (and unnecessary
under the operator identity int B = (1/4) 1).  Legendre: lam* = log2/(2pi), lam*/4 + h_{lam*}(1/4) = G/pi^2 exactly (closed form of
Li2((1-i)/2)).  Numerics (k03): Herglotz closed form vs integral <= 5e-15; h_lam via Li2 vs strip Poisson integral 2e-16; mean value on
circles r = 0.3, 0.7, 0.95 <= 5e-15; Q^ell/N^2 vs int tau(A g) dm (incl. a zero cell) <= 1.2e-13; boundary mean-value identity ~1e-7
(quadrature-limited; 1.2e-8 with a smooth integrand, k03c).

## Item 3 -- cell inequalities (QD2-L1) and window-sum form (QD2-L2): OK
Re-derived: the operator constraint int Btilde = d 1 for every cell vector (zero cells included); kernel invariance under the double
shift by d (L_{x+d} = L_x + d), so averaging over d rotations equals averaging over Z_N; windows embed as two adjacent arcs with value
N^2 G/pi^2 for every cell vector; the window-sum form via S_r(2d-j) = 2d - S_{r+d-j}(j).  Numerics (k02, d = 3..8, M = 2, 3, 5, random
Dirichlet, zero-cell and rational cells, all rotations): max [rotated cell value - N^2 Phi_c] = -3.6e-15, attained only by two-residue
embeddings whose two visible sites commute (the blind spot of Remark 4.3); with all cells positive the maximum was <= -1.2.  The
rotation-averaging identity (1.4) holds to 6e-15 (relative); u^ell agrees with the window-sum form to 3e-16; windows and commuting
one-step mixtures are tight for every rotation; two-residue cells give u^ell = c t_s with c > 0.

## Item 4 -- QD2-R1 with the actual certificates: OK
Certificates d = 2..8 (k04): u^ell recomputed from the original cell-pair kernel at 50 digits; stored float weights leave
|v - U lambda| <= 1.1e-14; the exact minimum-norm correction keeps every lambda > 0 (matching the certified minima) and makes the
residual zero at 50 digits.  Random strategies: every certificate direction pairs negatively with delta (largest -3.5);
sum lambda_k <u_k, delta> = <v, delta> = 2(F - F_DKZ) to 2e-13; I_d <= I_ME always.  Near the optimum (k06, DKZ (x) 1_2 with
non-commuting rotations of size s = 0.1, 0.01, 0.001): the identity holds to 1.7e-10 of the deficit (deficits down to 4e-5); each
certificate direction is strictly negative, ~ s^2; commutators ~ s.  All 199 LP certificates (k07, d = 2..200): every cell >= 1/16,
correct sums, positive weights; smallest certified weight 4.25e-4 (d = 198).

## Item 5 -- CONE_d certification: logic OK; gap G2
d <= 200: exact finite representations, verified in interval arithmetic in verify_cone.py (Clausen series with rigorous tail, residual
bound for the exact weights); d = 2 included.  201 <= d <= 2000: v = E_mu[u^ell] + sum w_s t_s with w_s >= 0, exact at the
Poincare-Miranda zero; continuity on the box (the boundary of the event E is null since Var eta_r = Phi(1) > 0); sign conditions from
a certified sign change plus a certified derivative bound.  Re-derived: the regular-part coefficients g_i (incl. g_1 and the odd-index
formula), the tail bounds, the Bell-polynomial bound, |F_r^{(k)}| <= 8 k! d^2/(d)_k, the remainder bound on kappa_16 and the truncated
Gaussian moments, P(E^c), "at_k >= 0 <=> positive-definite covariance", Lemma R2.  Independent re-implementation at d = 50 (k08, direct
Beta-density quadrature, no series): reproduces Phi* to ~1e-11 and the minimum variogram coefficient 0.0654767/d^2 at k = 25.
Enclosures of F, F'', F'''' at d = 60 match direct quadrature to 18, 11, 6 digits (k10).  Monte Carlo of the Dirichlet aggregation in
Lemma R3 consistent (k05b: all |z| <= 3.2 over 27 values).  Logged certificates reproduce bit-for-bit at d = 201, 202, 204, 250, 300,
400, 500, 600, 601, 777, 1500.
d >= 2001: Lemma P and the QD2-L11 identity (4.4e-14); QD2-L12 at 40 digits for 0 <= m <= 401 (a(m) convex and positive,
a_0 - 2a_1 + a_2 = 0.1054879, max m^2 a(m) = 0.0722217 <= 13/180); boundary-layer coefficient 0.12626 >= claimed 0.12034 (d = 2001,
2002, 3001, 5000); the eps^4 terms of the Euler-Maclaurin defect cancel (1/240 - 1/144 + 1/360 = 0), so the defect is O(eps^6); inner
and outer zones overlap; all audit items pass.  Boundary cross-check: the regime-2 verifier certifies d = 2001 directly
(d^2 min at_k = 0.1264, d min slack = 0.666, fixed-point ratio 4.001), and its Phi* gives D_B(1) = -2.747 eps^2, D_B(2) = 208.4 eps^3,
D_B(m) >= 9.9 eps^3 (m >= 3), consistent with the regime-3 bounds.  Coverage: 2..200 LP; 201..2000 Gaussian + fixed point; >= 2001
analytic; no hole at 200/201 or 2000/2001.
Trivial directions t_s (d >= 201): confirmed nonpositive, by (1) the pair form N(s) + N(d-s) - d = sum over d pairs of
[pi(0) + pi(1) - pi(2) - pi(3) - 1] <= 0 (including s = d/2; numerically 1.4e-15, max <t_s, delta> = -1.17), and (2) QD2-R2 (the cell
inequality with zero-length cells; u^ell = c t_s, c > 0).  Lemma R1's w decomposes with nonnegative coefficients on the t_s; the LP
certificates (d <= 200) contain no t_s terms.

## Item 6 -- rigidity: OK
Step 1: exact representation, every term <= 0, so equality forces tightness for mu-a.e. cell vector; for d <= 200 all atoms have
positive cells (k07), for d >= 201 mu charges positive cells fully (Dirichlet parameters >= 1/4).  Step 2: equality carries through
(3.5) at the fixed lam*; Theorem 2(d) of Q_2bmv (equality at one, equivalently all, lam) was re-verified as correct.  Step 3: the residue lemma
is correct (simple poles with residues 2J_j; distinct endpoints exactly when all cells are positive).  Steps 4-5 correct (conjugation
identity X^r W_0 X^{-r} in Corollary C; translation to u (x) conj(u)); near-optimal numerics (k06) consistent.

## Gaps and fixes
G1 (closed): fixed-point sweep complete; update status lines in RIGIDITY_ALLD.md (D5)/s.8 and SHARED_LEMMAS [MAIN].
G2 (bookkeeping; conclusion not in doubt): (a) logs/vg_d203.json is a leftover of an older verify_gauss.py; (b) for 204 <= d <= 600 the
  Gaussian logs are 100-bit runs while the fixed-point logs are 160-bit runs (verify_fixedpoint.py default), and the root boxes differ by
  1.65e-11 (d = 300), 9.1e-13 (d = 600) >> r ~ 1e-30, so the logged margins and derivative bound do not refer to one Poincare-Miranda box.
  FIX: regenerate the Gaussian logs for 203 <= d <= 600 at 160 bits (or recompute min at_k and min slack inside verify_fixedpoint.py on its
  own widened boxes and record the precision).  Confirmed at d = 203, 300, 600.
G3 (cosmetic): audit_certs.py's check ptail <= 2d exp(-0.4 d) is vacuous for d >~ 1865 (underflow); store log10(ptail).
G4 (documentation): audit_alld.py hard-codes |G - G_4| <= 200 eps^3 and |d_t G_4| <= (40/pi) d; re-derived ~137.7 eps^3 (consistent
  with 137.3 of CONE_ALLD_PROOF s.9); compute these in a script.
G5 (documentation): verify_gauss.py takes zeta values from mpmath at higher precision and widens them; state this.
G6 (text): RIGIDITY_ALLD.md (D1) still says "UNDER RE-VERIFICATION"; its s.8 sweep range is obsolete.
Scope: projective measurements only.
