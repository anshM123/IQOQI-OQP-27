# Re-verification report on Q_RI/PROOF.md (elementary proof of the Radon identity)

Object: Q_RI/PROOF.md (version of 2026-10-02 03:31). Sections 0-6 checked line by line; section 7 spot-checked against the author's
logs. Method: every step re-derived by hand; independent numerics written from scratch (nothing imported from Q_RI/*.py); instances
are exact Gaussian-rational matrices (sympy), exactly degenerate spectra from Cayley unitaries; branch points are the real zeros of the
exact y-discriminant of p(y, tau), isolated exactly; mpmath at 40-60 digits with two quadrature rules per piece, non-converged pieces
redone by adaptive bisection; a direct 2D quadrature for s.4 (not via the Radon slices) in double precision.

## 0. Verdict
CORRECT. The logical chain is complete and correct, with no gap and no false statement: s.1-2 (Theorem RI-C including kappa = 0,
Theorem RI); s.3.5 (Theorem RI-B); s.4 (Theorem 1 of Q_2bmv from RI); s.4.1 (Theorem 3 / BMV); s.5 (Lemma U and the distribution-free
route to Theorem 2). One displayed formula in the unused side Remark 3.2 is misprinted (the final M = 2 formula is right); three
cosmetic or labelling points. Independent numerics confirm every identity to 34-46 digits.

## A. Step-by-step verdicts
| Item | Verdict | What was checked |
|---|---|---|
| s.0 setup | OK | (P-tau)^{-1} = P/(1-tau) - B/tau; leading coefficient (-(1-tau))^{M-r} tau^r, independent of c; r in {0, M} trivial. Lean `Hyp_RI M` (StripBMV.lean) states exactly Theorem RI. |
| Lemma A(a) | OK | Im c = a Im y with a = \|Pv\|^2 - tau in [-tau, 1-tau]; one eigenvector per eigenvalue suffices (Jordan blocks harmless). Sharp. |
| Lemma A(b) | OK | homotopy sH: leading coefficient fixed and nonzero, roots never real, so the C_+ count is constant; at s = 0 it is M - r. |
| Lemma A(c) | OK | pinched pencil is block diagonal. |
| Lemma B(i)-(iii) | OK | \|(P-tau)v\| >= min(tau, 1-tau); \|(P-tau)v\|^2 = tau(1-tau) + a(1-2tau), valid exactly for (C_+, tau <= 1/2) and (C_-, tau >= 1/2); trace identity; the majorant depends on c only through \|\|H\|\| + \|c\|, uniform in Im c in (0,1]. |
| Lemma C | OK | the disc D (centre iT, radius T - eta/2, T = rho^2/eta + 1) lies in {Im >= eta/2}; (1.1) holds; p_tau = y p_c; exact derivative. |
| Lemma D(a), (b) | OK | (1-tau)Y -> P(H+c); Log(z/(1-tau)) = Log z - log(1-tau) exactly; Schur: p0 = det_B(BHB+c) det_P(T_0 - y), degree M - r; Hurwitz: M - r roots stay bounded, r roots ~ -(beta+c)/tau escape in C_-; spec T_0 in C_+; exp Theta = det(H+c)/det(H_d+c). |
| Lemma E | OK | real polynomial, conjugate pairs, continuity in c; Sylvester inertia for H + c0 > 0. |
| Steps 1-4 | OK | FTC on [delta, 1-delta]; c-uniform tails; Weierstrass; Psi' = -Theta; Theta - Theta_1 in 2 pi i Z constant; dominated convergence; z Log z -> t log\|t\| + i pi min(t,0); k = 0 from c0 > \|\|H\|\|. |
| Prop 2.1 (kappa = 0) | OK | Ky Fan with D_tau <= P/(1-tau); Schur-complement frame; E(c0) = -\|\|BHP\|\|_F^2/c0 + O(c0^{-2}). |
| Cor 2.2 | OK* | Nevanlinna property and Stieltjes formula hold (Schwarz reflection needs the standard continuity of the Cauchy transform of the Lipschitz profile). |
| Rem 3.2 | misprint | see B1; final formula correct. |
| Rem 3.3 (a)-(d) | OK | (d) follows from (c) alone (B4). |
| 3.5 (A')-(E') | OK | count m^+; sigma >= d_+d_-/(d_+ + d_-); \|(B-tau)v\|^2 >= d_+d_-/2 on the half-gap; interior cancellation at b_k (one-sided limits agree; numerically <= 1.8e-33 at 10 interior points incl. multiplicities 2 and 3); kappa = 0. |
| s.4 (i)-(iv) | OK | slice reduction; Laplace transform of a slice = D(a, a xi)/a^2; Tonelli; entire functions; identity theorem in a, then in t. |
| s.4.1 | OK | spec(A_d - xi B) = union_k (spec Pi_k A Pi_k - xi b_k); D_B(0,t) = d_a D_B(0,t) = 0. |
| s.5 | OK | Lemma 6 holomorphic version; step (b); Lemma U (identity theorem + Gaussian approximate identity), applied with c = pi, J = (0, pi). |

Notes on flagged points: (1) root location and count hold for every Im c > 0, tau in (0,1) (400 + 120 samples, 0 failures);
(2) the proof never differentiates individual roots; collisions inside C_+ occur (example M = 4, r = 1, tau0 = 0.32, double root to
4e-30) and d_tau Lam_+ = d_c S_+ holds there to 60 digits; (3) Log only evaluated on C_+; divergent -log(1-tau) terms cancel; escaping
roots at tau -> 0 are in C_-; k = 0 confirmed (|Theta - Theta_1| <= 3.8e-60); (4) the B(iii) majorant is uniform in Im c, the split
bound holds exactly on the stated combinations (max ratios 0.970 and 0.169; 8.2e6 on the other half-plane, as stated);
(5) Tonelli and identity theorem correct; (6) Lemma U correct; (7) general-B interior cancellation correct.

## B. Issues and fixes
B1 (misprint, unused Remark 3.2): with rho = tau/(1-tau) the displayed prefactor/products are wrong; correct substitution is
  rho = (1 - tau)/tau (then everything stands). As printed max deviation 3.8-9.5; with the fix <= 7.4e-40. Final L(H) correct (1.2e-41).
B2 (cosmetic): "every root satisfies d_tau y = y d_c y" -> "every simple root".
B3 (cosmetic): s.5 "uses Theorem 1 only at t = +-ia": step (d) also uses a = 0 (available by s.4).
B4 (labelling): Remark 3.3(d) is the boundary value of (c) alone; can be labelled PROVED with a dominated-convergence remark (4.8e-23).
Optional: two-line proof of Lemma C via d_tau Lam_+ = -(1/2 pi i) oint p_tau/(y p) dy = -(1/2 pi i) oint p_c/p dy = d_c S_+.

## C. Independent numerics (this folder)
| Check (script) | Cases | Result |
|---|---|---|
| RI, L = R (rc01, rc07) | 22 instances, M = 2-8; r = 1, M-1; repeated spectra; H1 (+) H1; BHB = 0; singular H; off-diagonal 1e-6, 1e-9; spread 1e-3..1e3; scale 1e4; M = 8, r = 4 | <= 9.2e-40 absolute (scale 1e4: relative 8.8e-41) |
| Shifted RI (rc01, rc07b) | 32 values of c0 across all kinks | <= 1.3e-34 |
| RI-C, Psi = E (rc02, rc07d) | 40 (instance, c) pairs, Im c/\|\|H\|\| from 1/300 to 6 | <= 2.8e-39 |
| Lemmas A-E, Step 1 (rc02, rc02b, rc03, rc08) | 400 + 245 samples | trace identity 2.8e-61; Step 1 to 8.7e-41; Lemma C defect < 1e-60; Theta = Theta_1 to 3.8e-60 |
| Prop 2.1, Cor 2.2, Rem 3.2 (rc04) | 36 cases | 0 violations; Stieltjes formula to 1.3e-39; B1 confirmed |
| Rem 3.3 (rc04b) | 3 instances | (a) 1.8e-25, (c) 7.5e-24, (d) 4.8e-23 |
| RI-B, Psi_B = E (rc05, rc07*, ) | 7 B-spectra x 2 c0; 14 values of c | <= 2.3e-40; Psi_B = E <= 9.1e-39 (one point 1.2e-31) |
| s.4 / s.4.1 by direct 2D quadrature (rc06b) | 6 (a,t) per instance incl. t = +-ia | projections 7.5e-14..7.8e-11; general B <= 2.7e-9; sum rule to 1e-15 |

Quadrature artifacts (signature |GL - TS| ~ |L - R|) were all recomputed adaptively and agree to 0..5e-44.

Overall verdict: the elementary proof of RI is correct, and so are the derived results (RI-C with kappa = 0, RI-B, Theorem 1 (2BMV)
and Theorem 3 (BMV) from RI by Tonelli plus the identity theorem, and the distribution-free route to Theorem 2 via Lemma U).
