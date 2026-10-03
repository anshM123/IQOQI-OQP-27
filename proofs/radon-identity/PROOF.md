# Q_RI/PROOF.md -- an elementary proof of the Radon identity (RI), and the distribution-free route to 2BMV and (*)

Authors: Ansh Mishra, Aryan Senthilkumar.  October 2026.  License MIT.
Status labels: PROVED = complete proof written below; NUMERICAL = checked numerically (scripts ri02..ri11 in this folder,
logs *.log next to them; s.7).  Everything in s.0-s.5 is PROVED except Remark 3.3(d) (NUMERICAL, not used).
RE-VERIFIED 2026-10-02 (internal check, Q_RI_check/REPORT.md): CORRECT, no gap; misprint in Remark 3.2 (rho = (1 - tau)/tau) and cosmetic
points B2, B3 fixed here; B4 (Remark 3.3(d) follows from (c) alone by dominated convergence) noted.
Tools: linear algebra, continuity of polynomial roots,
the Cauchy integral formula on a circle, differentiation under the integral sign, dominated convergence, Weierstrass'
theorem on locally uniform limits of holomorphic functions, and the one-variable identity theorem.  No distributions,
no Paley-Wiener-Schwartz, no Fourier inversion, no Radon inversion.

## 0. Statements

H is a Hermitian M x M matrix, P an orthogonal projection of rank M - r, B = 1 - P (rank r), H_d := BHB + PHP.
lam_1..lam_M = spec H, lam0_1..lam0_M = spec H_d = {mu_1..mu_{M-r}} u {beta_1..beta_r}, where mu_k = spec(PHP|ran P),
beta_j = spec(BHB|ran B).  Tr H = Tr H_d.  ||.|| = operator norm.  C_+ = {Im z > 0}, C_- = {Im z < 0}.  Log = principal
logarithm (holomorphic on C \ (-oo, 0]).  For 0 < tau < 1 and c in C put

    p(y; tau, c) := det(H + c - y(P - tau)),        Y(tau, c) := (P - tau)^{-1}(H + c) = (P/(1-tau) - B/tau)(H + c).

Since H + c - y(P - tau) = (P - tau)(Y - y), the roots of p (with multiplicity) are the eigenvalues of Y; the leading
coefficient det(-(P - tau)) = (-(1-tau))^{M-r} tau^r does not depend on c.  At c = 0 these are the y_i(tau) of the problem.

    L(H) := (1/2pi) int_0^1 sum_i |Im y_i(tau)| dtau,        R(H) := Tr H_+ - Tr (H_d)_+ .

THEOREM RI (Radon identity) [PROVED, s.2].  tau -> sum_i |Im y_i(tau)| is continuous on (0,1) and bounded by
M ||H|| / sqrt(tau(1-tau)), hence integrable, and L(H) = R(H).

(Lean: this is exactly `OQP27.StripL3b.Hyp_RI M` of formal-conjectures/OQP27/StripBMV.lean, where `pencilRoots P H tau` are
the roots of the characteristic polynomial of (P - tau)^{-1} H.  If r = 0 or r = M, P - tau is a real scalar, all roots are
real and H_d = H, so both sides vanish; below 1 <= r <= M - 1.)

THEOREM RI-C (complex form) [PROVED, s.2].  For Im c > 0 exactly M - r roots of p(.; tau, c) lie in C_+ and none is real.
Let S_+(tau, c) be their sum and S0_+(tau, c) := (Tr_P(PHP) + (M - r)c)/(1 - tau) (the same quantity for H_d, Lemma A(c)).
Then
    Psi(c) := int_0^1 [S_+(tau, c) - S0_+(tau, c)] dtau  =  E(c) := Tr[(H_d + c) Log(H_d + c)] - Tr[(H + c) Log(H + c)].
Taking boundary values: Im Psi(c0 + i0) = pi L(H + c0) and Im E(c0 + i0) = pi R(H + c0) for every real c0, so RI holds in
the shifted form  L(H + c0) = R(H + c0)  for all c0 in R  (RI for H + c0).

THE IDEA.  In the variables (tau, c) every simple root satisfies the complex inviscid Burgers equation d_tau y = y d_c y
(implicit differentiation of det(H + (c + y tau) - yP) = 0).  Summed over the M - r roots in C_+ (where no collisions with
the real axis can occur) this is the conservation law  d_tau sum Log y = d_c sum y  (Lemma C).  Hence d_c Psi is a boundary
term in tau; at tau = 1 it vanishes and at tau = 0 it is a Schur complement, giving d_c Psi = -log det(H + c) + log det(H_d + c)
= d_c E (Lemma D).  So Psi - E is affine (in fact 0), and taking imaginary parts on the real axis gives RI (s.2).

## 1. The complexified pencil (Im c > 0)

Throughout s.1: Im c > 0, 0 < tau < 1, K := ||H|| + |c|.  For a root y fix an eigenvector v of Y, |v| = 1, so
(H + c)v = y(P - tau)v, and put alpha := |Pv|^2 in [0,1] and a := <v,(P - tau)v> = alpha - tau in [-tau, 1 - tau].

LEMMA A (location, count).
 (a) Im c = a Im y.  Hence a != 0; a > 0 for y in C_+, a < 0 for y in C_-; and
        y in C_+  =>  Im y >= Im c/(1 - tau) > Im c,          y in C_-  =>  Im y <= -Im c/tau.
 (b) No root is real; exactly M - r roots (with multiplicity) lie in C_+ and r in C_-.
 (c) For H_d the roots are (mu_k + c)/(1 - tau) in C_+ (k <= M - r) and -(beta_j + c)/tau in C_- (j <= r).
Proof. (a) <v,(H + c)v> = <v,Hv> + c and = y<v,(P - tau)v> = y a, with <v,Hv> and a real; take imaginary parts.  Then
Im y = Im c / a with 0 < a <= 1 - tau, resp. -tau <= a < 0.  (b) Not real by (a).  For s in [0,1] apply (a) to sH (also
Hermitian): the roots of det(sH + c - y(P - tau)) are never real.  They depend continuously on s (unordered M-tuple; the
leading coefficient is independent of s), so the number in C_+ is constant on [0,1]; at s = 0 the roots are c/(1 - tau)
(M - r times) and -c/tau (r times).  (c) H_d + c - y(P - tau) is block diagonal: PHP + c - y(1 - tau) on ran P and
BHB + c + y tau on ran B.                                                                                                  QED

LEMMA B (bounds).  (i) Every root: |y| <= K/min(tau, 1 - tau).
 (ii) If y in C_+ and tau <= 1/2, or y in C_- and tau >= 1/2:  |y| <= K/sqrt(tau(1 - tau)).
 (iii) With S_-, S0_- the sums over C_- (S0_- = -(Tr_B(BHB) + rc)/tau):  S_+ + S_- = S0_+ + S0_-  (trace identity), and
        |S_+(tau, c) - S0_+(tau, c)|  <=  M K (2 + (tau(1 - tau))^{-1/2}).
Proof. |y| |(P - tau)v| = |(H + c)v| <= K.  (i) |(P - tau)v| >= min(tau, 1 - tau).  (ii) |(P - tau)v|^2 = (1-tau)^2 alpha +
tau^2 (1 - alpha) = tau(1 - tau) + a(1 - 2 tau), and in both cases a(1 - 2tau) >= 0 by Lemma A(a); so |(P - tau)v|^2 >= tau(1 - tau).
(iii) S_+ + S_- = Tr Y and Tr[(P/(1-tau) - B/tau)(H - H_d)] = Tr[(P/(1-tau) - B/tau)(PHB + BHP)] = 0.  For tau <= 1/2 use (ii):
|S_+| <= (M - r)K/sqrt(tau(1-tau)), and |S0_+| <= (M - r)K/(1 - tau) <= 2(M - r)K.  For tau >= 1/2 write S_+ - S0_+ = S0_- - S_-
and use (ii) for the C_- roots and |S0_-| <= rK/tau <= 2rK.                                                                QED
(The 'other' half plane is NOT bounded like (ii): roots of size ~ 1/tau, resp. 1/(1 - tau), occur there; ri02.)

LEMMA C (regularity; the Burgers identity).  Let Lam_+(tau, c) := sum_{y in C_+} Log y and Lam0_+(tau, c) :=
sum_k Log((mu_k + c)/(1 - tau)).  On (0,1) x C_+ the functions S_+, Lam_+ are C^1 in tau and holomorphic in c, with jointly
continuous partial derivatives, and
        d_tau Lam_+ = d_c S_+ ,           d_tau Lam0_+ = d_c S0_+  ( = (M - r)/(1 - tau) ).
Proof. Fix (tau0, c0).  By Lemma A(a) and B(i), the C_+ roots for (tau, c) near (tau0, c0) lie in the compact set
Q := {Im y >= eta, |y| <= rho} c C_+ (eta = Im c0/2, rho = 2K0/min(tau0, 1 - tau0), K0 = ||H|| + |c0| + 1).  Let D be the open
disc with centre iT and radius T - eta/2, T := rho^2/eta + 1; then Q c D and the closed disc lies in {Im >= eta/2} c C_+.  So,
near (tau0, c0), all C_+ roots are in D, all C_- roots outside, and p has no zero on the circle dD.  Writing
p = lc * prod_i (y - y_i), p_y/p = sum_i 1/(y - y_i), and the Cauchy integral formula gives, for phi holomorphic near the
closed disc,
        sum_{y_i in C_+} phi(y_i)  =  (1/2 pi i) oint_{dD} phi(y) p_y(y; tau, c)/p(y; tau, c) dy.                        (1.1)
Take phi(y) = y and phi = Log.  The integrand is smooth in (y, tau, Re c, Im c) on dD x (neighbourhood) and holomorphic in c,
so differentiation under the integral sign gives the regularity.  Next, p(y; tau, c) = f(y, c + y tau) with the polynomial
f(y, w) := det(H + w - yP), hence p_tau = y p_c.  With u := p_c/p we have d_tau(p_y/p) = d_y(p_tau/p) = d_y(y u) and
d_c(p_y/p) = d_y u, so
        d_tau Lam_+ - d_c S_+ = (1/2 pi i) oint_{dD} [ Log(y) d_y(y u) - y d_y u ] dy = (1/2 pi i) oint_{dD} d_y[ (y Log y - y) u ] dy = 0,
because Log(y)(u + y u') - y u' = (Log y) u + (y Log y - y) u' = d_y[(y Log y - y) u], a derivative of a single-valued
holomorphic function near the circle.  The pinched statement is the explicit computation Lam0_+ = sum_k Log(mu_k + c) -
(M - r) log(1 - tau), S0_+ = (sum_k mu_k + (M - r)c)/(1 - tau).                                                            QED
(For a simple root (1.1) reduces to d_tau y = y d_c y; with c = -s this is the Hopf equation d_tau x + x d_s x = 0 for the
roots x_i(s, tau) of Q_2bmv, and the density F = (1/pi) sum_{Im x > 0} Im x is a conserved density of it.  NUMERICAL ri03.)

LEMMA D (the two ends).  Fix c in C_+.
 (a) As tau -> 1-:  Lam_+(tau, c) - Lam0_+(tau, c) -> 0.
 (b) As tau -> 0+:  Lam_+(tau, c) - Lam0_+(tau, c) -> Theta(c) := sum_{t in spec T_0} Log t - sum_k Log(mu_k + c), where
     T_0 := PHP + c - PHB (BHB + c)^{-1} BHP on ran P (Schur complement; BHB + c is invertible as Im c > 0).  Moreover
     spec T_0 c C_+ and exp Theta(c) = det(H + c)/det(H_d + c).
Proof. (a) (1 - tau)Y = (P - ((1 - tau)/tau)B)(H + c) -> P(H + c) as tau -> 1.  In the decomposition ran P (+) ran B, P(H + c)
is block upper triangular with diagonal blocks PHP + c and 0, so its eigenvalues are mu_k + c (Im = Im c > 0) and 0 (r times).
By continuity of eigenvalues, for tau near 1 exactly M - r eigenvalues z_k of (1 - tau)Y are near the mu_k + c (so in C_+),
labelled so that z_k -> mu_k + c, and r are near 0.  Multiplication by 1/(1 - tau) > 0 preserves C_+, and Y has exactly M - r
eigenvalues in C_+ (Lemma A(b)); hence the C_+ roots are z_k/(1 - tau), the eigenvalues near 0 lie in C_-, and since
Log(z/(1 - tau)) = Log z - log(1 - tau) for z in C_+,  Lam_+ - Lam0_+ = sum_k [Log z_k - Log(mu_k + c)] -> 0.
(b) Schur: H + c - yP has blocks PHP + c - y, PHB, BHP, BHB + c, so p0(y) := det(H + c - yP) = det_B(BHB + c) det_P(T_0 - y),
a polynomial of exact degree M - r with roots spec T_0.  For y real, H - yP is Hermitian and Im c > 0, so p0(y) != 0: spec T_0
has no real point.  As tau -> 0, p(y; tau, c) -> p0(y) coefficientwise (p is polynomial in tau).  By Rouche on a circle
enclosing spec T_0 (and on small circles around its points), for small tau exactly M - r roots of p(.; tau, c) lie in a fixed
bounded disc, and they converge to spec T_0 with multiplicity.  The other r roots: tau Y = (tau P/(1 - tau) - B)(H + c) ->
-B(H + c), whose eigenvalues are -(beta_j + c) (in C_-, at distance >= Im c from R) and 0 (M - r times); so r eigenvalues of Y
are ~ -(beta_j + c)/tau, lie in C_- and leave every bounded set.  Since C_- contains exactly r roots, the M - r bounded roots
are the C_+ roots; their limits lie in the closure of C_+ and are not real, so spec T_0 c C_+, and Lam_+ -> sum Log t
(Log is continuous on C_+).  Also Lam0_+ = sum_k Log(mu_k + c) - (M - r) log(1 - tau) -> sum_k Log(mu_k + c).  Finally
exp Theta = det T_0 / det_P(PHP + c) = det(H + c)/(det_B(BHB + c) det_P(PHP + c)) = det(H + c)/det(H_d + c).                  QED
(Alternative without Rouche: for tau <= 1/2 the C_+ roots and spec T_0 lie in {Im >= Im c, |y| <= 2K_1}, K_1 = K + ||H||^2/Im c
(Lemma A(a); Schur bound |y|(1 - tau) <= ||PHP + c - PHB(BHB + c + y tau)^{-1}BHP||; numerical range of T_0), so (1.1) holds on
one fixed circle and p -> p0 uniformly on it; similarly at tau -> 1 with the characteristic polynomial of (1 - tau)Y.)

LEMMA E (boundary values).  Let c0 in R, 0 < tau < 1, and y_1..y_M the roots of p(.; tau, c0).  As c -> c0 within C_+:
        Im S_+(tau, c) -> (1/2) sum_i |Im y_i| ,        Im S0_+(tau, c) = (M - r) Im c/(1 - tau) -> 0.
If moreover H + c0 > 0, then all y_i are real and non-zero, exactly M - r are positive, and S_+(tau, c) -> sum_{y_i > 0} y_i.
Proof. p(.; tau, c0) is real on R (determinant of a Hermitian matrix), so its non-real roots come in conjugate pairs.  The
roots depend continuously on c (fixed leading coefficient).  If z is a root of p(.; tau, c0) of multiplicity m, then for c near
c0 exactly m roots are near z; if z is in C_+ (C_-) they are in C_+ (C_-), and if z is real their imaginary parts tend to 0.
Summing over the C_+ roots: Im S_+ -> sum_{Im z > 0} m_z Im z = (1/2) sum_i |Im y_i|.  If A := H + c0 > 0: a non-real root
would have <v,Av> = y a with a real, forcing a = 0 = <v,Av>, impossible; 0 is not a root (det A != 0); Y is similar to the
Hermitian matrix A^{1/2}(P - tau)^{-1}A^{1/2}, which by Sylvester's law of inertia has M - r positive and r negative
eigenvalues.  For c near c0 with H + Re c > 0, a C_+ root has Re y = <v,(H + Re c)v>/a > 0 (real part of Lemma A(a)'s identity,
a > 0), so the limits of the M - r roots in C_+ are >= 0, hence > 0, hence exactly the positive roots.                      QED

## 2. Proof of Theorems RI-C and RI

Step 1 (Psi is holomorphic, Psi' = -Theta).  By Lemma B(iii) the integral defining Psi converges absolutely.  For
0 < delta < 1/2 let Psi_delta(c) := int_delta^{1-delta} (S_+ - S0_+) dtau.  By Lemma C (continuity on [delta, 1 - delta] x
compact sets, differentiation under the integral sign, fundamental theorem of calculus) Psi_delta is holomorphic on C_+ and
        Psi_delta'(c) = int_delta^{1-delta} d_c (S_+ - S0_+) dtau = int_delta^{1-delta} d_tau (Lam_+ - Lam0_+) dtau
                      = (Lam_+ - Lam0_+)(1 - delta, c) - (Lam_+ - Lam0_+)(delta, c).
By Lemma B(iii), |Psi - Psi_delta| <= M(||H|| + R0) int_{(0,delta) u (1-delta,1)} (2 + (tau(1-tau))^{-1/2}) dtau -> 0 uniformly on
{|c| <= R0}.  By Weierstrass' theorem Psi is holomorphic on C_+ and Psi_delta' -> Psi' pointwise; by Lemma D, Psi'(c) = -Theta(c).

Step 2 (integration).  Let Theta_1(c) := sum_j Log(lam_j + c) - sum_j Log(lam0_j + c), holomorphic on C_+.  By Lemma D,
exp Theta = det(H + c)/det(H_d + c) = exp Theta_1, so Theta - Theta_1 is continuous (Theta = -Psi') with values in 2 pi i Z, hence
equal to a constant 2 pi i k on the connected set C_+.  Since d/dc [(lam + c) Log(lam + c)] = Log(lam + c) + 1 and both spectra
have M elements, E'(c) = -Theta_1(c).  Hence (Psi - E)' = -2 pi i k and
        Psi(c) = E(c) - 2 pi i k c + kappa      (c in C_+)  for some constant kappa in C.                                  (2.1)

Step 3 (boundary values).  Fix c0 in R and let eps -> 0+.  By Lemma E the integrand Im(S_+ - S0_+)(tau, c0 + i eps) tends to
(1/2) sum_i |Im y_i(tau, c0)| for every tau, and by Lemma B(iii) it is dominated by M(||H|| + |c0| + 1)(2 + (tau(1-tau))^{-1/2})
for eps <= 1.  By dominated convergence  Im Psi(c0 + i eps) -> pi L(H + c0).  On the other side, as z -> t in R from C_+,
z Log z -> t log|t| + i pi min(t, 0) (and -> 0 at t = 0), so, using min(t,0) = t - t_+ and Tr H = Tr H_d,
        Im E(c0 + i eps) -> -pi sum_j min(lam_j + c0, 0) + pi sum_j min(lam0_j + c0, 0) = pi R(H + c0).
Taking imaginary parts in (2.1):   L(H + c0) = R(H + c0) - 2 k c0 + Im(kappa)/pi    for all c0 in R.                        (2.2)

Step 4.  For c0 > ||H|| both H + c0 and H_d + c0 are positive definite (||H_d|| <= ||H||).  Then all roots are real (Lemma E),
so L(H + c0) = 0, and R(H + c0) = Tr(H + c0) - Tr(H_d + c0) = 0.  So the affine function -2kc0 + Im(kappa)/pi vanishes on
(||H||, oo): k = 0 and Im kappa = 0.  By (2.2), L(H + c0) = R(H + c0) for all real c0; c0 = 0 is RI.  The integrability claim:
sum_i |Im y_i(tau)| is continuous (continuity of roots) and each non-real root has |y| <= ||H||/sqrt(tau(1-tau)) (Lemma 1(b) of
Q_2bmv; the c0 = 0 case of the argument of Lemma B(ii), where a = 0).                                                       QED (RI)

PROPOSITION 2.1 (kappa = 0; this completes Theorem RI-C).  Let c0 > ||H|| and A := H + c0 > 0, D_tau := (P - tau)^{-1}.  By
Lemma E and dominated convergence, Psi(c0 + i eps) -> int_0^1 [S_pos(tau) - Tr(PAP)/(1 - tau)] dtau, S_pos := sum_{y_i > 0} y_i.
X := A^{1/2} D_tau A^{1/2} is Hermitian with spectrum = the roots, M - r of them positive; by Ky Fan's maximum principle
S_pos = max{Tr Q*XQ : Q*Q = 1_{M-r}}.  Upper bound: D_tau <= P/(1 - tau), so Tr Q*XQ <= Tr(Q*A^{1/2}PA^{1/2}Q)/(1 - tau) <=
Tr(A^{1/2}PA^{1/2})/(1 - tau) = Tr(PAP)/(1 - tau).  Lower bound: with J an isometry onto ran P take Q := A^{-1/2}J(J*A^{-1}J)^{-1/2};
then Q*XQ = (J*A^{-1}J)^{-1}/(1 - tau) = (A_PP - A_PB A_BB^{-1} A_BP)/(1 - tau).  Hence
        0 >= S_pos - Tr(PAP)/(1 - tau) >= -Tr(A_PB A_BB^{-1} A_BP)/(1 - tau) >= -||BHP||_F^2/((c0 - ||H||)(1 - tau)),
and the mirror argument for the r negative roots (D_tau >= -B/tau, Q := A^{-1/2}J'(J'*A^{-1}J')^{-1/2}, J' onto ran B) together with
S_pos + S_neg = Tr(D_tau A) gives the same bound with tau in place of 1 - tau.  So |S_pos - Tr(PAP)/(1 - tau)| <=
2||BHP||_F^2/(c0 - ||H||) for all tau, and Psi(c0 + i0) -> 0 as c0 -> oo.  Also E(c0) -> 0 (Taylor expansion of
(lam + c0)log(lam + c0) in lam: E(c0) = -(Tr H^2 - Tr H_d^2)/(2c0) + O(c0^-2) = -||BHP||_F^2/c0 + O(c0^-2), using Tr H = Tr H_d).
By (2.1) with k = 0, kappa = Psi(c0 + i0) - E(c0) for every c0 > ||H||; letting c0 -> oo, kappa = 0.                            QED

COROLLARY 2.2 (Nevanlinna structure) [PROVED].  By Lemma A(a), each C_+ root has Im y >= Im c/(1 - tau), so
Im(S_+ - S0_+) >= 0 pointwise in tau: Psi = E is a Nevanlinna function, E(c) = -||BHP||_F^2/c + O(c^-2), and
        E(c) = int_R R(H + t) dt / (t - c)        (Im c > 0),       int_R R(H + t) dt = ||BHP||_F^2,
i.e. E is the Stieltjes transform of the continuous, piecewise linear, nonnegative profile t -> R(H + t) = Tr(H + t)_+ -
Tr(H_d + t)_+ (its nonnegativity, Tr H_+ >= Tr (H_d)_+, is the classical pinching inequality, here a by-product).  RI says
that the same profile is the tau-integral of the pencil density.  (Proof of the formula: both sides are holomorphic on C_+,
O(1/c) at infinity, with the same imaginary boundary values pi R(H + t) (Step 3); their difference is entire after reflection
(Schwarz) and tends to 0, hence vanishes by Liouville.  Only RI itself is used later.)

## 3. Remarks and side results

3.1 (What was used.)  Lemma A-E and s.2 use: eigenvectors, Schur complements, Weyl-type norm bounds, continuity of the roots
of a polynomial of fixed degree in its coefficients (and Rouche for the degree drop in Lemma D(b), avoidable as noted), the
Cauchy integral formula on a circle, differentiation under integral signs, dominated convergence, Weierstrass' convergence
theorem, and 'a continuous 2 pi i Z-valued function on a connected set is constant'.  Positivity of U_xi (pinching) is not
used, nor any Fourier analysis.  Proposition 2.1 (not needed for RI) also uses Sylvester's law of inertia and Ky Fan.

3.2 (M = 2, by explicit integration) [PROVED].  H = [[alpha, gamma], [conj gamma, beta]], P = diag(1, 0).  The roots satisfy
sum |Im y| = sqrt(4 tau(1-tau)|gamma|^2 - m(tau)^2)_+ / (tau(1-tau)), m(tau) = alpha tau + beta(1 - tau) (discriminant of the
quadratic; cf. Q_2bmv Remark 4.4).  With rho = (1 - tau)/tau, the integrand becomes |beta| sqrt((rho - rho1)(rho2 - rho))/(rho(1+rho))
(rho1 rho2 = alpha^2/beta^2, (1 + rho1)(1 + rho2) = ((alpha - beta)^2 + 4|gamma|^2)/beta^2), and the classical
int_a^b sqrt((x - a)(b - x)) dx/(x + d) = (pi/2)(sqrt(b + d) - sqrt(a + d))^2 gives
        L(H) = (1/2) ( sqrt((alpha - beta)^2 + 4|gamma|^2) - |alpha| - |beta| )_+ = Tr H_+ - alpha_+ - beta_+ = R(H)
(the last equality by cases on the signs; both sides vanish iff H is semidefinite).  NUMERICAL check: ri08 (1e-30).

3.3 (The log-determinant / Frullani form) [PROVED: (a)-(c); NUMERICAL: (d)].  For Im c > 0 let nu_j(x, tau) be the
eigenvalues of the Hermitian matrix H - x(P - tau) (x real), nu0_j those for H_d, ell(x, tau, c) := sum_j Log(nu_j + c) -
sum_j Log(nu0_j + c) (a continuous branch of log p/q on the real line), Om(z) := z Log z - z.
 (a) Complex Jensen formula:  S_+(tau, c) - S0_+(tau, c) = (i/2pi) int_R ell(x, tau, c) dx.  (Split log(p/q) into the C_+ and C_-
     root groups; each group's log is holomorphic in the opposite half plane and is -(sum of its root differences)/x + O(x^-2);
     close the contour there.  At real c this is Lemma 2 of Q_2bmv.)
 (b) Since nu_j(x, tau) = (eigenvalue of H - xP) + x tau, and int_0^1 Log(m + x tau + c) dtau = (Om(m + x + c) - Om(m + c))/x
     (the path stays in C_+), int_0^1 ell dtau = (Phi_B(x) - Phi_P(x))/x with
     Phi_B(x) := Tr Om(H + c + xB) - Tr Om(H_d + c + xB),  Phi_P(x) := Tr Om(H + c - xP) - Tr Om(H_d + c - xP).
 (c) Phi_B extends holomorphically to x in C_+ and Phi_P to x in C_- (numerical ranges stay in C_+), both are O(log|x|/|x|) at
     infinity, and Phi_B(0) = Phi_P(0) = -E(c); closing the contours (principal values at 0) gives
        (i/2pi) int_R (Phi_B(x) - Phi_P(x)) dx/x = E(c).
 (d) Hence (a)+(b)+(c) give a second proof of Theorem RI-C, PROVIDED the x- and tau-integrations in int_0^1 int_R ell may be
     exchanged; the absolute integrability needed for Fubini is plausible (int_R |ell| dx = O(1 + log 1/(tau(1-tau))))
     but is not proved here.  At c -> c0 + i0 the real parts give the one-dimensional formula
        2 pi^2 (Tr(H + c0)_+ - Tr(H_d + c0)_+) = int_R dx/x [Tr Lam(H+c0+xB) - Tr Lam(H_d+c0+xB) - Tr Lam(H+c0-xP) + Tr Lam(H_d+c0-xP)],
     Lam(t) = t log|t| - t  (NUMERICAL ri10, ~1e-14).  This is the 'Lambda(z) = z log|z| - z' structure: route 1 (s.1-2) is the
     version of this computation in which the order of integration never has to be exchanged.

3.4 (Why the shift c0 matters.)  RI for H + c0, all c0, says: on every line s = w + xi tau the Radon projection of the density
F of Q_2bmv is the piecewise linear profile U_xi(w); its second derivative in w is the signed spectral measure
sum delta_{lam_j(xi)} - sum delta_{lam0_j(xi)}.  So the Burgers dynamics of the pencil roots is invisible after integration over
tau, except through the two ends tau = 0, 1 (Lemma D), which carry the spectra of H and H_d.

3.5 (Arbitrary Hermitian B: THEOREM RI-B) [PROVED; NUMERICAL ri11].  Let B be Hermitian with distinct eigenvalues
b_1 < ... < b_n (n >= 2), spectral projections Pi_k of ranks m_k, H_d := sum_k Pi_k H Pi_k, G := (b_1, b_n) \ {b_2, ..., b_{n-1}}.
For tau in G let y_i(tau) be the roots of det(H - y(B - tau)) (the eigenvalues of (B - tau)^{-1} H).  Then
        (1/2pi) int_G sum_i |Im y_i(tau)| dtau  =  Tr H_+ - Tr (H_d)_+ ,
and for Im c > 0, with S_+ the sum of the C_+ roots of det(H + c - y(B - tau)) and S0_+ := sum_{b_k > tau} (Tr_{Pi_k}(Pi_k H Pi_k)
+ m_k c)/(b_k - tau),   Psi_B(c) := sum over the gaps of int (S_+ - S0_+) dtau  =  E(c)  (E as in Theorem RI-C, with this H_d).
The projection case is n = 2, b = (0, 1).
Proof (changes only).  For tau in the gap (b_l, b_{l+1}) put d_- = tau - b_l, d_+ = b_{l+1} - tau, delta_l = b_{l+1} - b_l,
w_k = |Pi_k v|^2, a = <v,(B - tau)v> = sum_k (b_k - tau) w_k, m^+ = sum_{k > l} m_k, m^- = M - m^+.
 (A') Im c = a Im y as before; since a <= b_n - tau, C_+ roots have Im y >= Im c/(b_n - tau); the homotopy sH gives exactly m^+
     roots in C_+ (at s = 0 the roots are c/(b_k - tau)).
 (B') For a C_- root, sigma := sum_{k <= l}(tau - b_k) w_k > sum_{k > l}(b_k - tau) w_k (a < 0), so sigma >= max(d_+ W_+, d_- W_-)
     >= d_+ d_-/(d_+ + d_-) (W_+, W_- the total weights above, below tau), and |(B - tau)v|^2 >= sum_{k <= l}(tau - b_k)^2 w_k >=
     d_- sigma >= d_- d_+/2 when d_+ <= d_-.  Symmetrically for C_+ roots when d_- <= d_+.  With the trace identity (which holds as
     Tr[Pi_k(H - H_d)] = 0) this gives |S_+ - S0_+| <= M K (2/delta_l + sqrt(2/(d_- d_+))), integrable over every gap.
 (C') Lemma C verbatim, with f(y, w) = det(H + w - yB).
 (D') Ends of the gaps.  At b_n^- the C_+ roots are the m_n roots ~ (mu + c)/(b_n - tau), mu in spec(Pi_n H Pi_n), and they cancel
     the pinched term: limit 0 (as Lemma D(a), with (b_n - tau)(B - tau)^{-1} -> Pi_n).  At b_1^+ the C_+ roots converge to the
     M - m_1 roots of det(H + c - y(B - b_1)) = det(Pi_1(H + c)Pi_1) det(T_1 - y D_1) (T_1 the Schur complement of Pi_1(H + c)Pi_1 in
     H + c, D_1 = Q(B - b_1)Q > 0 on ran Q, Q = 1 - Pi_1), all of them in C_+, and exp(limit) = (det T_1/det D_1) *
     (det D_1 det(Pi_1(H + c)Pi_1)/det(H_d + c)) = det(H + c)/det(H_d + c), as in Lemma D(b).  At an interior b_k the two one-sided
     limits are EQUAL: (b_k - tau)(B - tau)^{-1}(H + c) -> Pi_k(H + c), so m_k roots are ~ (mu + c)/(b_k - tau) -- in C_+ for
     tau < b_k, where they are cancelled exactly by the k-th pinched term (present in Lam0_+ only for tau < b_k), and in C_- for
     tau > b_k; the remaining roots converge from both sides (Rouche) to the roots of det(H + c - y(B - b_k)) =
     det(Pi_k(H + c)Pi_k) det(T_k - y Q_k(B - b_k)Q_k), a polynomial of exact degree M - m_k without real roots; and the pinched
     terms with b_j > b_k are continuous at b_k.
 (E') Lemma E verbatim.  In Step 1 (now Psi_B := sum over gaps, truncated by delta at every gap end) the boundary terms telescope;
     the interior ends cancel by (D'), so Psi_B' = -Theta with exp Theta = det(H + c)/det(H_d + c), and Steps 2-4 are unchanged
     (for c0 > ||H|| all roots are real).
 (kappa = 0) Proposition 2.1 with D_tau = (B - tau)^{-1}, whose positive and negative parts are Delta_+ = sum_{b_k > tau} Pi_k/(b_k - tau)
     and -Delta_- = sum_{b_k < tau} Pi_k/(b_k - tau): with A = H + c0 > 0, Ky Fan and D_tau <= Delta_+ give S_pos <= Tr(Delta_+ A) = S0_+;
     the subspace A^{-1/2} ran(sum_{b_k > tau} Pi_k) gives S_pos >= Tr(Delta_+ A) - ||Delta_+|| Tr(A_{+-}A_{--}^{-1}A_{-+}), and the mirror
     argument the analogous bound with Delta_-; so |S_pos - S0_+| <= (2/delta_l) ||H||_F^2/(c0 - ||H||) -> 0, and kappa = 0.         QED

## 4. From RI to Theorem 1 of Q_2bmv (2BMV) -- Fubini/Tonelli and the identity theorem only

Notation of Q_2bmv: g Hermitian, F(s, tau) = (1/2pi) sum_i |Im x_i(s, tau)| for 0 < tau < 1 (x_i the roots of
det(g - s - x(P - tau))), F = 0 otherwise; D(a, t) = Tr e^{ag - tP} - e^{-t} Tr_P e^{aPgP} - Tr_B e^{aBgB}.
THEOREM 1 (Q_2bmv): F >= 0 is continuous on R x (0,1), vanishes unless lmin(g) < s < lmax(g), F <= (M/2pi)||g - s||/sqrt(tau(1-tau))
(so F is in L^1(R^2) with compact support), and D(a, t) = a^2 int int e^{as - t tau} F(s, tau) ds dtau for all (a, t) in C^2.

PROOF from RI.  The properties of F are Lemma 1 of Q_2bmv (elementary).  Write lam_j(xi) = spec(g - xi P),
lam0_j(xi) = spec(g_d - xi P) = spec(BgB|ranB) u (spec(PgP|ranP) - xi), and
        U_xi(w) := sum_j (lam_j(xi) - w)_+ - sum_j (lam0_j(xi) - w)_+  =  sum_j (w - lam_j(xi))_+ - sum_j (w - lam0_j(xi))_+
(equal since (l - w)_+ - (w - l)_+ = l - w and sum_j lam_j(xi) = sum_j lam0_j(xi)); U_xi is the U_xi of Q_2bmv Lemma 3.
(i) Radon slices.  Fix xi, w real and put H := g - xi P - w (Hermitian).  On the line s = w + xi tau,
     g - s - x(P - tau) = H - (x - xi)(P - tau), so the roots are x_i = xi + y_i with y_i the roots of det(H - y(P - tau)) and
     Im x_i = Im y_i.  Also H_d = g_d - xi P - w.  RI for this H reads
        int_0^1 F(w + xi tau, tau) dtau = Tr(g - xi P - w)_+ - Tr(g_d - xi P - w)_+ = U_xi(w).                              (4.1)
(ii) Laplace transform of a slice, real a != 0.  For a > 0, int_R e^{aw}(l - w)_+ dw = e^{al}/a^2; for a < 0,
     int_R e^{aw}(w - l)_+ dw = e^{al}/a^2.  Using the first (a > 0) or second (a < 0) form of U_xi (finite sums of integrable terms):
        int_R e^{aw} U_xi(w) dw = a^{-2} [ sum_j e^{a lam_j(xi)} - sum_j e^{a lam0_j(xi)} ] = a^{-2} [ Tr e^{a(g - xi P)} - Tr_B e^{aBgB}
                                  - e^{-a xi} Tr_P e^{aPgP} ] = D(a, a xi)/a^2.                                                 (4.2)
(iii) Tonelli.  F >= 0, so by (4.1) and the substitution s = w + xi tau (fixed tau)
        int_R e^{aw} U_xi(w) dw = int_0^1 int_R e^{aw} F(w + xi tau, tau) dw dtau = int int e^{as - (a xi) tau} F(s, tau) ds dtau.
     With t := a xi this gives, by (4.2),   D(a, t)/a^2 = I(a, t) := int int e^{as - t tau} F ds dtau   for all real a != 0, t.
(iv) Continuation.  D is entire on C^2 (power series), D(0, t) = 0 and d_a D(0, t) = 0 (e^{-tP} = B + e^{-t}P; Step 0 of Q_2bmv),
     so G := D/a^2 is entire on C^2 (divide the double power series).  I is entire on C^2 (F in L^1 with compact support:
     differentiation under the integral sign).  For fixed real t, a -> G(a, t) - I(a, t) is entire and vanishes on R \ {0},
     hence identically (identity theorem).  For fixed a in C, t -> G(a, t) - I(a, t) is entire and vanishes on R, hence
     identically.  So D(a, t) = a^2 I(a, t) on C^2.                                                                         QED
No Laplace/Fourier uniqueness theorem is needed for Theorem 1: RI provides the Radon projections in every direction xi,
which is already the full two-variable Laplace transform on the real (a, t)-plane.

4.1 (Theorem 3 of Q_2bmv: arbitrary Hermitian B) [PROVED from RI-B].  The proof above goes through verbatim with P -> B,
(0, 1) -> G, D -> D_B(a, t) = Tr e^{aA - tB} - sum_k e^{-t b_k} Tr_{Pi_k} e^{a Pi_k A Pi_k} (A Hermitian, F built from the roots
of det(A - s - x(B - tau)), F := 0 for tau outside G, F in L^1 by (B') and Q_2bmv (1')): on the line s = w + xi tau one has
H = A - xi B - w, H_d = A_d - xi B - w, spec(A_d - xi B) = union_k (spec(Pi_k A Pi_k) - xi b_k), so (4.2) reads
int e^{aw} U_xi(w) dw = D_B(a, a xi)/a^2; D_B(0, t) = 0 = d_a D_B(0, t) (Q_2bmv (3')).  Hence Theorem 3 of Q_2bmv holds with
the same elementary tools, and with a = 1 so does its corollary: for Hermitian A, B the function t -> Tr e^{A - tB} is the
Laplace transform of the positive measure  sum_k Tr_{Pi_k}(e^{Pi_k A Pi_k}) delta_{b_k} + (int_R e^s F(s, tau) ds) dtau  on
[b_1, b_n]  (Stahl's theorem, the former BMV conjecture).  This is a proof of it without distribution theory or Fourier
analysis; on prior proofs and on the mechanism see Q_2bmv s.8 (Stahl 2013, Eremenko 2015, Heinavaara arXiv:2310.03227).
No priority claim is made.

## 5. From Theorem 1 to Theorem 2 of Q_2bmv (the strip inequality (*) for every M)

The proof of Theorem 2 in Q_2bmv s.5 uses Theorem 1 at t = +-ia and, in the equality step (d), at a = 0 (both available on C^2
by s.4).  Its analytic inputs are all
one-variable and elementary; we list them and remove the two places where distribution language appears.
 * Lemma 5 (strip Poisson kernel K_X and its Laplace transform sin(a(1 - X))/sin(a)): geometric series and a rectangle-contour
   residue computation.
 * Lemma 6 (h_lam = Poisson integral of its boundary data): step (4) ('two harmonic functions agreeing on an open set agree') can
   be done with holomorphic functions: h_lam = Re[(i/pi^2) Li2(e^{-i pi z - pi lam})] and Phi = Re G with
   G(z) := (1/2) int_lam^oo (w - lam)[cot(pi(z - iw)/2) - i] dw (convergent: cot(pi(z - iw)/2) - i = O(e^{-pi(w - Y)})), both
   holomorphic on the open strip; G - (i/pi^2)Li2(...) has zero real part on {Y < lam}, so it is an imaginary constant there
   (Cauchy-Riemann), hence on the whole strip (identity theorem).
 * Step (a): Theorem 1 at t = +-ia, Lemma 5, Tonelli.
 * Step (b), Laplace transform of W without distributions.  rho - sigma has zero mass and zero first moment (from (5.2):
   rhohat - sigmahat = O(a^2), both analytic near 0).  Hence W(w) := int (w - u)_+ d(rho - sigma)(u) = int (u - w)_+ d(rho - sigma)(u).
   For 0 < a < pi use the second form and Fubini (int int e^{aw}(u - w)_+ dw d(rho + sigma)(u) = int e^{au} d(rho + sigma)/a^2 < oo):
   int e^{aw} W(w) dw = (rhohat(a) - sigmahat(a))/a^2; for -pi < a < 0 use the first form.  So by (5.2)
   int e^{aw} (W - V)(w) dw = 0 for 0 < |a| < pi, where W, V are continuous and O(e^{-pi|w|}) (Q_2bmv s.5(b)).
 * Uniqueness, minimal version needed:
   LEMMA U [PROVED].  Let Z: R -> C be continuous with |Z(w)| <= C e^{-c|w|} (c > 0).  If int e^{aw} Z(w) dw = 0 for all a in a
   nonempty open interval J c (-c, c), then Z = 0.
   Proof.  A(a) := int e^{aw} Z(w) dw is holomorphic on |Re a| < c (differentiation under the integral sign) and vanishes on J,
   hence on the strip (identity theorem); so Zhat(k) := int e^{-ikw} Z(w) dw = A(-ik) = 0 for all real k.  For eps > 0, w0 real,
   Fubini and int_R e^{iku - eps^2 k^2/2} dk = (sqrt(2pi)/eps) e^{-u^2/(2 eps^2)} give
        0 = (1/2pi) int_R Zhat(k) e^{ik w0 - eps^2 k^2/2} dk = int_R Z(w) (eps sqrt(2pi))^{-1} e^{-(w - w0)^2/(2 eps^2)} dw  ->  Z(w0)
   as eps -> 0 (Z bounded and continuous).                                                                               QED
   Applied to Z = W - V (c = pi, J = (0, pi)) it gives W = V, i.e. the exact defect formula; steps (c), (d) of Q_2bmv s.5 are
   unchanged ((d) uses G(0, t) = ||BgP||_F^2 (1 - e^{-t})/t, a second-order Duhamel computation).
So Theorem 2 -- the strip inequality (*) for every M and every projection B, with the exact defect and the equality case --
follows from RI using only: Tonelli/Fubini, the one-variable identity theorem, rectangle-contour residues, the Gaussian integral,
and Lemma U.  Chain: RI (s.2) => Theorem 1 (s.4) => Theorem 2 (s.5).

## 6. Formalisation notes (for formal-conjectures/OQP27, module L3b)

At the time of writing, `Hyp_RI M` in OQP27/StripBMV.lean is a hypothesis whose paper proof is s.2 above.  The proof uses:
 (F1) matrix facts: eigenvectors of Y for roots of p; |(P - tau)v|^2 = tau(1 - tau) + a(1 - 2tau); the trace identity; Schur
      complement determinants (Lemma D); the bound ||(BHB + c)^{-1}|| <= 1/Im c.
 (F2) continuity of the roots of a polynomial in its coefficients (Lemma A(b), D(a), E) and the degree-drop limit of Lemma D(b).
      All of these reduce to (1.1), i.e. to the Cauchy integral formula on a circle applied to sum_i phi(y)/(y - y_i): the number
      of roots in a disc is (1/2 pi i) oint p'/p, a continuous integer-valued function of the parameters as long as no root meets
      the circle.  For Lemma A(b) and D one fixed circle in C_+ suffices (C_+ roots lie in {Im y >= Im c, |y| <= const}, see the
      remark after Lemma D); for Lemma E use small circles around the roots of the limit polynomial.
 (F3) differentiation under the integral sign over a circle and over a compact tau-interval; FTC on [delta, 1 - delta].
 (F4) dominated convergence (Steps 1 and 3), with the explicit dominating function of Lemma B(iii).
 (F5) Weierstrass: locally uniform limits of holomorphic functions are holomorphic, with convergent derivatives (Step 1).
 (F6) a continuous function with values in 2 pi i Z on a connected set is constant (Step 2); the boundary values of z Log z
      (Step 3).
s.4 uses Tonelli on R x (0,1), translation invariance of Lebesgue measure, and the identity theorem in one variable twice.
Suggested order: Lemma B(i)-(ii) and A(a) (pure linear algebra), (1.1) for a circle, Lemma C, Lemma D(a), D(b), Steps 1-4.
`Hyp_RI` concerns projections only; Theorem RI-B (s.3.5) and Theorem 3 of Q_2bmv (s.4.1) are outside the OQP27 chain.

## 7. Numerical verification (NUMERICAL; Python 3.14 + mpmath; scripts and logs in this folder)

Common module ri_core.py: instances (P = diag(1_{M-r}, 0_r) w.l.o.g.), pencil roots via mpmath eig, S_+, Lam_+, E, R; L(H) by
tanh-sinh in theta (tau = sin^2 theta, tau and 1 - tau computed separately, working precision raised near the ends) split at the
exact branch points = real zeros of the reduced discriminant disc_y(p)/(tau^{r(r-1)}(1 - tau)^{(M-r)(M-r-1)}), a polynomial of
degree <= 2r(M - r) (the factor removed is a zero of that order at the ends, which otherwise hides branch points near tau = 0, 1),
plus a sign scan as safeguard and extra nodes at near-real complex zeros (near-collisions of roots).  Instances: 12 standard ones
(random M = 2..6 with all ranks r, scales 1..3; a repeated eigenvalue of PHP; zero diagonal blocks; near-commuting, off-diagonal
block 1e-3), plus in ri06 four more (scale 40; wide spectrum -30..25; rank-one B with M = 6; corank one with M = 6) and in ri02
six random sweep instances.

 ri01  (given) float check of RI.
 ri02_lemmas_AB   Lemma A count: 0 failures in 648 (instance, tau, c) samples (Im c from 1e-9 to 4, tau from 1e-8 to 1 - 1e-8);
                  Lemma B(i) max ratio 0.99999981, B(ii) max ratio 0.99306 (both bounds nearly sharp); the wrong half plane gives
                  ratio 9999.997 (unbounded, as stated); trace identity 6e-29; domination ratio <= 0.19; real-c Lemma 1(b) <= 0.81.
 ri03_burgers     d_tau Lam_+ = d_c S_+ at 36 random points: 2.8e-49 (40 digits); pinched pencil; DOUBLE root (H = H_d with repeated
                  mu) and near-double root (gap 3.4e-12): 0 and 6.4e-50; contour formula (1.1) on an explicit circle: 5.7e-40;
                  Hopf equation x_tau + x x_s = 0 at 30 non-real roots: 1.1e-40.
 ri04_endpoints   tau -> 1 and tau -> 0 limits of Lam_+ - Lam0_+ (linear rates O(1 - tau), O(tau) visible down to 1e-8);
                  exp Theta = det(H + c)/det(H_d + c) to 1.4e-40; Theta = Theta_1 (k = 0) to 2.8e-40.
 ri05_complex     Theorem RI-C, Psi(c) = E(c), at 48 (instance, c) pairs with Im c in {2, 0.5, 0.05, 0.003}: max |Psi - E| 2.5e-29
                  (30 digits); Step 1 (d/dc Psi_delta = boundary terms), delta = 0.1, 1e-3: 1.4e-28.
 ri06_RI_highprec RI at 30 digits on all 16 instances: max |L - R| = 4.4e-29 (e.g. near-commuting: L = 9.430689654741421121197e-7
                  = R to 9e-33); shifted form L(H + c0) = R(H + c0) on 33 points crossing all kinks: 3.2e-30; boundary values
                  Im E(c0 + i eps)/pi - L(H + c0) = -1.01 eps (eps = 0.3 .. 1e-6), and direct quadrature of Im Psi agrees with Im E.
 ri07_kappa       Proposition 2.1: C_+ roots -> positive roots (3e-17 at eps = 1e-20), Ky Fan upper bound and Schur lower bounds:
                  0 violations, |S_pos - S0_+| (c0 - ||H||)/(2||BHP||_F^2) <= 0.47; int (S_pos - S0_+) = E(c0) to 2.7e-28.
 ri08_M2          Remark 3.2: integrand formula 1.4e-30; L = closed form = R to 3.9e-31 on 19 cases incl. all sign patterns and
                  the degenerate cases gamma = 0, alpha beta = |gamma|^2.
 ri09_chain_thm1  s.4 (20 digits): roots on the line s = w + xi tau equal xi + y (1e-19); Radon slice by pencil quadrature =
                  U_xi(w) (9e-21); (4.2) for real a of both signs (3e-19); full chain RI -> Tonelli -> Laplace at real (a, t) =
                  (0.9, 0.5), (-0.6, 1.4), slices computed by pencil quadrature at 56 w-nodes: |chain - D(a,t)/a^2| <= 1.8e-16;
                  genuinely complex (a, t) = (0.8 + 0.6i, 0.3 - 1.1i) (t/a not real) by direct float 2D integration: 3.1e-10.
 ri10_logdet      Remark 3.3: complex Jensen (a) 4.3e-25; tau-integration (b) 9.1e-25; Frullani identity (c) 9.9e-14 (14 cases);
                  real one-dimensional formula (d) = 2 pi^2 R(H + c0) to 2.1e-25 (18 cases).  (Tails of the x-integrals need working
                  precision ~ dps + log10|x|; without it tanh-sinh returns wrong values silently.)
 ri11_generalB    Theorem RI-B, spec B = (0,.37,1), (-1,.2,.5,2), (0,.6,.6,1), (0,.3,.3,.31,1), (-.5,.1,.1,.9,2,2) (repeated interior
                  eigenvalues included): Psi_B = E to 1.1e-29 (10 values of c); one-sided limits at interior b_k agree (difference
                  O(distance), 1.7e-7 at distance 1e-9); RI-B itself at 30 digits: max |L_B - R| = 4.3e-28 (all five spectra).
