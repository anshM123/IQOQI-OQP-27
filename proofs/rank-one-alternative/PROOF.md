# The strip inequality (\*) for rank-one B, every M  (and consequences: (\*) for corank <= 3, all M <= 5)

Working notes Q_r1.  Status of every statement: PROVED (full proof below) unless marked otherwise.
Numerical cross-checks: scripts r01..r09 in this folder; re-verification checks rv_01..rv_11 (report: REVIEW.md).

## 0. Notation and standing facts

S = {nu = x + iy : 0 < x < 1}, closure S-bar.  h(x+iy) = -(1/pi^2) Im Li2(e^{pi y} e^{-i pi x}).

(F1) h is harmonic on S, continuous on S-bar, h(iy) = y\_+, h(1+iy) = 0, and 0 <= h(x+iy) <= C(1 + |y|).
(F2) h(x+iy) - h(x-iy) = (1-x) y on S-bar; hence h >= max(0, (1-x)y) = (1-x) y\_+.
     (Both sides are harmonic, agree on the boundary lines, and the difference grows at most linearly; a harmonic function
     on a strip of width 1 vanishing on both boundary lines with sub-exponential growth is 0.  h >= 0 because h is the
     Poisson integral of its nonnegative boundary data, by the same uniqueness.)  [= Q-L4]
(F3) phi(nu) := (i/pi^2) Li2(e^{-i pi nu}) is holomorphic on S with Re phi = h, and
        phi'(nu) = -(1/pi) log(1 - e^{-i pi nu})      (principal log; 1 - e^{-i pi nu} lies in the upper half-plane for nu in S).
     Boundary values: for y > 0, phi'(0+ + iy) = -(1/pi) log(e^{pi y} - 1) - i;  for y < 0, phi'(0 + iy) = -(1/pi) log(1 - e^{pi y})
     (real, and phi' extends holomorphically across {x = 0, y < 0});  phi'(1 + iy) = -(1/pi) log(1 + e^{pi y}) (real, and phi'
     extends holomorphically across x = 1).  Near 0: phi'(nu) = -(1/pi) log(i pi nu) + O(|nu|).  phi'(x+iy) = O(1 + |y|) for |nu| >= 1.
(F4) h_x - i h_y = phi'; h_y = (1/pi) arg(1 - e^{-i pi nu}) lies in [0, 1].
(F5) Legendre identity (Q_star/M3_PROOF.md s.1):  h(x+iy) - p y >= Phi_c(x,p) := L(x) + L(p) + L(1-x-p) for all real y,
     0 <= x <= 1, 0 <= p <= 1-x;  L(t) = Cl2(2 pi t)/(2 pi^2).

CONFIGURATIONS.  For M >= 1 and 0 < s <= 1 let C_M(s) be the set of nu = (nu_1, ..., nu_M), nu_k = x_k + i y_k in S-bar with
sum_k x_k = s.  To nu attach the positive measure of mass M
        sigma_nu := sum_k Cauchy(y_k, x_k),     Cauchy(y, x) has density (1/pi) x / (x^2 + (t - y)^2),  Cauchy(y, 0) := delta_y,
its distribution function F(t) = sigma_nu((-oo, t]) = sum_k omega(t; nu_k),  omega(t; x+iy) := 1/2 + (1/pi) arctan((t-y)/x)
(omega(t; iy) := 1{t >= y}), and its INTEGER QUANTILES  gamma_j := min{t : F(t) >= j},  j = 1, ..., M-1.
Since s > 0, at least one x_k > 0, so F is continuous-plus-jumps and STRICTLY increasing; the gamma_j are finite and
#{j : gamma_j <= t} = min(floor F(t), M-1) for every t.   For x > 0, omega(t; .) is harmonic and
omega(t; nu) = Re[1/2 + (i/pi) log(nu - it)],  so its holomorphic derivative is (i/pi)/(nu - it).

THE FUNCTIONAL.  With alpha = alpha_s := (1-s)/s and S(nu) := sum_k x_k y_k,
        T(nu) := sum_k h(nu_k) - sum\_{j=1}^{M-1} (gamma_j)\_+ - alpha (S(nu))\_+ .

MAIN THEOREM.  T(nu) >= 0 for every M >= 1, 0 < s <= 1 and nu in C_M(s).

(For s = 1 this is exactly (\*) for rank-one B, by Lemma 1; the s < 1 statements are needed to close the induction.)

## 1. Matrix realisation and the trace identity

LEMMA 1.  Let 0 < s <= 1, v in C^M a unit vector, g Hermitian, P = 1 - vv\*, and nu_1..nu_M = spec(s vv\* + i g) (algebraic
multiplicity), nu_k = x_k + i y_k.
 (a) 0 <= x_k <= s and sum x_k = s, i.e. nu is in C_M(s).
 (b) If all x_k > 0, the multiset spec(PgP restricted to ran P) equals {gamma_1, ..., gamma\_{M-1}}.
 (c) Conversely every nu in C_M(s) with all x_k > 0 arises in this way.
Proof.  (a) Re nu_k lies in the numerical range [0, s] of the Hermitian part s vv\*; sum nu_k = Tr(s vv\* + ig).
(b) A := g - i s vv\* has eigenvalues zeta_k := -i nu_k = y_k - i x_k, and A\* = g + i s vv\* has eigenvalues conj(zeta_k).  With
G(z) := <v, (g - z)^{-1} v>, the matrix determinant lemma gives det(A - z) = det(g - z)(1 - i s G(z)) and
det(A\* - z) = det(g - z)(1 + i s G(z)).  Put R(z) := det(A - z)/det(A\* - z) = prod_k (zeta_k - z)/(conj(zeta_k) - z).
For real t, (zeta_k - t)/(conj(zeta_k) - t) = conj(w)/w with w = (y_k - t) + i x_k, and arg w = pi/2 + arctan((t-y_k)/x_k)
= pi omega(t; nu_k); hence R(t) = exp(-2 pi i F(t)).  For real t not in spec g, G(t) is real and R(t) = (1 - isG)/(1 + isG),
so R(t) = 1 iff G(t) = 0, while R = -1 at the poles of G.  Generic case: v cyclic for g and spec g simple.  Then
G = sum_i p_i/(s_i - z) (p_i > 0, M distinct real poles), G has exactly M-1 real zeros, all simple, and
det((PgP - t)|ran P) = G(t) det(g - t) (Cramer), so spec(PgP|ran P) = zeros of G.  These are exactly the real t with
R(t) = 1, i.e. F(t) in {1, ..., M-1}; as F is continuous and strictly increasing from 0 to M, these are the gamma_j.
(This covers every case: if all x_k > 0 then v is cyclic for g and spec g is simple, since an eigenvector of g orthogonal
to v, or a two-dimensional eigenspace of g, which always contains such a vector, would be an eigenvector of s vv\* + ig with
real part 0.)
(c) Given nu, put zeta_k = y_k - i x_k, R(z) := prod_k (zeta_k - z)/(conj(zeta_k) - z) and G := (1 - R)/(i s (1 + R)).
For Im z > 0, |z - zeta_k| > |z - conj(zeta_k)| (x_k > 0), so |R| > 1, Re[(1-R)/(1+R)] < 0 and Im G > 0.  On R, |R| = 1, so G
is real off its poles; R = 1 + 2 i s/z + O(z^-2), so G = -1/z + O(z^-2).  A rational Herglotz function with these properties
is sum_i p_i/(s_i - z) with real s_i, p_i > 0, sum p_i = 1; its poles are the M real points where R = -1, i.e. F in Z + 1/2.
With g := diag(s_i), v := (sqrt p_i): 1 - isG = 2R/(1 + R), so det(g - i s vv\* - z) is a polynomial of degree M vanishing
exactly at the zeros zeta_k of R; hence spec(s vv\* + ig) = {i zeta_k} = {nu_k}.  []

LEMMA 2 (trace identity).  For every nu in C_M(s):  sum_k (1 - x_k) y_k - sum_j gamma_j = alpha_s S(nu).
Proof.  If all x_k > 0, realise nu (Lemma 1(c)).  sum y_k = Tr g; sum x_k y_k = (1/2) Im Tr (s vv\* + ig)^2 = s<v,gv>;
sum gamma_j = Tr(PgP) = Tr g - <v,gv>.  So the left side is (1-s)<v,gv> = alpha_s S.  General nu: a point with x_k = 0 contributes an
atom delta\_{y_k} to sigma, which (Lemma 4's counting identity) adds exactly the quantile y_k; it contributes y_k to the
first sum and y_k to the second, and nothing to S; delete it and induct.  []

## 2. Easy cases, boundary points, near-boundary points

LEMMA 3 (easy cases).  Let nu in C_M(s).  (i) If all gamma_j <= 0 then T(nu) >= 0.  (ii) If all gamma_j >= 0 then T(nu) >= 0.
Proof.  (i) T = sum h(nu_k) - alpha (S)\_+.  By (F2), h(nu_k) >= (1-x_k)(y_k)\_+ >= alpha x_k (y_k)\_+, because
1 - x_k - alpha x_k = 1 - x_k/s >= 0.  Summing, sum h >= alpha sum x_k (y_k)\_+ >= alpha (S)\_+.
(ii) By Lemma 2 and (F2): T = sum_k [h(nu_k) - (1-x_k)y_k] + alpha S - alpha (S)\_+ = sum_k h(conj nu_k) - alpha (S)\_-,
and (i)'s argument applied to conj(nu) (same x_k, y_k -> -y_k) gives sum_k h(conj nu_k) >= alpha (-S)\_+ = alpha (S)\_-.  []

LEMMA 4 (boundary points).  Let M >= 2, nu in C_M(s), and x_m = 0 for some m.  Then T(nu) = T(nu'), where nu' in C\_{M-1}(s)
is nu with nu_m deleted.  If s = 1 and x_m = 1 for some m, then T(nu) = 0.
Proof.  F = F' + 1{t >= y_m}, F' the distribution function of nu' (mass M-1, strictly increasing since s > 0, so
F'(t) < M-1 for all finite t).  For every t:  min(floor F, M-1) = min(floor F', M-2) + 1{t >= y_m}.  Hence the quantile
multiset of nu is that of nu' together with y_m, and T(nu) = T(nu') + h(i y_m) - (y_m)\_+ = T(nu') (S and s are unchanged).
If x_m = 1 and s = 1, every other point has x = 0; deleting them one by one leaves the one-point configuration 1 + i y_m in
C_1(1), for which T = h(1 + i y_m) = 0.  []

LEMMA 5 (near-boundary points).  Let R >= 1, nu in C_M(s) with |y_k| <= R for all k, and 0 < x_m <= eta for some m, where
eta <= s/2.  Let nu^0 be nu with nu_m replaced by i y_m (so nu^0 is in C_M(s'), s' = s - x_m >= s/2).  Then
     |T(nu) - T(nu^0)| <= E(eta) := eta (R + 1 + log(1/eta)) + 4 eta R/s + 8 M (R+1) sqrt(2 eta/s).
Proof.  (a) |h(nu_m) - h(i y_m)| <= int_0^eta |h_x(t + i y_m)| dt, and for |y| <= R, 0 < t <= 1/2:
e^{-pi R} 2t <= e^{pi y} sin(pi t) <= |1 - e^{pi y} e^{-i pi t}| <= 1 + e^{pi R}, so |h_x| = (1/pi)|log|1 - e^{-i pi nu}|| <=
R + 1 + (1/pi) log(1/t) (we use t <= eta <= s/2 <= 1/2); integrating gives <= eta (R + 1 + log(1/eta)).
(b) |alpha_s (S)\_+ - alpha\_{s'} (S')\_+| <= alpha_s |S - S'| + |alpha_s - alpha\_{s'}| |S'| <= eta R/s + (eta/(s s')) s R <= 4 eta R/s.
(c) Quantiles.  sum_j (gamma_j)\_+ = int_0^oo (M - 1 - min(floor F(t), M-1)) dt, the same for nu^0 with F^0.  For |t| > R + 1
both F, F^0 are < 1 or > M-1 (each Cauchy(y_k, x_k) puts mass <= x_k/(pi (|t - y_k|)) beyond t, and sum x_k <= 1), so the
two integrands differ only on the set E of t in [-R-1, R+1] for which an integer lies between F(t) and F^0(t).  Write
F = F'' + omega(.; nu_m), F^0 = F'' + 1{. >= y_m}, F'' the distribution of the other M-1 points.  If |t - y_m| >= rho then
|F - F^0| <= delta := eta/(pi rho) (|omega(t; nu_m) - 1{t >= y_m}| = (1/pi) arctan(x_m/|t - y_m|)), and an integer between
F and F^0 forces F''(t) to lie within delta of an integer n in {0, ..., M-1}.  On [-R-1, R+1], F'' has density
>= d := (s'/(M-1)) / (pi (1 + (2R+1)^2)) (the point of largest x among the others has x >= s'/(M-1) and |t - y| <= 2R+1).
So |E| <= 2 rho + 2 M delta/d = 2 rho + 2M(M-1)(1 + (2R+1)^2) eta/(rho s'); with rho = sqrt(M(M-1)(1+(2R+1)^2) eta/s')
this is <= 4 sqrt(M(M-1)(1+(2R+1)^2) eta/s') <= 8 M (R+1) sqrt(2 eta/s).  The two integrands differ by at most 1.  []

COROLLARY 5.1.  T is continuous on C_M(s).  Proof: h is continuous on S-bar; nu -> sigma_nu is weakly continuous on C_M(s)
(including at x_k = 0, where Cauchy(y, x) -> delta_y); since s > 0, the limiting distribution function is strictly increasing,
and integer quantiles of a strictly increasing distribution function are continuous under weak convergence; S and alpha_s
are continuous (s is fixed on C_M(s)).  Lemma 5 is the quantitative version used in Section 5, where s changes.

## 3. The zero-count lemma

LEMMA 6.  Let J >= 1, 0 < g_1 < ... < g_J, c_1, ..., c_J > 0, mu real, a >= 0, eps > 0, and
     f(nu) := phi'(nu) + (i/pi) sum_j c_j/(nu - i g_j) - mu + i a nu + eps pi cos(pi nu)        (nu in S).
Then f has at most J + 1 zeros in S, counted with multiplicity.
Proof.  f is holomorphic on S, extends holomorphically across x = 1 and across {x = 0, y < 0}, and has simple poles at
i g_j and a logarithmic singularity at 0 on the left boundary line.  Count the zeros in Omega = {delta < x < 1, |y| < R} by
the argument principle (contour avoiding zeros).  ORDER OF LIMITS: fix R (large, no zeros on |y| = R); the left side of
 the contour is the straight segment x = delta, which passes to the right of the poles i g_j and of the corner 0; let
 delta -> 0 (in particular delta << exp(pi C_0), C_0 := -(1/pi) sum_j c_j/g_j - mu + eps pi, so that near 0 the corner
 term -(1/pi) log(i pi nu) dominates, and delta small enough that the pole terms dominate near each i g_j); then R -> oo.
 (delta -> 0 is genuinely needed: a pole can carry a zero of f extremely close to the line x = 0 -- the re-verification observed one
 at x ~ 2e-30 -- which a contour at any fixed delta would miss.)
 Right side x = 1: Im f(1+iy) = (1/pi) sum_j c_j/(1 + (y - g_j)^2) + a > 0, and Re f(1 + iy) -> -oo as y -> +-oo (the term
   -eps pi cosh(pi y) dominates).  So f stays in the upper half-plane and the change of arg tends to 0.
 Top y = R (x from 1 to delta): f = (eps pi/2) e^{pi R} e^{-i pi x}(1 + o(1)), change of arg -> +pi.
 Bottom y = -R (x from delta to 1): f = (eps pi/2) e^{pi R} e^{i pi x}(1 + o(1)), change of arg -> +pi.
 Left side x = delta, y from R down to 0+: f -> r(y) - i with r real (F3; the pole terms and i a nu are real at x = 0),
   r(R) -> +oo (penalty), r -> +oo as y -> 0+ (the term -(1/pi) log(e^{pi y} - 1)), r -> +oo just above each g_j and -oo just
   below.  Along the line Im = -1, going from +oo to +oo contributes 0 and from -oo to +oo contributes +pi; passing to the
   right of each simple pole contributes +pi (the pole term (c_j/pi)(u + i delta)/(delta^2 + u^2), u = y - g_j from
   + to -, sweeps the upper half-plane).  Segments: [R, g_J]: 0; J poles: J pi; J-1 gaps: (J-1) pi; [g_1, 0+]: pi.
   Total 2J pi.
 Corner: f = -(1/pi) log(i pi nu) + O(1); Re f -> +oo while Im f stays bounded, change of arg -> 0.
 Left side, y from 0- down to -R: f(delta + iy) -> r\_-(y) real, r\_-(0-) = +oo, r\_-(-R) -> +oo.  f extends holomorphically
   across this segment with real boundary values, so near a real zero y_0 of order p, f ~ c (nu - i y_0)^p and the contour
   passing to its right contributes -p pi; elsewhere arg f stays near 0 or pi mod 2 pi.  Total -Z pi, Z = total order of the
   zeros of r\_- on (-R, 0), Z even (the argument returns to 0 mod 2 pi).
 Sum: (2J + 2 - Z) pi + o(1).  Hence #zeros in Omega = J + 1 - Z/2 <= J + 1, and letting delta -> 0, R -> oo (zeros of f in
 S are isolated; those near the lower-left boundary are zeros of the holomorphic extension) proves the claim.  []

## 4. Interior local minima

LEMMA 7.  Let M >= 2, 0 < s <= 1, eps > 0, u(nu) := sin(pi x) cosh(pi y) (= Re sin(pi nu), harmonic, >= 0 on S-bar), and
T_eps(nu) := T(nu) + eps sum_k u(nu_k).  If nu in C_M(s) has all x_k in (0,1) and is a local minimum of T_eps on C_M(s),
then T(nu) >= 0.
Proof.  Let J\_> = #{j : gamma_j > 0}, J\_>= = #{j : gamma_j >= 0}.  If J\_> = 0 or J\_>= = M-1, Lemma 3 gives T(nu) >= 0.  Assume
1 <= J\_> <= J\_>= <= M-2 and derive a contradiction.  Let I = {j : gamma_j(nu) > 0} and
   T~(nu') := sum_k [h + eps u](nu'_k) - sum\_{j in I} gamma_j(nu') - a sum_k x'\_k y'\_k,     a := alpha 1{S(nu) > 0}.
Near nu, T_eps <= T~ with equality at nu (for j not in I, -(gamma_j)\_+ <= 0; for S(nu) <= 0, -alpha (S')\_+ <= 0), so nu is a
local minimum of T~ on the smooth manifold {sum x'\_k = s} in S^M.  The gamma_j are smooth (implicit function theorem,
dF/dt > 0) with grad\_{nu_k} gamma_j = -grad omega(gamma_j; nu_k)/F'(gamma_j).  Lagrange: for some mu and all k,
grad Xi(nu_k) = 0, where
   Xi(z) := h(z) + eps u(z) + sum\_{j in I} c_j omega(gamma_j; z) - a Re z Im z - mu Re z,     c_j := 1/F'(gamma_j) > 0,
is harmonic on S.  Writing Xi = Re Fr (Fr holomorphic on S), Fr' = f with f as in Lemma 6 (g_j = gamma_j, j in I; J = J\_>):
indeed the holomorphic derivatives of h, u, omega(gamma; .), xy, x are phi', pi cos(pi z), (i/pi)/(z - i gamma), -iz, 1.
So f(nu_k) = 0 for all k.
MULTIPLICITY.  Let m points coincide at nu\*.  For 2 <= n <= m perturb n of them to nu\* + eta w^q (q = 0..n-1, w = e^{2 pi i/n});
this keeps sum x fixed.  Then delta F(t) = O(|eta|^n) uniformly near the gamma_j (which are at positive distance from nu\*), so
gamma_j changes by -delta F(gamma_j)/F'(gamma_j) + O(|eta|^{2n}), and
   T~(perturbed) - T~(nu) = sum_q [Xi(nu\* + eta w^q) - Xi(nu\*)] + O(|eta|^{2n}) = n Re[Fr^{(n)}(nu\*) eta^n]/n! + O(|eta|^{2n}).
Minimality for all small complex eta forces Fr^{(n)}(nu\*) = 0, n = 2..m; with f(nu\*) = 0 this says f vanishes to order >= m at
nu\*.  Hence f has at least M zeros in S counted with multiplicity, while Lemma 6 (J = J\_> >= 1) allows at most
J\_> + 1 <= M - 1.  Contradiction.  []

## 5. Proof of the Main Theorem

Induction on M.  M = 1: T = h(s + iy) - (1-s) y\_+ >= 0 by (F2) (no quantiles; alpha s y\_+ = (1-s) y\_+).
Let M >= 2, assume the theorem for all smaller sizes and all s, and suppose T(nu^0) = -d < 0 for some nu^0 in C_M(s).
Fix eps > 0 with eps sum_k u(nu^0_k) <= d/4, and for R > max |y^0_k| let K_R = {nu in C_M(s) : |y_k| <= R}, compact.
T_eps is continuous on K_R (Cor. 5.1); let nu\* minimise it there.  Then T(nu\*) <= T_eps(nu\*) <= T_eps(nu^0) <= -3d/4.
(a) FACE POINTS.  T is Lipschitz in each y_k with constant L := M + alpha: |h_y| <= 1; (.)\_+ is 1-Lipschitz; each gamma_j is
nondecreasing and 1-Lipschitz in y_k (raising y_k by e >= 0 lowers F pointwise, and F\_{new}(t + e) >= F\_{old}(t) because
F_new(t + e) = F_others(t + e) + omega(t; nu_k) >= F_old(t); so gamma_j(old) <= gamma_j(new) <= gamma_j(old) + e);
|dS/dy_k| = x_k <= 1.
If y\*\_k = R, moving y_k down by t lowers the penalty by >= eps pi sin(pi x\*\_k) sinh(pi(R - t)) t and raises T by <= L t; so
minimality forces sin(pi x\*\_k) <= L/(eps pi sinh(pi R)), i.e. min(x\*\_k, 1 - x\*\_k) <= eta_R := L/(2 eps pi sinh(pi R)).  Same at
y\*\_k = -R.
(b) If a face point has x\*\_k >= 1 - eta_R (only possible for s = 1 once eta_R < 1 - s), all other points have x <= eta_R.
Replacing them one by one by boundary points (Lemma 5, each step error <= E(eta_R)) and deleting them (Lemma 4) leaves a
one-point configuration, for which T >= 0 (M = 1).  So T(nu\*) >= -(M-1) E(eta_R).
(c) Otherwise, if face points exist, each has x\*\_k <= eta_R; there are fewer than M of them once M eta_R < s.  Replace them by
boundary points (Lemma 5) and delete them (Lemma 4): T(nu\*) >= T(nu'') - M E(eta_R), with nu'' in C\_{M'}(s''), M' < M,
s'' >= s - M eta_R > 0, so T(nu'') >= 0 by the induction hypothesis.
(d) Otherwise |y\*\_k| < R for all k and nu\* is a local minimum of T_eps on C_M(s).  If some x\*\_k = 0, Lemma 4 and the induction
hypothesis give T(nu\*) >= 0; if some x\*\_k = 1 (s = 1), T(nu\*) = 0 (Lemma 4); otherwise Lemma 7 gives T(nu\*) >= 0.
Since E(eta_R) -> 0 as R -> oo (eps fixed), every case contradicts T(nu\*) <= -3d/4 for R large.  []

## 6. Consequences

COROLLARY 1 ((\*) for rank-one B).  For every M, unit v in C^M, Hermitian g and real lambda, with P = 1 - vv\*:
        sum\_{nu in spec(vv\* + ig)} h_lambda(nu) >= Tr[(P(g - lambda)P)\_+].
Proof.  Replace g by g - lambda.  For g with no eigenvector orthogonal to v (a dense set) all x_k > 0 and Lemma 1(b) (s = 1)
shows LHS - RHS = T(spec(vv\* + ig)) >= 0.  Both sides are continuous in g.  []

COROLLARY 2 (dual form with a rank-one outcome).  For every PVM (A, B, C) on C^M in which some outcome has rank <= 1, and every
ordered ONB:   |Tr(A iT(B))| <= sum_k Phi(A_kk, B_kk, C_kk).
Proof.  Tr(A iT(B)) = Tr(B iT(C)) = Tr(C iT(A)) (A + B + C = 1, Tr(X iT(Y)) = -Tr(Y iT(X))), and it changes sign under a
transposition, while the right side is symmetric; so we may put the outcome of rank <= 1 in the middle slot (both
orientations).  Rank 0: the left side is 0 and Phi >= 0.  Rank 1: take g = diag(y) + iT(B) in the given basis (then B + ig is
upper triangular, spec = {B_kk + i y_k}); Corollary 1 gives sum_k h(B_kk + i y_k) >= Tr[(PgP)\_+] >= Tr(Ag)
= sum_k A_kk y_k + Tr(A iT(B)) (A <= P).  So Tr(A iT(B)) <= sum_k [h(B_kk + i y_k) - A_kk y_k] for all y; by (F5) the infimum
over y_k equals Phi_c(B_kk, A_kk) = Phi(A_kk, B_kk, C_kk) (attained at the stationary point when 0 < A_kk < 1 - B_kk,
Q_star/M3_PROOF.md s.1; approached as y_k -> -+oo when A_kk = 0 or A_kk = 1 - B_kk).  []

COROLLARY 3 ((\*) for rank <= 1 or corank <= 3; all M <= 5).  (\*) holds for every projection B on C^M with rank B <= 1 or
rank(1 - B) <= 3, every Hermitian g and every lambda.  In particular (\*) holds for all projections when M <= 5.
Proof.  Rank <= 1: Corollary 1 (rank 0 trivial).  Corank <= 3: in a Schur basis of B + i(g - lambda) one has
g - lambda = diag(y) + iT(B), and with Q the projection onto the positive part of P(g - lambda)P,
Tr[(P(g-lambda)P)\_+] = sum_k Q_kk y_k + Tr(Q iT(B)) <= sum_k [Q_kk y_k + Phi(Q_kk, B_kk, (P-Q)\_kk)] <= sum_k h(B_kk + i y_k)
(Corollary 2 applies because rank Q + rank(P - Q) = rank P <= 3 forces one of them to be <= 1; then (F5)).  For M <= 5,
every projection has rank <= 1 or corank <= 3.  []

REMARK.  This section gives an independent proof of (\*) for rank B <= 1, corank B <= 3 and all M <= 5.  The general case
(all M) is proved by a different method in Q_2bmv/PROOF.md (explicit positive density for 2BMV); the two proofs agree where
both apply.  (The dual form for PVMs all of whose outcomes have rank >= 2 is implied by (\*) for all M via the easy half of
Q-L12 together with Corollary 2's argument; its smallest instance is ranks (2,2,2) on C^6.)

## 7. Numerical cross-checks (not part of the proof)
 - r01: spec(PgP) = integer quantiles of sum Cauchy(y_k, x_k): error <= 9e-12 (M <= 8, scales up to 30).
 - r05: same for s < 1 (error 1e-12); trace identity (Lemma 2) error 1e-12; zero count of Lemma 6 <= J+1 in 200 random
   instances with penalty (and r03: 300 instances without penalty).
 - r02/r04: subcritical inequality T >= 0 in matrix form, 400 adversarial Nelder-Mead runs, worst -4.7e-13 (rounding).
 - r07: psi = i phi' satisfies psi^3 = id and nu + psi(nu) + psi^2(nu) = 1 to 40 digits (order-3 automorphism of S, fixed point 1/3).
 - Re-verification (REVIEW.md, rv_01..rv_11): every item OK; 1800 extreme instances of Lemma 6; end-to-end rank-one (\*)
   at M = 3..8 with entries up to 300, (\*) at M = 5 for all projections, dual form with a rank-one outcome at M = 5..7; all
   double-precision near-violations positive at 50 digits.
