# Q_2bmv/PROOF.md -- 2BMV is TRUE: the explicit density nu_2 = (1/2pi) sum |Im x_i|, and the strip inequality (\*) for every M

RE-VERIFIED 2026-10-02 (internal check, Q_2bmv_check/REFEREE.md): sections 0-5 CORRECT, no gap; independent numerics agree (Theorem 1 to
6.8e-13 at 82 complex points, Theorem 2 to 1.3e-12 at 51 (instance, lambda) pairs).  Section 6 corrected after the re-verification.

Status labels: PROVED = complete proof written below; NUMERICAL = checked numerically (scripts in this folder).

## 0. Statements

Throughout: B is an orthogonal projection on C^M of rank r, P = 1 - B, g is Hermitian, g_d := BgB + PgP (the pinching),
lmin, lmax are the extreme eigenvalues of g, ||.|| is the operator norm.  Tr_P e^{aPgP} denotes the trace over ran P of the
exponential of the compression PgP|\_{ran P} (similarly Tr_B), and Tr[(P(g - lam)P)\_+] = sum\_{mu in spec(PgP|ran P)} (mu - lam)\_+.

    D(a,t) := Tr e^{ag - tP} - e^{-t} Tr_P e^{aPgP} - Tr_B e^{aBgB},        (a,t) in C^2.

For s real and 0 < tau < 1 let

    p_{s,tau}(x) := det(g - s - x(P - tau)),      q_{s,tau}(x) := det(g_d - s - x(P - tau)),

and let x_1(s,tau), ..., x_M(s,tau) be the roots of p\_{s,tau} (with multiplicity); since P - tau is invertible they are the
eigenvalues of (P - tau)^{-1}(g - s) = (P/(1-tau) - B/tau)(g - s).  Define

    F(s,tau) := (1/2pi) sum_{i=1}^M |Im x_i(s,tau)|   for 0 < tau < 1,       F(s,tau) := 0 otherwise.

THEOREM 1 (2BMV, explicit form) [PROVED, s.1-4].  F >= 0, F is continuous on R x (0,1), F(s,tau) = 0 unless lmin < s < lmax,
F(s,tau) <= (M/2pi) ||g - s|| / sqrt(tau(1-tau))  (so F is in L^1(R^2) with compact support), and for ALL (a,t) in C^2

    D(a,t) = a^2 int_0^1 int_R e^{as - t tau} F(s,tau) ds dtau.

In particular the conjecture Q-C3 (2BMV) holds, with nu_2 = F(s,tau) ds dtau, an absolutely continuous POSITIVE measure.

THEOREM 2 (the strip inequality (\*) for every M) [PROVED, s.5].  For every lam in R,

    sum_{nu in spec(B + ig)} h_lam(nu) - Tr[(P(g - lam)P)_+]  =  int_0^1 int_R K_{1-tau}(s - lam) F(s,tau) ds dtau  >=  0,

h_lam(x + iy) = -(1/pi^2) Im Li2(e^{pi(y - lam)} e^{-i pi x}) (with its continuous boundary values on x = 0, 1; on x = 0 with
y > lam the Li2 argument lies on the cut [1, oo) and the value is the limit from inside the strip, Im Li2(r - i0) = -pi log r), and
K_X(u) = sin(pi X)/(2(cosh(pi u) - cos(pi X))) the Poisson kernel of the strip 0 < X < 1 for its left edge.  Equality holds
(for one, equivalently all, lam) iff [B, g] = 0.

COROLLARIES [PROVED].  (i) tau-marginal sum rule: int_R F(s,tau) ds = ||BgP||\_F^2 for every tau in (0,1) (s.4, Remark 4.3).
(ii) Stahl's BMV theorem for projections with an explicit density: for Hermitian A, t -> Tr e^{A - tP} is the Laplace transform
of the positive measure Tr_B(e^{BAB}) delta_0 + Tr_P(e^{PAP}) delta_1 + (int_R e^s F_A(s,tau) ds) dtau on [0,1] (take a = 1, g = A).
(iii) the real-slice positivity Q-L9 (U_xi >= 0) is the Radon transform of F >= 0.  (iv) Via SHARED_LEMMAS Q-T1, Q-T2, every
statement there that was "PROVED modulo (\*)" is now unconditional (that chain is not re-checked here).
THEOREM 3 (side result, s.7) [PROVED]: the same closed form for an arbitrary Hermitian B (atoms at ALL eigenvalues of B), which
contains Stahl's theorem.  PRIOR WORK (s.8): the mechanism -- and a BMV proof by a positive planar measure with density
(1/2pi) sum Im(pencil eigenvalues) -- is in Heinavaara, arXiv:2310.03227; Theorem 3 is a variant of it, not a new BMV proof.
Numerical verification: s.6.

## 1. Elementary facts about the pencil

LEMMA 1.  Let 0 < tau < 1 and s real.
 (a) Every root x of p\_{s,tau} satisfies |x| <= ||g - s|| / min(tau, 1 - tau); the same holds for q\_{s,tau} (with ||g_d - s|| <= ||g - s||).
 (b) Every NON-REAL root x of p\_{s,tau} satisfies |x| <= ||g - s|| / sqrt(tau(1 - tau)).
 (c) If s <= lmin or s >= lmax, all roots of p\_{s,tau} are real, i.e. F(s,tau) = 0.
 (d) All roots of q\_{s,tau} are real.
 (e) p\_{s,tau} and q\_{s,tau} have degree M, the same leading coefficient c_tau = det(-(P - tau)) = (-1)^M (1-tau)^{M-r} (-tau)^r
     and the same sum of roots.
 (f) F is continuous on R x (0,1).
Proof. Roots x are the values with (g - s)v = x(P - tau)v for some unit vector v.
 (a) P - tau has eigenvalues 1 - tau and -tau, so |(P - tau)v| >= min(tau, 1 - tau) and |x| |(P - tau)v| = |(g - s)v| <= ||g - s||.
 (b) <v,(g - s)v> = x <v,(P - tau)v> with both inner products real; if Im x != 0 then <v,(P - tau)v> = 0, i.e.
     |Pv|^2 = tau, |Bv|^2 = 1 - tau, hence |(P - tau)v|^2 = (1-tau)^2 |Pv|^2 + tau^2 |Bv|^2 = tau(1 - tau), and (a)'s argument gives (b).
 (c) If g - s is semidefinite and Im x != 0, then by (b)'s argument <v,(g - s)v> = 0, so (g - s)v = 0 (semidefinite), so
     x(P - tau)v = 0, so v = 0 (P - tau invertible, x != 0): contradiction.
 (d) g_d - s - x(P - tau) is block diagonal: on ran B it is BgB - s + x tau, on ran P it is PgP - s - x(1 - tau); its determinant
     vanishes iff x = (s - mu)/tau (mu in spec BgB|ranB) or x = (mu - s)/(1 - tau) (mu in spec PgP|ranP): real.
 (e) p(x) = det(-(P - tau)) det(x - (P - tau)^{-1}(g - s)), so the roots sum to Tr[(P - tau)^{-1}(g - s)]; likewise for q with g_d.
     (P - tau)^{-1} = P/(1-tau) - B/tau commutes with B, so Tr[(P - tau)^{-1}(g - g_d)] = Tr[(P - tau)^{-1}(BgP + PgB)] = 0.
 (f) The roots of a polynomial of fixed degree depend continuously (as an unordered M-tuple) on its coefficients, which are
     polynomials in (s, tau, 1/tau, 1/(1-tau)); sum_i |Im x_i| is a continuous symmetric function of the M-tuple.            QED
Consequently F <= (M/2pi)||g - s||/sqrt(tau(1-tau)), supp F is contained in K := [lmin, lmax] x [0,1], and F is in L^1(R^2).

LEMMA 2 (Jensen-type identity).  Let p(x) = c prod\_{i=1}^M (x - x_i) and q(x) = c prod\_{i=1}^M (x - y_i) with c != 0, all y_i real,
and sum_i x_i = sum_i y_i.  Then log|p/q| is in L^1(R) and   int_R log|p(x)/q(x)| dx = pi sum_i |Im x_i|.
Proof. Write x_i = alpha_i + i beta_i.  Then log|p/q| = A + C with A(x) = sum_i (1/2) log(1 + beta_i^2/(x - alpha_i)^2) >= 0 and
C(x) = sum_i [log|x - alpha_i| - log|x - y_i|].  Each summand of A is integrable with int_R (1/2)log(1 + b^2/u^2) du = pi|b|
(substitute u = |b|v: |b| int_0^inf log(1 + v^-2) dv = |b| [v log(1 + v^-2) + 2 arctan v]\_0^inf = pi|b|).
C has only logarithmic singularities and, for |x| -> inf, C(x) = sum_i [log|1 - alpha_i/x| - log|1 - y_i/x|] = O(x^-2) because
sum alpha_i = Re sum x_i = sum y_i; so C is in L^1.  For L > max(|alpha_i|, |y_i|),
    int\_{-L}^{L} log|x - a| dx = (L - a)log(L - a) + (L + a)log(L + a) - 2L =: m_L(a)   (a real),
and m_L is even and smooth in a with m_L''(a) = 2L/(L^2 - a^2), so m_L(a) = m_L(0) + a^2/L + O(a^4/L^3).  Hence
int\_{-L}^{L} C = sum_i (alpha_i^2 - y_i^2)/L + O(L^-3) -> 0, and since C is in L^1, int_R C = 0.                                  QED

LEMMA 3 (real slices; the data of Q-L9).  For xi real let lambda_j(xi) (j = 1..M) be the eigenvalues of g - xi P and
lambda^0_j(xi) those of g_d - xi P (= spec(BgB|ranB) together with spec(PgP|ranP) - xi).  Put
    U_xi(w) := sum_j [ (w - lambda_j(xi))\_+ - (w - lambda^0_j(xi))\_+ ],      N_xi(w) := sum_j [ 1\_{w > lambda_j(xi)} - 1\_{w > lambda^0_j(xi)} ].
Then (a) U_xi is continuous, piecewise linear, compactly supported, absolutely continuous with U_xi' = N_xi a.e.;
 (b) for every complex a != 0:  int_R e^{aw} U_xi(w) dw = D(a, a xi)/a^2;
 (c) the Hilbert transform (Hf)(w) = (1/pi) p.v. int f(u)/(w - u) du (L^2 multiplier -i sgn sigma) of N_xi is
        (H N_xi)(w) = (1/pi) log| det(g - xi P - w) / det(g_d - xi P - w) |    for w outside the two spectra.
Proof. (a) For w below all eigenvalues U_xi = 0; above all of them U_xi(w) = sum_j (lambda^0_j - lambda_j) = Tr(g_d - xi P) - Tr(g - xi P) = 0.
 (b) U_xi'' = sum_j (delta\_{lambda_j} - delta\_{lambda^0_j}) as distributions and U_xi has compact support, so integrating by parts twice
     int e^{aw} U_xi dw = a^-2 sum_j (e^{a lambda_j} - e^{a lambda^0_j}) = a^-2 [Tr e^{a(g - xi P)} - Tr_B e^{aBgB} - e^{-a xi} Tr_P e^{aPgP}]
     = a^-2 D(a, a xi).
 (c) Pair lambda_j with lambda^0_j: 1\_{w > lambda} - 1\_{w > lambda0} = +-1 of the interval between them, and
     (1/pi) int_alpha^beta du/(w - u) = (1/pi) log|(w - alpha)/(w - beta)|; summing over j gives (1/pi) log|prod(w - lambda_j)/prod(w - lambda^0_j)|.
     (The p.v.-kernel and the L^2-multiplier definitions of H agree on L^2, M. Riesz/Titchmarsh.)                              QED
(Positivity of U_xi -- Schur pinching -- is NOT used anywhere below; it follows from Theorem 1.)

LEMMA 4 (limits).  For Hermitian A:  lim\_{t->+inf} Tr e^{A - tP} = Tr_B e^{BAB}  and  lim\_{t->-inf} e^{t} Tr e^{A - tP} = Tr_P e^{PAP}.
Proof. Shifting A by a constant multiplies both sides by the same factor, so assume A >= 1.  Let mu_1 >= ... >= mu_M be the
eigenvalues of H_t = A - tP and beta_1 >= ... >= beta_r those of BAB|ranB.  Min-max with subspaces of ran B (where P = 0) gives
mu_k >= beta_k (k <= r).  For v = b + p (b in ran B, p in ran P) and t > ||A||:  <v, H_t v> <= <b,Ab> + 2||A|| |b||p| - (t - ||A||)|p|^2
<= <b, (A + eps_t) b>, eps_t = ||A||^2/(t - ||A||); the form v -> <Bv,(A + eps_t)Bv> has top r eigenvalues beta_k + eps_t (> 0, the
others are 0), so mu_k <= beta_k + eps_t for k <= r.  Finally mu\_{r+1} <= max over unit w in ran P of <w, H_t w> <= ||A|| - t (min-max
with the codimension-r subspace ran P).  Hence Tr e^{H_t} -> sum_k e^{beta_k}.  The second limit is the first one with B and P
exchanged, since e^t Tr e^{A - tP} = Tr e^{A + tB} = Tr e^{A - |t| B} for t < 0.                                            QED

## 2. Step 0-1: the distribution nu_2 (Paley-Wiener-Schwartz), without the Weyl calculus

Step 0.  D is entire on C^2.  D(0,t) = Tr e^{-tP} - (M - r)e^{-t} - r = 0, and dD/da(0,t) = Tr(g e^{-tP}) - e^{-t}Tr(PgP) - Tr(BgB) = 0
because e^{-tP} = B + e^{-t}P.  Hence G(a,t) := D(a,t)/a^2 is entire on C^2.  (Explicitly, G(a,t) = int_0^1 (1-u) d_a^2 D(ua,t) du, which is
jointly holomorphic.)

Step 1.  Put Ghat(zeta) := G(-i zeta_1, i zeta_2) (zeta in C^2), so that e^{-i(zeta_1 s + zeta_2 tau)} = e^{as - t tau} when
a = -i zeta_1, t = i zeta_2.  Let eta = Im zeta and H_K(eta) = sup\_{(s,tau) in K} (s eta_1 + tau eta_2), K = [lmin,lmax] x [0,1].
 Bound for D.  For complex a, t write X = ag - tP = H_1 + iH_2 with H_1 = (Re a)g - (Re t)P = eta_1 g + eta_2 P and H_2 Hermitian.
 For u(theta) = e^{theta X}v one has d/dtheta |u|^2 = 2<u, H_1 u> <= 2 lambda_max(H_1)|u|^2, so ||e^X|| <= e^{lambda_max(H_1)} and
 |Tr e^X| <= M e^{lambda_max(H_1)}.  Since lambda_max(eta_1 g + eta_2 P) = max\_{|v|=1} (eta_1 <v,gv> + eta_2 <v,Pv>) and
 (<v,gv>, <v,Pv>) lies in K, |Tr e^{ag - tP}| <= M e^{H_K(eta)}.  Likewise |e^{-t} Tr_P e^{aPgP}| <= (M-r) e^{eta_2 + max_mu eta_1 mu}
 <= (M-r)e^{H_K(eta)} (mu in spec PgP|ranP lies in [lmin,lmax], so (mu,1) is in K) and |Tr_B e^{aBgB}| <= r e^{H_K(eta)}.  So
 |D| <= 2M e^{H_K(eta)}.
 For |zeta_1| >= 1 this gives |Ghat(zeta)| <= 2M e^{H_K(eta)}.  For |zeta_1| < 1 apply the maximum principle to the entire function
 zeta_1 -> Ghat(zeta_1, zeta_2) on the disc |zeta_1| <= 2: |Ghat(zeta)| <= max\_{|z| = 2} |Ghat(z, zeta_2)| <= (M/2) e^{H_K(eta) + 3 c_K},
 c_K = max(|lmin|, |lmax|), because |Im z - eta_1| <= 3 and H_K(eta') <= H_K(eta) + c_K |eta'\_1 - eta_1|.  So |Ghat(zeta)| <= C e^{H_K(Im zeta)}.
 By the Paley-Wiener-Schwartz theorem (Hormander, ALPDO I, Thm 7.3.1) there is a distribution T with compact support in K whose
 Fourier-Laplace transform T(e^{-i<., zeta>}) equals Ghat(zeta); equivalently
        T(e^{as - t tau}) = G(a,t) = D(a,t)/a^2      for all (a,t) in C^2.                                                    (2.1)
 (T is the distribution nu_2 of Q-L9/Q-C3: by (2.1) it has the defining Laplace transform.)  On R^2, |Ghat| <= C (bounded).

## 3. Step 2: T = F on the open strip (Fourier slice + Lemma 2)

Let phi be in C_c^infty(R^2), phihat(k) = int phi(z) e^{-i k.z} dz.  Since T is compactly supported with bounded transform,
        T(phi) = (2pi)^{-2} int\_{R^2} Ghat(k) phihat(-k) dk                                                                    (3.1)
(Fourier inversion phi(z) = (2pi)^{-2} int phihat(k) e^{ik.z} dk and Hormander Thm 7.1.14).  The integrand is in L^1(R^2).
Change variables k = (sigma, -sigma xi), (sigma, xi) in (R\{0}) x R: this is a diffeomorphism onto R^2 minus the null line
{k_1 = 0} with Jacobian |sigma|.  By Fubini,
        T(phi) = (2pi)^{-2} int_R dxi int_R dsigma |sigma| Ghat(sigma, -sigma xi) phihat(-sigma, sigma xi).                    (3.2)
(i)  Ghat(sigma, -sigma xi) = G(-i sigma, -i sigma xi) = D(-i sigma, -i sigma xi)/(-i sigma)^2 = Uhat_xi(sigma) := int U_xi(w) e^{-i sigma w} dw
     by Lemma 3(b) with a = -i sigma.
(ii) phihat(-sigma, sigma xi) = int int phi(s,tau) e^{i sigma (s - xi tau)} ds dtau = psihat_xi(-sigma), psi_xi(w) := int_R phi(w + xi tau, tau) dtau
     (psi_xi is in C_c^infty(R)).
(iii) By Lemma 3(a), U_xi is absolutely continuous with derivative N_xi in L^1 and L^2, so i sigma Uhat_xi = Nhat_xi and
     |sigma| Uhat_xi(sigma) = (-i sgn sigma) Nhat_xi(sigma) = (H N_xi)^(sigma), with H N_xi in L^2.  By Parseval,
     (2pi)^{-1} int dsigma |sigma| Uhat_xi(sigma) psihat_xi(-sigma) = int_R (H N_xi)(w) psi_xi(w) dw
                                                       = int int (H N_xi)(s - xi tau) phi(s,tau) ds dtau
     (substitute w = s - xi tau for fixed tau; H N_xi is locally integrable -- logarithmic singularities -- and phi has compact support).
(iv) By Lemma 3(c) at w = s - xi tau, since g - xi P - (s - xi tau) = g - s - xi(P - tau):
        (H N_xi)(s - xi tau) = (1/pi) log| p\_{s,tau}(xi) / q\_{s,tau}(xi) |   (for tau not in {0,1}).
Therefore, for every phi in C_c^infty(R^2),
        T(phi) = (1/2pi^2) int_R dxi int int phi(s,tau) log|p\_{s,tau}(xi)/q\_{s,tau}(xi)| ds dtau.                                (3.3)
Now let supp phi be contained in [-S,S] x [delta, 1 - delta] (0 < delta < 1/2).  For (s,tau) there, Lemma 1(a) puts all roots of
p\_{s,tau} and q\_{s,tau} in the disc |x| <= R := (||g|| + S)/delta; by Lemma 1(e) both polynomials have the same leading coefficient and
root sum.  Hence, uniformly in (s,tau) in supp phi:
  - for |xi| <= 2R:  |log|p/q|(xi)| <= sum_i (|log|xi - x_i|| + |log|xi - y_i||), whose integral over [-2R, 2R] is at most
    2M sup\_{|z| <= R} int\_{-2R}^{2R} |log|xi - z|| dxi < inf;
  - for |xi| > 2R:  using |log|1 - z| + Re z| <= |z|^2 for |z| <= 1/2 and Re sum_i (x_i - y_i) = 0,
    |log|p/q|(xi)| = |sum_i (log|1 - x_i/xi| - log|1 - y_i/xi|)| <= 2M R^2/xi^2.
So the integrand of (3.3) is absolutely integrable on R x supp phi, Fubini applies, and by Lemma 2 (q has real roots, Lemma 1(d))
        T(phi) = int int phi(s,tau) [ (1/2pi^2) int_R log|p\_{s,tau}(xi)/q\_{s,tau}(xi)| dxi ] ds dtau = int int phi F ds dtau.     (3.4)
That is, T = F on the open strip S := R x (0,1).

## 4. Step 3: no singular part on the edges tau = 0, 1; end of proof of Theorem 1

F defines a distribution with compact support in K (Lemma 1), and T - F vanishes on S and outside K, so T - F is supported in
L_0 u L_1, L_j = [lmin,lmax] x {j}.  T - F has compact support, hence finite order, and its support splits into two disjoint compact
pieces; by the structure theorem for distributions supported in a hyperplane (Hormander Thm 2.3.5, applied to each piece after a
cutoff) there are N and compactly supported distributions alpha_k, beta_k on R with
        T - F = sum\_{k=0}^N [ alpha_k (x) delta^{(k)}(tau) + beta_k (x) delta^{(k)}(tau - 1) ].
Evaluating on e^{as - t tau} (allowed for compactly supported distributions) and using <delta^{(k)}, f> = (-1)^k f^{(k)}(0):
        R(a,t) := G(a,t) - int int e^{as - t tau} F ds dtau = sum_k t^k [ A_k(a) + e^{-t} B_k(a) ],   A_k(a) = alpha_k(e^{as}), B_k(a) = beta_k(e^{as}).
Fix a real a != 0.
 t -> +inf: G(a,t) = D(a,t)/a^2 -> 0 by Lemma 4 (A = ag); int int e^{as - t tau}F -> 0 by dominated convergence (F in L^1, compact
   support, e^{-t tau} <= 1 and -> 0 for tau > 0); t^k e^{-t} B_k -> 0.  Hence the polynomial sum_k A_k(a) t^k tends to 0, so A_k(a) = 0.
 t -> -inf: e^t G(a,t) = [e^t Tr e^{ag - tP} - Tr_P e^{aPgP} - e^t Tr_B e^{aBgB}]/a^2 -> 0 by Lemma 4; e^t int int e^{as - t tau} F
   = int int e^{as + t(1 - tau)} F -> 0 by dominated convergence; e^t sum A_k t^k = 0.  Hence sum_k B_k(a) t^k -> 0, so B_k(a) = 0.
a -> A_k(a), B_k(a) are entire (Fourier-Laplace transforms of compactly supported distributions) and vanish on R\{0}, hence vanish
identically, so alpha_k = beta_k = 0 (injectivity of the Fourier transform).  Thus T = F, i.e. by (2.1)
        D(a,t)/a^2 = int int e^{as - t tau} F(s,tau) ds dtau   for all (a,t) in C^2 (both sides entire).
Together with Lemma 1 this proves Theorem 1.                                                                                    QED

REMARK 4.1 (why this is natural).  The real slices of Q-L9 are the Radon projections of nu_2 in every non-horizontal direction;
s.3 is the 2D filtered back-projection nu_2(s,tau) = (1/2pi) int dxi (Lambda U_xi)(s - xi tau), Lambda = H d/dw.  The back-projected
data at (s,tau) is the logarithm of the characteristic polynomial xi -> p\_{s,tau}(xi) of the pencil through (s,tau), divided by the
pinched (real-rooted) one; integrating it over the line kills all real roots and leaves exactly pi |Im| of the non-real ones
(Lemma 2).  So positivity of nu_2 is a property of the inversion formula, not of the data: Q-X5 (no positive-combination proof
from the slices) is consistent with this, since the back-projection is not a positive operator.

REMARK 4.2 (number of non-real roots).  (P - tau)^{-1}(g - s) is self-adjoint for the indefinite form [u,v] = <u,(P - tau)v>, which
has M - r positive and r negative squares; eigenvectors for x and y with x != conj(y) are [.,.]-orthogonal, so the span of the
eigenvectors with Im x > 0 is [.,.]-neutral and has dimension <= min(r, M - r).  For generic (s,tau) the roots are simple, hence at
most min(r, M - r) conjugate pairs are present and F = (1/pi) sum\_{Im x_i > 0} Im x_i.  For rank-one B: F = (1/pi) Im x\_+ (a single
root in the upper half plane, if any).  (Remark only; not used.)

REMARK 4.3 (tau-marginal sum rule).  The second-order Duhamel formula gives d^2/da^2 Tr e^{ag - tP} at a = 0 equal to
int_0^1 Tr(g e^{-theta tP} g e^{-(1-theta)tP}) dtheta, and with e^{-theta tP} = B + e^{-theta t}P this equals
Tr(BgB)^2 + e^{-t}Tr(PgP)^2 + 2||BgP||\_F^2 (1 - e^{-t})/t; the first two terms are removed by the subtractions in D, so
G(0,t) = ||BgP||\_F^2 (1 - e^{-t})/t = ||BgP||\_F^2 int_0^1 e^{-t tau} dtau.  By Theorem 1 and uniqueness of Laplace transforms (the
s-marginal of F is continuous in tau by dominated convergence), int_R F(s,tau) ds = ||BgP||\_F^2 for EVERY tau in (0,1).
This is the one direction NOT used as input to the proof (the horizontal Radon projection), so it is an independent check (q02).

REMARK 4.4 (M = 2).  B = diag(1,0), g = [[alpha, c],[conj c, beta]]: p\_{s,tau}(x) = -tau(1-tau)x^2 + [tau(beta - s) - (1-tau)(alpha - s)]x
+ (alpha - s)(beta - s) - |c|^2 has discriminant (m(tau) - s)^2 - 4 tau(1-tau)|c|^2, m(tau) = tau beta + (1-tau) alpha, so
F(s,tau) = sqrt(4 tau(1-tau)|c|^2 - (s - m(tau))^2)\_+ / (2 pi tau(1-tau)):  each tau-slice is a semicircle law of radius
2|c| sqrt(tau(1-tau)) centred on the segment joining alpha (tau = 0) to beta (tau = 1), with mass |c|^2.  (This replaces the
sphere-projection formula of Q_quantum/LOG.md s.6.)

## 5. Proof of Theorem 2 (the strip inequality (\*) for every M, exact defect)

This re-derives Q-L10 of SHARED_LEMMAS completely, using Theorem 1 in place of the conjecture.

LEMMA 5 (strip Poisson kernel).  For 0 < X < 1 let K_X(u) = sin(pi X)/(2(cosh(pi u) - cos(pi X))).  Then K_X > 0,
K_X(u) <= C_X e^{-pi|u|}, for u != 0 one has K_X(u) = sum\_{n>=1} sin(n pi X) e^{-n pi |u|}, and for complex a with |Re a| < pi
        int_R e^{-au} K_X(u) du = sin(a(1 - X))/sin(a)        (= 1 - X at a = 0).
Proof.  Series: with q = e^{-pi|u|}, theta = pi X: sum_n q^n sin(n theta) = Im[q e^{i theta}/(1 - q e^{i theta})] = q sin(theta)/(1 - 2q cos(theta) + q^2)
= sin(theta)/(2cosh(pi u) - 2cos(theta)).  Transform: first a = i kappa, kappa real, kappa != 0.  Let f(u) = e^{-i kappa u}/(cosh(pi u) - cos(pi X))
and integrate over the boundary of the rectangle [-L, L] x [0, 2] (counterclockwise); the vertical sides vanish as L -> inf, and
f(u + 2i) = e^{2 kappa} f(u), so the contour integral is (1 - e^{2 kappa}) int_R f.  The poles inside are u = iX and u = i(2 - X)
(cosh(pi u) = cos(pi X)), simple, with residues e^{-i kappa u0}/(pi sinh(pi u0)) = e^{kappa X}/(i pi sin(pi X)) and
-e^{kappa(2-X)}/(i pi sin(pi X)).  Hence int_R f = 2(e^{kappa X} - e^{kappa(2-X)})/((1 - e^{2 kappa}) sin(pi X)) = 2 sinh(kappa(1-X))/(sinh(kappa) sin(pi X)),
i.e. int e^{-i kappa u} K_X(u) du = sinh(kappa(1-X))/sinh(kappa) = sin(a(1-X))/sin(a) at a = i kappa.  Both sides are analytic on
|Re a| < pi (left: exponential decay of K_X; right: sin has no zero there except the removable a = 0), so they agree there.   QED

LEMMA 6 (h_lam is the Poisson integral of its boundary data).  For z = X + iY with 0 < X < 1,
        h_lam(z) = int_R (w - lam)\_+ K_X(Y - w) dw,
and h_lam extends continuously to the closed strip with h_lam(iY) = (Y - lam)\_+ and h_lam(1 + iY) = 0.
Proof.  Let Phi(z) be the right side.  (1) Phi is harmonic: K_X(Y - w) = (1/2) Re cot(pi(z - iw)/2) is harmonic in z, and
differentiation under the integral is justified by K_X(u) <= C e^{-pi|u|} locally uniformly in X.  (2) h_lam is harmonic on the
open strip: e^{pi(Y - lam)} e^{-i pi X} = exp(-i pi z - pi lam) is analytic in z and its argument -pi X lies in (-pi, 0), so it never
meets the cut [1, inf) of Li2.  (3) For Y < lam: (w - lam)\_+ vanishes unless w > lam > Y, where by Lemma 5
K_X(Y - w) = sum_n sin(n pi X) e^{-n pi (w - Y)} (absolutely, uniformly for w >= lam); integrating termwise,
Phi(z) = sum_n sin(n pi X) e^{n pi (Y - lam)}/(n pi)^2 = -(1/pi^2) Im sum_n (e^{pi(Y-lam)} e^{-i pi X})^n/n^2 = h_lam(z).
(4) Two harmonic functions on the connected strip agreeing on the open set {Y < lam} agree everywhere.  (5) As X -> 0,
K_X(Y - .) is an approximate identity at Y (positive, mass 1 - X -> 1, uniformly small off any neighbourhood of Y, with
exponential tails dominating the linear growth of (w - lam)\_+), so Phi -> (Y - lam)\_+; as X -> 1, K_X <= sin(pi X) C e^{-pi|u|}
(cosh(pi u) - cos(pi X) >= max(1, e^{pi|u|}/2 - 1) for X >= 1/2), so Phi -> 0.                                                QED

For nu = x + iy in the closed strip let omega_nu be the measure K_x(y - w)dw (0 < x < 1), delta_y (x = 0), 0 (x = 1).  By Lemmas 5-6:
        h_lam(nu) = int (w - lam)\_+ omega_nu(dw),      int e^{aw} omega_nu(dw) = e^{ay} sin(a(1 - x))/sin(a)   (|Re a| < pi).      (5.1)

PROOF OF THEOREM 2.  Let nu_k = x_k + i y_k (k = 1..M) be the eigenvalues of X = B + ig; x_k in [0,1] because Re<v,Xv> = <v,Bv>.
Put rho = sum_k omega\_{nu_k} (a positive measure with density <= C e^{-pi|w|} plus atoms) and sigma = sum\_{mu in spec(PgP|ranP)} delta_mu.
Then the left side of Theorem 2 equals int (w - lam)\_+ d(rho - sigma)(w).
(a) Laplace transforms.  For real a with 0 < |a| < pi, by (5.1),
    rhohat(a) := int e^{aw} rho(dw) = sum_k e^{a y_k} sin(a(1 - x_k))/sin a = [Tr e^{ag + iaP} - Tr e^{ag - iaP}]/(2i sin a),
because e^{-ia(X - 1)} = e^{ag + iaP} has eigenvalues e^{a y_k} e^{ia(1 - x_k)} and e^{ia(X\* - 1)} = e^{ag - iaP} has eigenvalues
e^{a y_k} e^{-ia(1 - x_k)}.  Also sigmahat(a) = Tr_P e^{aPgP}.  Since the B-terms cancel,
    D(a, -ia) - D(a, ia) = Tr e^{ag + iaP} - Tr e^{ag - iaP} - (e^{ia} - e^{-ia}) Tr_P e^{aPgP} = 2i sin(a) [rhohat(a) - sigmahat(a)].
By Theorem 1 at t = -ia and t = ia:  D(a,-ia) - D(a,ia) = 2i a^2 int int e^{as} sin(a tau) F ds dtau.  Hence, with Lemma 5 (X = 1 - tau),
    rhohat(a) - sigmahat(a) = a^2 int int e^{as} (sin(a tau)/sin a) F ds dtau = a^2 int int F(s,tau) int e^{a(s - u)} K\_{1-tau}(u) du ds dtau
                            = a^2 int e^{aw} V(w) dw,        V(w) := int_0^1 int_R K\_{1-tau}(s - w) F(s,tau) ds dtau          (5.2)
(Tonelli; all integrands are >= 0 for real a).  V is finite, continuous and O(e^{-pi|w|}): int K\_{1-tau} = tau <= 1 and
sup_s F(s,tau) <= C/sqrt(tau(1-tau)) (Lemma 1), so V(w) = int_0^1 (K\_{1-tau} \* F(.,tau))(w) dtau with a dominated, continuous
integrand; F has compact support and K\_{1-tau}(u) <= C sin(pi tau) e^{-pi|u|} for |u| >= 1.
(b) Moments.  By (5.2), rhohat - sigmahat = O(a^2) as a -> 0 (both sides are analytic on |a| < pi), so rho and sigma have equal
mass and equal first moment.  Put W(w) := int (w - u)\_+ d(rho - sigma)(u).  W is continuous; for w below supp sigma,
W(w) = int\_{u<w} (w - u) drho(u) = O(e^{-pi|w|}); for w above it, by the moment identities W(w) = int\_{u>w} (u - w) drho(u) = O(e^{-pi w}).
W'' = rho - sigma as distributions, so (two integrations by parts, boundary terms vanish since the decay rate pi exceeds |a|)
int e^{aw} W(w) dw = a^{-2}(rhohat(a) - sigmahat(a)) = int e^{aw} V(w) dw  for real 0 < |a| < pi.  Both sides are analytic on
|Re a| < pi, hence agree on the imaginary axis: W and V are integrable continuous functions with the same Fourier transform, so W = V.
(c) Since (u - lam)\_+ = (lam - u)\_+ + (u - lam) and rho - sigma has zero mass and first moment,
    int (u - lam)\_+ d(rho - sigma)(u) = W(lam) = V(lam) = int int K\_{1-tau}(s - lam) F(s,tau) ds dtau >= 0.
(d) Equality.  K\_{1-tau} > 0 for 0 < tau < 1 and F >= 0 is continuous, so V(lam) = 0 forces F = 0 on R x (0,1); then D = 0 by
Theorem 1, so G(0,t) = ||BgP||\_F^2 (1 - e^{-t})/t = 0 (Remark 4.3), i.e. BgP = 0 = PgB, i.e. [B,g] = 0.  Conversely [B,g] = 0 gives
g = g_d, p = q, F = 0, V = 0.                                                                                                  QED

REMARK 5.1.  For all lam simultaneously the defect is the strip-balayage V of the positive measure nu_2 = F ds dtau onto the left
edge (this is the "conversely" of Q-L10: (\*) for (B,g) <=> V >= 0; Theorem 1 gives the stronger pointwise positivity of nu_2).

## 6. Numerical verification (NUMERICAL; scripts and logs in this folder)

All checks test the IDENTITY of Theorem 1 (positivity of F is manifest).  "Exact breakpoints" = real roots of the x-discriminant
along the integration path (q_core.breakpoints); tanh-sinh in mpmath between them.
 q01_formula_check.py   D(a,t)/a^2 vs int int e^{as - t tau} F, M = 2..5, 24 (a,t): rel. err 2e-7..9e-5 (= 2D quadrature error).
 q02_hp_checks.py (50 digits, log q02_hp_checks_dps50.log): tau-marginal = ||BgP||\_F^2 (the one direction not used in the proof)
   and Radon slices = U_xi at the Qf-X18 CM counterexample t03 (spec g = -2.95, 0.60, 77.36): <= 1.2e-49; Qf-X19 clustered point
   t59: <= 2e-50; spec g containing 150 (M = 3) or -300 (M = 4): <= 4.2e-49; M = 5 at scale 60 (spec -84..28): <= 1.1e-49;
   M = 4 r = 1: <= 1.6e-23; clustered M = 4 (three eigenvalues within 1.3e-3 of 40): Radon <= 1.8e-49, marginals 1.5e-9 with
   the float grid -> 1.5e-27 and 1.6e-22 with exact breakpoints (q08; the grid had missed a sub-grid window).
 q03_defect_check.py: end-to-end (\*) defect  Psi_lam - Tr[(P(g - lam)P)\_+]  vs  V(lam) = int int K\_{1-tau}(s - lam) F:
   t03 lam = 0.597: 0.13255808615430 vs 0.13255808615262; t03 lam = 68.405: 7.649727362386 vs 7.649727362385 (diff 5.5e-13);
   t59: diff 7e-16, 1e-15; r4_1: 2e-14; r4_2big (spec g contains -300): 1.4e-10, 2.7e-12; r5_2: 3e-14, 3.4e-10.
   CORRECTION (re-verification, Q_2bmv_check/REFEREE.md): q03 also logged two MISMATCHES that were omitted here before:
   r3_2big (spec g contains 150) at lam = 59.23852: 2.46e-3, and c4_2 (clustered at 40): 4.9e-8 and 1.4e-8.  Both are
   quadrature failures of q03 (fixed-order rules between branch points; F has complex singularities near the real s-axis):
   the re-verification's separate adaptive recomputation (rf_05\_\*.log) gives 7.1e-14 at r3_2big, lam = 59.23852, and
   2.4e-15, 2.8e-15 at c4_2.
 q04_stress_sweep.py (float, adaptive, grid breakpoints): random M = 3..6 at |g| up to 255 ('big', 'wide', 'cluster', 'twoscale'):
   marginal/Radon/Laplace deviations <= 6e-9 / 3e-10 / 4e-4 (Laplace = 2D Gauss quadrature).  The 'nearcomm' cases
   (off-diagonal block 1e-3, |g| ~ 150) FAIL in float only because the thin support strips of F fall between grid points;
   rechecked with exact breakpoints in q07/q08: M = 3, 4 (q07): <= 8.4e-34; M = 5 (q08): 8.8e-40 / 1.2e-34; M = 6: 1.9e-38 / 8.6e-35.
 q05_generalB.py, q06_generalB_hp.py, q08 (Theorem 3): spec B = (0, .37, 1), (-1, .2, .5, 2), (0, .6, .6, 1), (0, .3, .3, .31, 1):
   tau-marginals = sum ||Pi_k A Pi_l||^2/(b_l - b_k) to 30 digits, Radon slices crossing interior lines to 1e-29..1e-31
   (degenerate interior eigenvalue: 2.3e-12, quadrature-limited).

## 7. General Hermitian B (side result; contains Stahl's theorem) -- see s.8 for the closely related prior work of Heinavaara

THEOREM 3 [PROVED below].  Let A, B be Hermitian M x M matrices, B = sum\_{k=1}^n b_k Pi_k with b_1 < ... < b_n (n >= 2), m_k = rank Pi_k,
A_d = sum_k Pi_k A Pi_k, delta = min_k (b\_{k+1} - b_k).  For tau in G := (b_1, b_n) \ {b_2, ..., b\_{n-1}} and s real let x_i(s,tau) be
the roots of det(A - s - x(B - tau)) and F(s,tau) = (1/2pi) sum_i |Im x_i(s,tau)|; F := 0 for tau not in G.  Then F >= 0 is in L^1(R^2),
supported in K = [lmin(A), lmax(A)] x [b_1, b_n], and for all (a,t) in C^2
    D_B(a,t) := Tr e^{aA - tB} - sum_k e^{-t b_k} Tr\_{Pi_k} e^{a Pi_k A Pi_k}  =  a^2 int int e^{as - t tau} F(s,tau) ds dtau.
COROLLARY (Stahl's theorem, ex-BMV conjecture, with an explicit density).  For Hermitian A, B, t -> Tr e^{A - tB} is the Laplace
transform of the positive measure  sum_k Tr\_{Pi_k}(e^{Pi_k A Pi_k}) delta\_{b_k} + (int_R e^s F(s,tau) ds) dtau  on [b_1, b_n]  (a = 1).
Theorem 1 is the case n = 2 (the matrix P with b = (0,1)).  NUMERICAL: q05 (2D Laplace identity, 1e-7) and q06 (30-digit Radon
slices crossing interior lines, piecewise-constant tau-marginals sum\_{k<l, b_k<tau<b_l} ||Pi_k A Pi_l||\_F^2/(b_l - b_k)).

Proof.  Same five steps as for Theorem 1; only the changes are listed, each with its proof.
(1') Pencil bounds.  For tau in the gap (b_k, b\_{k+1}) put d\_- = tau - b_k, d\_+ = b\_{k+1} - tau.  All roots satisfy |x| <= ||A - s||/min(d\_-,d\_+)
  ((B - tau) has no eigenvalue in (-min, min)).  A non-real root has an eigenvector v (|v| = 1) with <v,(B - tau)v> = 0; with
  w_l = |Pi_l v|^2 and S := sum\_{b_l > tau} (b_l - tau) w_l = sum\_{b_l < tau} (tau - b_l) w_l one has S >= d\_+ W\_+, S >= d\_- W\_-
  (W\_+ + W\_- = 1), hence S >= d\_+ d\_-/(d\_+ + d\_-), and |(B - tau)v|^2 = sum_l (b_l - tau)^2 w_l >= (d\_+ + d\_-) S >= d\_+ d\_-.  So non-real
  roots obey |x| <= ||A - s||/sqrt(d\_+ d\_-), F <= (M/2pi)||A - s||/sqrt(d\_+ d\_-), and int over a gap of (d\_+ d\_-)^{-1/2} dtau = pi: F is in L^1.
  F = 0 for s outside (lmin, lmax) (Lemma 1(c) verbatim) and for tau outside [b_1, b_n] (B - tau definite: all roots real).
  q(x) = det(A_d - s - x(B - tau)) = prod_l det(Pi_l A Pi_l - s - x(b_l - tau)) has real roots; p and q have the same leading
  coefficient det(-(B - tau)) and the same root sum, since (B - tau)^{-1} = sum_l Pi_l/(b_l - tau) and Tr[Pi_l (A - A_d)] = 0.
(2') Radon data.  Lemma 3 holds verbatim with g, g_d, P replaced by A, A_d, B and D by D_B (spec(A_d - xi B) = union over l of
  spec(Pi_l A Pi_l) - xi b_l).
(3') Steps 0-1.  D_B(0,t) = Tr e^{-tB} - sum_l m_l e^{-t b_l} = 0 and dD_B/da(0,t) = Tr(A e^{-tB}) - sum_l e^{-t b_l} Tr(Pi_l A Pi_l) = 0
  (e^{-tB} = sum_l e^{-t b_l} Pi_l).  |D_B| <= 2M e^{H_K(Im zeta)} as in s.2 (the points (mu, b_l), mu in spec Pi_l A Pi_l, lie in K).  So
  T := the PWS distribution with T(e^{as - t tau}) = D_B(a,t)/a^2 exists, supp T in K, and its transform is bounded on R^2.
(4') Step 2 verbatim for phi supported in R x (b_k + delta', b\_{k+1} - delta'): T = F on R x G.
(5') Step 3 (all lines, interior ones included).  T - F is supported on the lines tau = b_l, so (Hormander Thm 2.3.5)
  T - F = sum\_{l,j<=N} gamma\_{l,j} (x) delta^{(j)}(tau - b_l), and for real kappa, omega
        That(kappa, omega) - Fhat(kappa, omega) = sum\_{l,j} gammahat\_{l,j}(kappa) (i omega)^j e^{-i omega b_l}.                    (7.1)
  Fix kappa != 0.  As omega -> +inf: Fhat(kappa, omega) -> 0 (Riemann-Lebesgue, F in L^1(R^2)), and That(kappa, omega) =
  -D_B(-i kappa, i omega)/kappa^2 -> 0 by LEMMA 8.  By LEMMA 9 every coefficient in (7.1) vanishes: gammahat\_{l,j}(kappa) = 0 for all
  kappa != 0, hence gamma\_{l,j} = 0.  So T = F, which is Theorem 3.                                                              QED

LEMMA 8 (first-order perturbation).  For real kappa and |omega| >= 8|kappa| ||A||/delta:
    | Tr e^{-i(omega B + kappa A)} - sum_k e^{-i omega b_k} Tr\_{Pi_k} e^{-i kappa Pi_k A Pi_k} |  <=  2M ||A||^2 kappa^2 / (delta |omega|).
Proof.  omega B + kappa A = omega H, H = B + eps A, eps = kappa/omega, |eps| ||A|| <= delta/8.  By Weyl's inequality and continuity in eps,
exactly m_k eigenvalues of H lie in I_k = [b_k - delta/4, b_k + delta/4].  Fix k, Q = 1 - Pi_k.  For lambda in I_k the compression
Q(H - lambda)Q on ran Q has all eigenvalues of modulus >= delta/2, so R(lambda) = (Q(H - lambda)Q|ranQ)^{-1} has norm <= 2/delta, and by the
Schur complement dim ker(H - lambda) = dim ker S(lambda), S(lambda) := (b_k - lambda) + eps Pi_k A Pi_k - eps^2 Pi_k A Q R(lambda) Q A Pi_k
on ran Pi_k (Hermitian).  dS/dlambda = -1 - eps^2 Pi_k A Q R(lambda)^2 Q A Pi_k <= -1, so the ordered eigenvalues sigma_j(lambda) of S(lambda)
satisfy sigma_j(lambda') <= sigma_j(lambda) - (lambda' - lambda) for lambda' > lambda; and by Weyl |sigma_j(lambda) - (b_k - lambda + eps mu\_{k,j})|
<= 2||A||^2 eps^2/delta (mu\_{k,j}: eigenvalues of Pi_k A Pi_k on ran Pi_k).  Since |eps mu| <= delta/8 and 2||A||^2 eps^2/delta <= delta/32,
sigma_j > 0 at b_k - delta/4 and < 0 at b_k + delta/4, so each sigma_j has exactly one zero lambda\_{k,j} in I_k, and
|lambda\_{k,j} - b_k - eps mu\_{k,j}| <= 2||A||^2 eps^2/delta.  Counting multiplicities (dim ker S(lambda) = #{j: sigma_j(lambda) = 0}),
the lambda\_{k,j} (j = 1..m_k) are the m_k eigenvalues of H in I_k.  Therefore Tr e^{-i omega H} = sum\_{k,j} e^{-i omega lambda\_{k,j}} and
|e^{-i omega lambda\_{k,j}} - e^{-i omega b_k - i kappa mu\_{k,j}}| <= |omega| 2||A||^2 eps^2/delta = 2||A||^2 kappa^2/(delta |omega|).          QED

LEMMA 9 (exponential polynomials).  If E(omega) = sum\_{l=1}^n P_l(omega) e^{-i omega b_l} with distinct real b_l and polynomials P_l, and
E(omega) -> 0 as omega -> +inf, then every P_l = 0.
Proof.  Otherwise let J = max deg P_l and a_l the omega^J-coefficients (not all 0).  Then f(omega) = sum_l a_l e^{-i omega b_l} =
omega^{-J} E(omega) + O(1/omega) -> 0, so (1/L) int_L^{2L} |f|^2 -> 0; but this mean equals sum_l |a_l|^2 + sum\_{l != l'} a_l conj(a_l')
(1/L) int_L^{2L} e^{-i omega (b_l - b_l')} d omega -> sum_l |a_l|^2 > 0.                                                         QED
(For projections, Lemmas 8-9 give a second proof of Step 3 of s.4.)

## 8. Relation to the literature, and what this does for the program

* Mechanism.  Inverting a trace-of-a-pencil function by the 2D Fourier transform and finding a density (1/2pi) sum Im(eigenvalues
  of an auxiliary pencil) is exactly the mechanism of O. Heinavaara, "Tracial joint spectral measures" (arXiv:2310.03227),
  Theorem 3.1, formula (7): for Hermitian A, B there is a positive measure mu\_{A,B} on R^2 with
  tr H(f)(xA + yB) = int f(ax + by) dmu\_{A,B}, H(f)(x) = int_0^1 ((1-t)/t) f(xt) dt, and Stahl's theorem is derived from it there.  So
  Theorem 3 / its corollary is NOT a new proof of BMV in substance; it is a variant (pinched, doubly integrated, affine chart instead
  of the dilation-averaged linear chart used there).  The plane-wave / Herglotz-Petrovsky-Leray densities of the Weyl calculus of two
  Hermitian matrices are classical (Bazer-Yen; Atiyah-Bott-Garding; B. Jefferies, arXiv:2108.09863).  Stahl: Acta Math. 211 (2013);
  Eremenko's exposition (2015).  Our proofs above are self-contained and were found independently of these papers; the priority
  check was done afterwards (2026-10-02).
* What appears to be specific to this program: the pinched, a^2-divided object nu_2 (2BMV, Q-C3) and its positivity (Theorem 1),
  and the deduction of the strip inequality (\*) with the exact defect formula (Theorem 2 = Q-L10 + Theorem 1).
* Consequences (not re-checked in this file): (\*) holds for every M and every projection B, so the items
  of SHARED_LEMMAS marked "PROVED modulo (\*)" -- Q-T1 (continuum quantum = classical) and Q-T2 (all-d asymptotic bound) -- become
  unconditional, and by STAR_CONTEXT ("27B for all d is EXACTLY equivalent to proving (\*) for every M", given CONE_d from QD2) the
  remaining input of the all-d 27B programme is supplied.
