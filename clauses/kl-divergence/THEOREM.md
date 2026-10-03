# The KL (statistical-strength) clause of OQP 27B: proved statements

Ansh Mishra, Aryan Senthilkumar -- 2026-10-02.  Folder `clauses/kl-divergence/`.

Main results.
* **Theorem 1.** For every d >= 4 the DKZ (CGLMP-optimal) measurements do **not** maximise the van Dam-Gruenwald-Gill
  statistical strength on the maximally entangled state Phi_d. This holds for all three versions (uniform,
  uncorrelated and correlated setting distributions). An explicit orthonormal-basis strategy beats DKZ_d by at least
  0.00154 bits, and by at least 0.0191 bits when 4 | d.
* **Corollary 2.** 0.0687273 <= sup_d S(DKZ_d) <= 0.0687803 bits. The upper bound holds for every d.
* **Theorem 3.** For d = 3, DKZ_3 is a strict local maximiser of all three strengths among all PVM strategies on Phi_3,
  modulo the gauge group. The KL-optimal dual of DKZ_3 is the exact CGLMP ("Gill") form, and
  S(DKZ_3) = 0.05778302549332865 bits in closed form.
  Global optimality at d = 3 remains OPEN (numerically true).

Natural logarithms are used in the proofs and bits in the tables.

---------------------------------------------------------------------------------------------------------------------

## 0. Setting

Scenario (2,2,d): settings x, y in {0,1}, outcomes a, b in Z_d. A behaviour q = (q_xy) consists of probability laws
q_xy = q(.,.|x,y) on Z_d x Z_d.
* Deterministic strategies: lambda = (a_0, a_1, b_0, b_1) in Z_d^4, with
  delta_lambda(a,b|x,y) = [a = a_x][b = b_y].
* Local polytope: L_d = conv{delta_lambda}.

**Strength** [van Dam-Gruenwald-Gill, IEEE TIT 51 (2005) 2812].
* For a setting distribution sigma on {0,1}^2:
  U_q(sigma) = inf\_{p in L_d} sum_xy sigma_xy D(q_xy || p_xy).
* S^UNI(q) = U_q(1/4).
* S^UC(q) = sup over product sigma = sigma_A (x) sigma_B.
* S^COR(q) = sup over all sigma.
* So S^UNI <= S^UC <= S^COR.

**Strategies on Phi_d** = d^(-1/2) sum_k |kk>. PVMs {A^x_a}, {B^y_b} on C^d give q(a,b|x,y) = Tr((A^x_a)^T B^y_b)/d.
* An orthonormal-basis (rank-one) strategy is a unitary A_x, B_y whose column a or b is the basis vector of outcome a or b.
* Its correlation is q(a,b|x,y) = |(A_x^+ Phihat conj(B_y))\_ab|^2, where Phihat = 1/sqrt(d).

**DKZ_d** (CGLMP-optimal, unique up to equivalence by ledger A2):
* |a>\_x = d^(-1/2) sum_k w^(k(a+alpha_x)) |k> and |b>\_y = d^(-1/2) sum_k w^(-k(b+beta_y)) |k>.
* w = e^(2 pi i/d), alpha = (1/2, 0), beta = (1/4, -1/4).

**Lemma 0 (closed form).** For DKZ_d on Phi_d, q(a,b|x,y) = Q^d_xy(b-a)/d, where
* Q^d_xy(m) = 1/(2 d^2 sin^2(pi (m - delta_xy)/d)),
* delta_00 = 1/4, delta_01 = 3/4, delta_10 = -1/4, delta_11 = 1/4.

*Proof.*
1. The amplitude is <a_x|<b_y|Phi_d> = d^(-3/2) sum_k w^(k s), with s = b - a - delta_xy and delta_xy = alpha_x - beta_y.
2. |sum\_{k<d} e^(2 pi i k s/d)|^2 = sin^2(pi s)/sin^2(pi s/d).
3. sin^2(pi s) = sin^2(pi delta_xy) = 1/2. QED

---------------------------------------------------------------------------------------------------------------------

## 1. General lemmas

**Lemma D (test factors).** Let sigma be a setting distribution. Let r >= 0 be a function of the cells (a,b|x,y), with
r > 0 on supp q, and with sum_xy sigma_xy r(a_x, b_y|x,y) <= 1 for every deterministic lambda. Then
U_q(sigma) >= sum_xy sigma_xy sum_ab q log r.

*Proof.* Let p be in L_d.
1. sum sigma q log(q/p) = sum sigma q log r - sum sigma q log(r p/q).
2. By concavity of log (Jensen, weights sigma q summing to 1 over supp q),
   sum sigma q log(r p/q) <= log sum\_{supp q} sigma r p.
3. sum_xy sigma_xy sum_ab r p <= 1 for every p in L_d. It holds on every delta_lambda by hypothesis, and it is linear in p.
4. So the log term in step 2 is <= 0, hence sum sigma q log(q/p) >= sum sigma q log r. Take the infimum over p. QED

**Lemma S (uniform settings).** Let G be a group of local relabellings: setting permutations of each party, plus outcome
permutations that may depend on the setting. Suppose G fixes q and acts transitively on the four setting pairs. Then
S^UNI(q) = S^UC(q) = S^COR(q).

*Proof.*
1. A relabelling g maps L_d onto L_d. Writing D(q_xy || (g p)\_xy) = D(q\_{g(xy)} || p\_{g(xy)}) gives U_q(g.sigma) = U_q(sigma).
2. sigma -> U_q(sigma) is concave, being an infimum of linear functions.
3. Hence U_q(avg_g g.sigma) >= U_q(sigma).
4. By transitivity, avg_g g.sigma is uniform. QED

**Lemma G (symmetries of DKZ_d).** Define
* G1: q'(a,b|x,y) = q(-a, -b + c_y | 1-x, y), with c = (0,1);
* G2: q'(a,b|x,y) = q(-a + c'\_x, -b | x, 1-y), with c' = (-1,0).

Both fix the DKZ_d correlation, and they act transitively on the setting pairs. Hence, by Lemma S,
**S^UNI(DKZ_d) = S^UC(DKZ_d) = S^COR(DKZ_d)**.

*Proof.* Q^d_xy is even about delta_xy and d-periodic.
1. Under G1, b - a -> -(b-a) + c_y.
2. One checks delta\_{1-x,y} - c_y = -delta_xy (mod d) in all four cases.
3. For G2, c'\_x + delta\_{x,1-y} = -delta_xy (mod d) in all four cases. QED

**Lemma SI (shift reduction).** Suppose q is invariant under (a,b) -> (a+s, b+s) for all x, y simultaneously. Set
Q_xy(m) = sum_a q(a, a+m|x,y). Then
* U_q(1/4) = inf_mu (1/4) sum_xy D(Q_xy || P^mu_xy),
* where mu ranges over the laws of (alpha, b0, b1) in Z_d^3, and
* P^mu_00 = law(b0), P^mu_01 = law(b1), P^mu_10 = law(b0 - alpha), P^mu_11 = law(b1 - alpha).

*Proof.*
1. Averaging a local p over the shifts gives a local p-bar. By convexity of D in its second argument and invariance of q,
   the objective does not increase.
2. The shift average of delta_lambda is (1/d)[b - a = b_y - a_x]. It depends only on
   (a_1-a_0, b_0-a_0, b_1-a_0) =: (alpha, b0, b1).
3. For shift-invariant q and p, D(q_xy||p_xy) = D(Q_xy||P_xy). QED

**Lemma W (DKZ_d is a wrapped universal correlation).** Let f(t) = 1/(2 pi^2 t^2) and Q^inf_xy(m) = f(m - delta_xy) on Z.
Each Q^inf_xy is a probability law, since sum_n (n + 1/4)^(-2) = 2 pi^2.
* (i) Q^d_xy(m) = sum\_{n in Z} Q^inf_xy(m + n d). That is, Q^d_xy is the image of Q^inf_xy under Z -> Z_d.
* (ii) Let mu be any probability law on Z^3, and define P^mu_xy on Z as in Lemma SI. Then for every d >= 2,
  S^UNI(DKZ_d) <= T(mu) := (1/4) sum_xy D(Q^inf_xy || P^mu_xy).
* (iii) S^UNI(DKZ_d) <= S^UNI(DKZ\_{kd}) for every k >= 1.

*Proof.*
1. (i) Use the partial-fraction identity sum_n (z+n)^(-2) = pi^2/sin^2(pi z) with z = (m - delta)/d.
2. (ii) Reduce mu mod d. This gives a law on Z_d^3, i.e. a shift-invariant local model, whose link laws are the images
   of P^mu_xy.
3. By Lemma SI and (i), S^UNI(DKZ_d) <= (1/4) sum D(wrap Q^inf || wrap P^mu).
4. By the log-sum inequality, applied on each residue class, this is <= T(mu).
5. (iii) Repeat steps 2-4 with Z\_{kd} -> Z_d in place of Z -> Z_d. By (i), Q^{kd} wraps onto Q^d. QED

**Lemma E (embedding).** Let q in the (2,2,d) scenario be supported on O_A x O_B for every setting pair, where O_A and
O_B are nonempty outcome subsets. Then each strength of q in L(2,2,d) equals its strength in the smaller scenario with
outcome sets O_A and O_B.

*Proof.* Fix sigma. Let U_big and U_small be the infima of sum sigma D(q||p) over L_d and over the small local
polytope L_small.
* *U_big <= U_small.* L_small is contained in L_d: a small-scenario local model is a big-scenario local model that never
  outputs outcomes outside O_A, O_B.
* *U_small <= U_big.* Coarse-grain any p in L_d by mapping every outcome outside O_A (resp. O_B) to a fixed element of
  O_A (resp. O_B). The image Pi p lies in L_small, and Pi p >= p pointwise on O_A x O_B. Since q vanishes elsewhere,
  D(q_xy || Pi p_xy) <= D(q_xy || p_xy).
* Hence U_big = U_small for every sigma, and so all three strengths agree. QED

(This is the one-block case of Lemma F below.)

**Lemma CG (coarse-graining).** Let q' be obtained from q by local outcome post-processing, i.e. maps pi^A_x, pi^B_y on
outcomes. Then S^X(q') <= S^X(q) for X = UNI, UC, COR.

Every d-outcome PVM on C^d is a coarse-graining of an orthonormal basis. Hence the maximal strength over all PVM
strategies on Phi_d equals the maximum over orthonormal-basis strategies.

*Proof.*
1. Post-processing maps L_d into L_d, and D(Pi q || Pi p) <= D(q || p) by data processing.
2. Therefore U\_{q'}(sigma) <= U_q(sigma).
3. For the second claim, split each rank-r_a projector into r_a rank-one projectors. Since sum r_a = d this gives a
   basis, and each refined label is mapped back to its original outcome. QED

---------------------------------------------------------------------------------------------------------------------

## 2. Theorem 1: the KL clause fails for every d >= 4

**Construction (block strategy B_d).** Write d = 4k + rho with k >= 1 and rho in {0,1,2,3}.

Split the computational basis of C^d, and the outcome set, into consecutive groups of sizes 4, ..., 4 (k groups) and rho.
* **CHSH bases (real).** Let basis(theta) = [[cos(theta/2), -sin(theta/2)], [sin(theta/2), cos(theta/2)]], with column
  index = outcome.
  * Alice uses theta = 0 for x = 0 and theta = pi/2 for x = 1.
  * Bob uses theta = pi/4 for y = 0 and theta = -pi/4 for y = 1.
  * On Phi_2 this gives c(a,b|x,y) = (1 + (-1)^(a+b+xy)/sqrt2)/4.
* **4-blocks.** On each 4-block C^2 (x) C^2, use A_x (x) A_x and B_y (x) B_y, with outcome (a1,a2) -> 2 a1 + a2 inside
  the block. This is "CC4" = CHSH (x) CHSH with shared settings.
* **Remainder block.** It is
  * rho = 1: the single basis vector, the same outcome for all four measurements ("T1");
  * rho = 2: the CHSH bases ("C2");
  * rho = 3: the DKZ_3 bases ("K3").

All four measurements of B_d are orthonormal bases of C^d, i.e. rank-one PVMs with all d outcomes used.

**Lemma B (direct sums).** If every PVM is block diagonal for C^d = (+)\_j H_j (coordinate blocks of sizes m_j, disjoint
outcome sets O_j), then the correlation on Phi_d is q = sum_j (m_j/d) q_j. Here q_j is the block strategy's correlation
on Phi\_{m_j}, supported on O_j x O_j.

*Proof.*
1. Transposition preserves coordinate blocks.
2. Tr((A^x_a)^T B^y_b) = 0 when a and b belong to different blocks.
3. Inside block j the trace equals m_j q_j(a,b|x,y). QED

**Lemma F (flagged mixtures).** Let q = sum_j lambda_j q_j with q_j supported on O_j x O_j (O_j disjoint, lambda_j >= 0,
sum lambda_j = 1). Let sigma be a setting distribution. For each j let r_j > 0 be a test factor on O_j satisfying
* (F1) sum_xy sigma_xy r_j(a_x, b_y|x,y) <= 1 for all (a_0,a_1,b_0,b_1) in O_j^4, and
* (F2) for all j, k: sigma_00 R_j^00 + sigma_11 R_k^11 <= 1 and sigma_01 R_j^01 + sigma_10 R_k^10 <= 1,
  where R_j^xy = max\_{a,b in O_j} r_j(a,b|xy).

Then U_q(sigma) >= sum_j lambda_j sum_xy sigma_xy sum_ab q_j log r_j.

*Proof.* Let r = r_j on O_j x O_j cells and 0 elsewhere. Take a deterministic lambda and let J_x, K_y be the blocks of
a_x and b_y. Only the pairs E = {(x,y) : J_x = K_y} contribute.
1. If all pairs in E lie in one block j: extend lambda inside O_j by choosing arbitrary values for the outcomes outside
   block j. Since r >= 0, the contribution is at most the value of the extended block-j strategy, which is <= 1 by (F1).
2. If E meets two blocks j != k: an edge (x,y) in j and an edge (x',y') in k force x' != x and y' != y. So E is a
   "diagonal" pair {(0,0),(1,1)} or {(0,1),(1,0)}, and its contribution is <= 1 by (F2).
3. So r is feasible, and Lemma D applies. QED

**Lemma C (block certificates; exact).** `blocks_testfactors.json` contains exact rational test factors for T1, C2, K3
and CC4. Each satisfies (F1) for uniform sigma, checked by exhaustive exact enumeration of all m^4 strategies; the maxima
are 1, 1 - 1e-9, 1 - 1e-9 and 1 - 1e-9. All entries are <= 1.24801, so (F2) holds for every pair.

Interval arithmetic gives the certified values (bits):

| block | m | L = (1/4) sum q log r >= |
|---|---|---|
| T1 | 1 | 0 |
| C2 | 2 | 0.046273845411 |
| K3 | 3 | 0.057783024051 |
| CC4 | 4 | 0.087900462237 |

**Lemma Z (explicit Z-model; exact).** `zmodel_cert_A10.json` defines a probability law mu\* on Z^3.
* **Window.** alpha has rational weights on |alpha| <= 10, and b0 ~ K0(.|alpha), b1 ~ K1(.|alpha) are rational laws on
  [-14, 14].
* **Tail.** For |alpha| > 10, alpha has weight t/(alpha^2 - 1/4), with t = 0.1224482084... rational. Given such alpha,
  b0 is in {0, alpha} and b1 is in {1, alpha}, each with probability 1/2.
* **Total mass.** It is exactly 1, by telescoping: sum\_{alpha > A} 1/(alpha^2 - 1/4) = 1/(A + 1/2).

Then T(mu\*) <= 0.068780260568 bits.

*Proof.*
1. The link laws P_xy(m) are exact rationals for |m| <= 24, computed from the window plus the tail.
2. For |m| > 24 only the tail contributes: P_xy(m) = t/(2(m'^2 - 1/4)) with m' in {m, -m, 1-m}.
3. The sum over |m| <= 3000 is evaluated in 40-digit interval arithmetic.
4. For |m| > 3000 we have P >= Q termwise. Indeed (|m|+1)^2 <= t pi^2 (|m| - 3/4)^2 for all |m| >= 19, because t pi^2 > 1.2085.
5. So every remaining term Q log(Q/P) <= 0. QED

**Theorem 1.** For every d >= 4 and X in {UNI, UC, COR}:

> S^X(DKZ_d) <= 0.0687802606 bits < 0.0703203697 bits <= S^UNI(B_d) <= S^X(B_d).

For 4 | d the lower bound improves to 0.0879004622 bits.

*Proof.*
1. **DKZ side.** By Lemma G, S^X(DKZ_d) = S^UNI(DKZ_d). By Lemmas W and Z, this is <= T(mu\*) <= 0.0687802606 bits,
   for every d >= 2.
2. **Competitor side.** By Lemma B, q\_{B_d} = sum_j (4/d) q_CC4 (k copies) + (rho/d) q_rho, a flagged mixture.
3. By Lemmas F and C with uniform sigma, S^UNI(B_d) >= C(d) := (4k L_CC4 + rho L_rho)/d.
4. Since L_rho < L_CC4, C(4k + rho) = L_CC4 - rho(L_CC4 - L_rho)/(4k + rho) is nondecreasing in k.
5. Hence C(d) >= min{C(4), C(5), C(6), C(7)} = C(5) = (4/5) L_CC4 >= 0.0703203697 bits.
   * C(4) >= 0.0879005, C(6) >= 0.0740249 and C(7) >= 0.0749930.
6. S^X >= S^UNI for every q. QED

Remarks.
1. The competitor is a rank-one orthonormal-basis strategy. Allowing POVMs, other states or non-rank-one PVMs only
   enlarges the competitor class, so the failure persists under every reading of the clause on Phi_d.
2. The result also holds on Phi_D with d | D: compare DKZ (x) 1 with B_d (x) 1 (inert ancilla, same correlations).
3. The flagged-mixture bound is exact. The flagged local model gives the matching upper bound, and the full d^4-strategy
   solver reproduces C(d) for d = 4..7 (`competitor_check.py`).

**Corollary 2.** 0.068727358 <= sup_d S^UNI(DKZ_d) <= 0.068780261 bits. Numerically, S(DKZ_d) increases to about
0.068753 bits, with S_inf - S_d about 0.10/d^2.

*Proof.*
1. The upper bound is Lemmas W and Z.
2. For the lower bound, `dkz_lower.py` gives an exact rational shift-invariant test factor for d = 64, with feasibility
   max_a [max_b(r00(b) + r10(b-a)) + max_b(r01(b) + r11(b-a))] <= 4 checked in exact arithmetic. Lemmas D and SI give
   S(DKZ_64) >= 0.068727358 bits.
3. Lemma W(iii) extends this to every multiple of 64. QED

---------------------------------------------------------------------------------------------------------------------

## 3. Theorem 3: d = 3, strict local optimality of DKZ_3

**CGLMP levels.** Define g'\_00 = g'\_11 = (a - b) mod 3, g'\_10 = (b - a) mod 3 and g'\_01 = (b - a - 1) mod 3.

**Proposition K3 (exact KKT data of DKZ_3).**
* (i) **CGLMP bound.** For every deterministic lambda, sum_xy g'\_xy(a_x, b_y) is congruent to 2 mod 3 and is >= 2.
  * Equality holds for exactly 30 strategies J.
  * On L_3 this is CGLMP_3 in Pi-form: sum_xy E_p[g'\_xy] >= 2, equivalently I_3 <= 2.
  * F = conv{delta_lambda : lambda in J} spans an affine space of dimension 23. Its direction space is
    V = {u : sum_ab u_xy = 0, no-signalling, sum_xy sum_ab g'\_xy u = 0}, with dim V = 23. So F is a facet and
    aff F = p + V for every p in F.
* (ii) **Level law.** DKZ_3: q0(a,b|x,y) = Q\_{g'}/3 with Q = (2(2+sqrt3)/9, 2(2-sqrt3)/9, 1/9) on every link.
* (iii) **Test factor.** Let beta = [(16 + 24 sqrt3) - sqrt(3280 - 960 sqrt3)]/54 = 0.3213778867..., the root in
  (0, 2/3) of 27 b^2 - (16 + 24 sqrt3) b + 16 sqrt3 - 12 = 0.
  * Set r_k = 1 + beta(1/2 - k), i.e. r = (1.16068894, 0.83931106, 0.51793317), and r\* = r\_{g'}.
  * Then sum_k Q_k/r_k = 1 and sum_k k Q_k/r_k = 1/2.
  * r\* is feasible: sum_xy r\*(lambda)/4 = 1 + beta(1/2 - sum g'/4) <= 1.
* (iv) **Local model.** p\* := q0/r\* is the shift-invariant behaviour whose link laws have levels
  P\* = (Q_k/r_k) = (0.714528, 0.070944, 0.214528). It equals the mixture of all 30 strategies of J with weights:
  * W_A/12 on the 12 strategies with a single link at level 2;
  * W_B/12 on the 12 strategies with two adjacent links at level 1;
  * W_C/6 on the 6 strategies with two opposite links at level 1;
  * where W_A = 4 P\*\_2 and W_B = W_C = P\*\_1, all > 0.

  Hence p\* lies in the relative interior of F.
* (v) **Value.** S^UNI(DKZ_3) = S^UC = S^COR = sum_k Q_k log r_k = 0.05778302549332865 bits.

  The AGG "Gill-form" dual ansatz is therefore \*exact\* at d = 3.

*Proof.*
1. (i) Sum the four definitions: sum g' = -1 (mod 3) identically. The count of 30 and the affine dimension 23 are exact
   enumerations (`d3_cert.py` E2, E7).
2. (ii) Lemma 0 with d = 3.
3. (iii) Clear denominators in sum_k Q_k (1/2 - k)/r_k = 0. The two identities follow from this equation and from
   sum Q_k = 1. They are checked symbolically in `d3_sympy_check.py`.
4. (iv) A mixture of shifts and patterns has link-level law (1 - (W_B + W_C)/2 - W_A/4, (W_B + W_C)/2, W_A/4).
   * Here each link lies in 2 adjacent pairs and 1 opposite pair.
   * Shift-invariant behaviours are determined by their link laws.
5. (v) Lemma D with r\* gives >=. The local p\* gives <=, since D(q0||p\*) = sum sigma q0 log r\*. Lemma G covers the other
   two strengths. QED

**Theorem 3.** Let S = U(3)^4 be the orthonormal-basis strategies (A_0, A_1, B_0, B_1) on Phi_3. Let the gauge group
Gamma = T^12 x U(3) act by per-vector phases and by (A_x, B_y) -> (W A_x, conj(W) B_y). Gamma leaves q invariant.

There is an open neighbourhood N of DKZ_3 in S such that for every s in N and X in {UNI, UC, COR}:

> S^X(q_s) <= S^X(DKZ_3) = 0.0577830254933 bits, with equality only if s is in Gamma . DKZ_3.

The same holds in the space of all 3-outcome PVM strategies on Phi_3, since ranks are locally constant (Lemma CG for
context).

*Proof.*

*Chart and slice.*
* Chart: A_x(z) = exp(i sum_j z\_{Ax,j} h_j) A_x^DKZ and B_y(z) = exp(i sum_j z\_{By,j} h_j) B_y^DKZ, with z in R^36 and
  h_1..h_9 the Hermitian basis in `d3_cert.py`.
* The gauge tangent space is spanned by |u_a><u_a| in each basis and by (h, h, -conj h, -conj h). It has exact rank 20.
* The coordinate slice I (16 coordinates, listed in `d3_cert.log`) is transversal: exact rank 36 over Q(sqrt3).
* Gamma . point(Sigma) therefore contains a neighbourhood of DKZ_3, where Sigma is a small disc in span(e_I). This uses the
  submersion / slice argument: (g, s) -> g . point(s) has surjective differential at (1, 0).

*Upper-bound functions.*
1. For z near 0 put p(z) = p\* + u1(z) + u2(z), with u1, u2 in V.
2. By K3(i)(iv), p(z) lies in F, a subset of L_3, for small z.
3. By weak minimax, S^COR(q(z)) <= max_xy phi_xy(z), where phi_xy(z) := D(q_xy(z) || p_xy(z)).
4. phi_xy is real-analytic near 0 and phi_xy(0) = sum_k Q_k log r_k = S0 for every link.

*First order (exact).* Let Pi_k(z) be the total probability of level k over the four links.
1. **Criticality.** d_i Pi_k(0) = 0 for k = 0, 1, 2 and all 36 directions. This is an exact identity in Q(sqrt3)
   (`d3_cert.py` E4), independently re-derived with sympy (`d3_sympy_check.py`).
2. **Link sums.** For u in V, sum\_{xy cells} r\* u = -beta LS_xy(u), where LS_xy(u) := sum\_{xy cells} g' u.
3. **Psi.** It is an exact right inverse of LS from V onto the sum-zero vectors of R^4, built from facet strategies.
   Let pi^k_xy = d_v Pi_k^{xy}.
4. **Choice of u1.** u1(v) = kappa_1 Psi(pi^1) + kappa_2 Psi(pi^2) + (V_0 part), where kappa_k = -(l_k - l_0)/beta,
   l_k = log r_k, and V_0 = {u in V : LS = 0}.
5. Then sum\_{xy cells} r\* u1 = sum_k l_k pi^k_xy, for every link.
6. Hence the first-order term of every phi_xy vanishes:
   d_v phi_xy = sum\_{xy cells} d_v q log r\* - sum\_{xy cells} r\* u1 = 0.

*Second order.*
1. With u2 = 0, phi_xy has Hessian H_xy(v,v) = sum\_{xy} d_v^2 q log r\* + sum\_{xy} (d_v q - r\* u1(v))^2/q0.
2. **Equalisation.** Choose u2(z) = Psi((z^T (Hbar - H_xy) z/(2 beta))\_xy), where Hbar = (1/4) sum_xy H_xy. Then every
   phi_xy(z) = S0 + z^T Hbar z/2 + O(|z|^3).
3. **Certified bound.** `d3_cert.py` computes Hbar on the slice from exact derivatives and interval logarithms. An interval
   Cholesky of -Hbar - I/200 succeeds, so Hbar <= -(1/200) I on span(e_I). The float spectrum is [-0.390, -0.00973].
4. Therefore max_xy phi_xy(z) < S0 for 0 < |z| small in the slice. Gauge invariance of q then gives the claim on N.

The second-order equalisation is genuinely needed: the individual H_xy are not negative definite (`d3_check.py`). QED

**Independent checks.**
* `d3_check.py`: finite-difference Hessians of the four actual link functions; their average equals Hbar to 2.8e-6.
  The full KL solver decreases along 60 random slice points.
* `d3_sympy_check.py`: exact sympy re-check of (ii), of the criticality identities and of (iii).

---------------------------------------------------------------------------------------------------------------------

## 4. What is not proved

* **Global optimality of DKZ_3** on Phi_3 (C3, d = 3): OPEN, but numerically true. 300 unbiased starts
  (`d3_global.py`; random Bell functional entry, then KL ascent) find exactly three local maxima of S^UNI and none above
  DKZ_3, for S^UNI or S^COR:
  * 0.0308492 bits = (2/3) S(CHSH), the 2+1 block;
  * 0.0481313 bits;
  * 0.0577830 bits = DKZ_3.
* **d = 2:** not treated.
* The exact value of sup_d S(DKZ_d) is not determined; it lies in [0.0687273, 0.0687803] bits.
