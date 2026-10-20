# The noise clause on direct sums: DKZ blocks, classical blocks and exact thresholds

Ansh Mishra, Aryan Senthilkumar. 2026-10-20. Folder `clauses/noise-direct-sums/`.

**Status:**
- Proved, computer-assisted. The computer parts are Theorem M (inherited) and Theorem PHI.
- Independently re-checked; see [`INDEPENDENT_VERIFICATION.md`](INDEPENDENT_VERIFICATION.md).
- Not reviewed by outside experts.

**What this does not settle.** The noise clause 27B(ii) for general strategies at d >= 5 (C2 in
[`../LEDGER.md`](../LEDGER.md)) remains OPEN. This folder proves it for the whole family of direct sums described
below, and for explicit neighbourhoods of them.

Notation as in [`../noise-dkz-threshold/THEOREM.md`](../noise-dkz-threshold/THEOREM.md):
- P(a,b|x,y) = (1/d)|<a_x|b_y>|^2 is the behaviour of a strategy on Phi_d (b_y the steered Bob vectors);
- P_v = vP + (1 - v)u, with u the uniform behaviour;
- v_c is the largest v with P_v local;
- kappa_n = I_ME(n)/2 and v*(d) = 1/kappa_d;
- G_n is the DKZ link law, and Q_n = G_n/kappa_n + (1 - 1/kappa_n)u_n;
- CLAIM(phi) means phi is the common one-dimensional marginal of a law on the compositions of n - 1 into four parts.
  Theorem M is CLAIM(Q_n).

## 1. Results

**Lemma K.** kappa_n is strictly increasing in n >= 2, and kappa_n < kappa_oo := lim kappa_n = 16G/pi^2 = 1.4849075
(G is Catalan's constant).

**Theorem PHI.** For every n >= 2, phi_inf(n) := [G_n - (kappa_n - 1) delta_0]/(2 - kappa_n) satisfies
CLAIM(phi_inf(n)) with nonnegative weights. The proof is in [`PROOF_PHI.md`](PROOF_PHI.md): interval verification for
4 <= n <= 50000, and a written argument with two n-independent interval checks for n >= 50001.

**Theorem DS_r (direct sums of DKZ blocks).** For r >= 2 and d_1, ..., d_r >= 2, with d = sum d_i,

    v_c(DKZ_{d_1} (+) ... (+) DKZ_{d_r}) = d / sum_i d_i kappa_{d_i}  >  v*(d).

**Theorem LB (DKZ blocks plus a classical block).**
- Setting: S = DKZ_{k_1} (+) ... (+) DKZ_{k_r} (+) C, with r >= 1, k_i >= 2, and C a classical block of dimension
  m >= 1. "Classical" means Alice uses one basis for both settings on C, and so does Bob.
  - On C x C the behaviour is J(a,b)/d with J doubly stochastic and setting-independent.
  - m one-dimensional blocks are the case J = I.
- Notation: K = sum k_i, d = K + m, kappa_i = kappa_{k_i}, Sig = sum k_i kappa_i, kbar = Sig/K. For a nonempty set U of
  DKZ blocks, define K_U, Sig_U and kbar_U in the same way, and put
      v0(U) := (2d - K_U)/(d kbar_U + d - K_U),   v0 := v0(all) = (K + 2m)/(d kbar + m).
- (i) v_c(S) <= v0(U) for every nonempty U.
- (ii) If max_{i,j} |kappa_i - kappa_j| <= (Sig - K)/(K + 2m), then v_c(S) = v0. This covers every case with
  m <= 2.4K, a single DKZ block, and equal blocks.
- (iii) In all cases v_c(S) > v*(d). So C2 holds on the whole family, in every dimension.

**Remark LB+ (any weakly nonlocal extra block).** Let the extra block be ANY strategy T on m dimensions instead of C.
- v_c(S) <= v0 still holds.
- If the condition of (ii) holds (or, more generally, the Hall condition of LB-exact) and
  v_c(T) >= v_T := v0/(v0 + (1 - v0) m/d), then v_c(S) = v0 > v*(d).
- v_T is about 0.87-0.91 in the cases tested, and the condition is sharp in LP tests.

**Remark LB-exact.** For a classical block, or any T as in LB+, v_c(S) = v0 holds if and only if v0 <= v0(U) for every
nonempty U.

**Theorem LB\* (the exact law for the whole family).** For S = DKZ_{k_1} (+) ... (+) DKZ_{k_r} (+) C, with C classical
of dimension m >= 0:

    v_c(S) = min over nonempty U of v0(U).

**Lemma TH.** Every minimiser U* is of the form {i : k_i >= tau}. So v_c(S) is the minimum of at most r explicit
values.

Notes on LB*:
- An exhaustive scan finds the full set U = all binding for every composition with d <= 41. The first exception is
  d = 42, blocks (4,2) + L_36.
- Example of a proper minimiser: (3,2) + L_50 has v_c = v0({3}) = 0.81676 < v0 = 0.81702.

**Lemma U and Corollary P (neighbourhoods).**
- Lemma U: a behaviour Z with uniform marginals is local if, for every y and b,
  min_{a0} Z(a0,b|0,y) + min_{a1} Z(a1,b|1,y) >= 1/d^2.
- Corollary P: if v_c(S) > v*, every strategy S' with
  max|P(S') - P(S)| <= (v_c(S) - v*)/(2 d^2 v* v_c(S)) has v_c(S') >= v*.
- With the theorems above, every direct sum in this folder has an explicit neighbourhood on which C2 holds.

## 2. Proofs

### Lemma K
- I_ME(d) = (4/(d(d-1))) sum_{m=1}^{d-1} m csc(pi m/(2d)) = 4 E_{nu_d}[phi]. Here nu_d is uniform on
  {1/d, ..., (d-1)/d}, phi(x) = x/sin(pi x/2) = (2/pi) psi(pi x/2) and psi(y) = y/sin y.
- psi is strictly convex on (0, pi/2]:
  - psi'' = csc y [y(cot^2 y + csc^2 y) - 2 cot y] has the sign of g(y) = y(1 + cos^2 y) - sin 2y;
  - g(0) = 0 and g'(y) = sin y (3 sin y - 2y cos y) > 0, because tan y > 2y/3.
- nu_{d+1} is a mean-preserving spread of nu_d. The kernel sends k/d to k/(d+1) with probability 1 - k/d and to
  (k+1)/(d+1) with probability k/d. It is a martingale (mean k/d), and its image is uniform on {j/(d+1)}: each j gets
  (1/(d-1))(1 - 1/d) = 1/d.
- Strict Jensen gives I_ME(d+1) > I_ME(d).
- The Riemann sums 4 E_{nu_d}[phi] tend to 4 int_0^1 phi = (16/pi^2) int_0^{pi/2} y/sin y dy = 32G/pi^2, so
  kappa_oo = 16G/pi^2. An increasing sequence lies strictly below its limit. QED
- Interval cross-check for 2 <= n <= 2000: `code/kappa_mono.py`.

### The template (local models)
Fix v. A local model is assembled from mixtures of deterministic points (a0, a1, b0, b1).
- **F_i, all four outcomes in DKZ block i.**
  - In the adapted variables n1 = a0 - b0, n2 = b1 - a0, n3 = b0 - a1 - 1, n4 = a1 - b1 (mod k_i; all four DKZ link
    laws equal G_{k_i}), use the link law
        phi_i = [(v k_i/d) G_{k_i} + (1-v) k_i/d^2 - Z_i delta_0] / q_i,
        Z_i := (v k_i/d)(kappa_i - 1) - (1-v) k_i^2/d^2,
    with weight q_i = (v k_i/d)(2 - kappa_i) + 2(1-v) k_i^2/d^2 > 0.
  - Z_i is forced by the CGLMP mean. The outcome a0 is uniform in the block, and the four adapted variables are drawn
    from a composition law with marginals phi_i.
- **T_ij, weight t_ij (j another DKZ block, or the extra block).** Three outcomes lie in block i with their two
  within-block adapted variables equal to 0. The fourth (A0, A1, B0 or B1, 1/4 each) is uniform in block j.
- **T_Ci, weight t_Ci.** The fourth outcome is uniform in DKZ block i. The other three lie in C: (a_{1-x}, b0 = b1),
  or (a0 = a1, b_{1-y}), drawn from J(a,b)/m.
- **F_C.** Setting-independent points (a, a, b, b) with weight rho(a,b) = (v/d - Z_C/m) J(a,b) + (1-v)/d^2, where
  Z_C := (1/2) sum_i t_Ci.

**Bookkeeping lemma.** Suppose t >= 0 and:
- (a) t_ij + t_ji = w_ij and t_iC + t_Ci = w_iC, where w_ab = 4(1-v) k_a k_b/d^2 (k_C = m);
- (b) (1/2)(sum_{j DKZ} t_ij + t_iC) = Z_i for each DKZ block i;
- (c) rho >= 0.

Then the mixture equals v P + (1-v) u exactly, so P_v is local.

*Proof.*
- Count each cell type:
  - within block i at adapted difference n, the mass is [q_i phi_i(n) + Z_i [n=0]]/k_i = (v/d) G(n) + (1-v)/d^2;
  - every cross cell (block i x block j) gets (t_ij + t_ji)/(4 k_i k_j) = (1-v)/d^2, and likewise with C;
  - on C x C, rho + (Z_C/m) J = (v/d) J + (1-v)/d^2.
- phi_i is decomposable. By (b) and t >= 0 we have Z_i >= 0. Writing phi_i = aG + bu + c delta_0 with a + b + c = 1,
  the CGLMP mean (k_i - 1)/4 is equivalent to a(2 - kappa_i) + 2b = 1, and {b >= 0, c <= 0} is exactly the segment
  [phi_inf(k_i), Q_{k_i}].
- phi_inf is decomposable by Theorem PHI and Q by Theorem M, so phi_i is too, by convexity. QED

### Theorem DS_r
- **Upper bound (witness).** Let Phi = sum_i CGLMP_{k_i} restricted to block-i x block-i cells, zero on cross cells.
  - Its local bound is 2. If the four outcomes share a block, the CGLMP bound applies. Otherwise the 4-cycle
    a0-b0-a1-b1 has at least two cross links, and the at most two within links contribute <= 1 each.
  - Phi(u) = 0, because every row of a CGLMP table sums to 0.
  - Phi(P) = (2/d) sum_i k_i kappa_i.
  - So P_v is nonlocal for v > d/sum k_i kappa_i.
- **Lower bound.** Use the template at v = d/Sig with no extra block and
      t_ij = (w_ij/2)(1 + (kappa_i - kappa_j)/mubar),   mubar = sum_k (d_k/d)(kappa_k - 1).
  - Identity (b) follows from (1 - v)/mubar = v.
  - t_ij >= 0 because |kappa_i - kappa_j| < kappa_oo - sqrt2 < 0.0707 < sqrt2 - 1 <= mubar (Lemma K).
- **C2.** kappa_{d_i} < kappa_d gives d/Sig > 1/kappa_d. QED

### Theorem LB
- **(i), the witness.**
  - Coarse-grain every outcome outside the blocks of U (the extra block, and the DKZ blocks not in U) to a fixed
    deterministic point of one block of U with CGLMP value 2. Then evaluate Phi_U = sum_{i in U} CGLMP_{k_i}.
  - The coarse-grained functional is still <= 2 on local behaviours.
  - Value on P_v: v (2 Sig_U/d + 2(d - K_U)/d) + (1-v) 2 (d - K_U)^2/d^2. Noise cells with one coarse-grained end
    contribute 0, by the row sums or because the cell is cross.
  - This exceeds 2 iff v > (2d - K_U)/(d kbar_U + d - K_U) = v0(U). The block contents never enter, so (i) holds for
    any extra block T.
- **(ii), mode A at v = v0.**
  - Take t_ij = (w_ij/2)(1 + (kappa_i - kappa_j)/mu) with mu = (Sig - K)/(K + 2m), t_iC = w_iC and t_Ci = 0. Then
    Z_C = 0 and rho = (v/d) J + (1-v)/d^2 > 0.
  - From (1 - v0)/v0 = d(kbar - 1)/(K + 2m) we get (1 - v0)/mu = v0 d/K. Then
    (1/2) sum_j t_ij = (1-v) k_i (K - k_i)/d^2 + (v k_i/d)(kappa_i - kbar), and adding (1/2) t_iC = 2(1-v) k_i m/d^2
    gives exactly Z_i at v0.
  - t_ij >= 0 iff |kappa_i - kappa_j| <= mu.
  - The bound m <= 2.4K suffices because (Sig - K) >= (sqrt2 - 1) K and |kappa_i - kappa_j| < kappa_oo - sqrt2.
- **(iii).**
  - If (ii) applies, 1/v0 = (d kbar + m)/(d + m) < (d kappa_d + m)/(d + m) <= kappa_d.
  - Otherwise K < 0.412 m, so K/d < 0.292. Use mode B at v = v*: t_ij = w_ij/2,
    t_iC = 2 Z_i - 2(1-v) k_i (K - k_i)/d^2 and t_Ci = w_iC - t_iC.
    - t_iC >= 0 iff d(kappa_i - 1) >= (kappa_d - 1) K. This holds because (sqrt2 - 1)/(kappa_oo - 1) > 0.854 > K/d.
    - t_Ci >= 0 iff d(kappa_i - 1) <= (kappa_d - 1)(2d - K). This holds because kappa_i < kappa_d.
    - rho >= 0 follows from (kappa_d - 1) K (K + 2m) <= 0.4850 * 0.412 * 2.412 m^2 < d m.
  - Every inequality is strict, so v_c > v*. QED

### LB+, LB-exact, LB* and TH
- **LB+.**
  - In mode A, t_Ci = 0, so only F_C touches the T x T cells. There F_C must reproduce v (m/d) P_T + (1-v)/d^2 on all
    four links.
  - Normalised by W_C = v m/d + (1-v) m^2/d^2, this is v_T P_T + (1 - v_T) u_m, which is local iff v_T <= v_c(T).
  - Every other cell is as in the classical case.
- **LB-exact.**
  - In mode A, block i needs (1/2) sum_j t_ij = Z_i' := Z_i - 2(1-v) k_i m/d^2 from DKZ-DKZ edges, each split as
    t_ij + t_ji = w_ij.
  - By the Gale/Hall supply-demand theorem, a split exists iff the totals agree (that is v = v0) and, for every set Y
    of DKZ blocks, sum_Y 2 Z_i' >= w(E(Y)), i.e.
    v0 d (Sig_Y - K_Y) >= (1 - v0) K_Y (K_Y + 2m).
  - Using v0 d (Sig - K) = (1 - v0) K (K + 2m), this is equivalent to
    v0 d (Sig_U - K_U) <= (1 - v0) K_U (2d - K_U) for U = complement of Y, i.e. v0(U) >= v0.
- **LB\*, by induction on r.**
  - Let U* minimise v0(U), and T* = (the DKZ blocks outside U*) (+) C, on d' = d - K_{U*} dimensions.
  - Inside U*, the Hall condition holds by minimality.
  - Write f(U, D) = sig_U/(K_U (2D - K_U)) with sig_U = sum_U k_i (kappa_i - 1). The LB+ condition
    v_c(T*) >= v_T(U*) becomes, by the induction hypothesis for T*, f(U', d') <= f(U*, d) for every nonempty U'
    outside U*.
  - Optimality of U* against U* u U' gives (a + b)/((p + q)(2d - p - q)) <= a/(p(2d - p)), with a = sig_{U*},
    b = sig_{U'}, p = K_{U*}, q = K_{U'}.
  - This is equivalent to b p (2d - p) <= a q (2d' - q), which is exactly f(U', d') <= f(U*, d).
  - For m = 0 the law reduces to DS_r. QED
- **TH.** Write 1/v0(U) - 1 = d sig_U/g(K_U) with g(W) = W(2d - W), strictly concave. Put a_i = kappa_i - 1, which is
  strictly increasing in k_i (Lemma K), and F = F(U) for a maximiser U.
  - Let j not in U. Comparing U with U u {j} gives a_j <= F [g(W + k_j) - g(W)]/k_j.
  - Let i in U with |U| >= 2. Comparing U with U - {i} gives a_i >= F [g(W) - g(W - k_i)]/k_i.
  - Strict concavity makes the first slope strictly smaller than the second, so k_j < k_i.
  - If U = {i}, then a_j <= a_i (2d - 2k_i - k_j)/(2d - k_i) < a_i. QED

### Lemma U and Corollary P
- **Lemma U.** Take lambda = (a0, a1) uniform on Z_d^2 with a_x = lambda_x, and let Bob output b with probability
  K_y(b|a0,a1) = d Z(a0,b|0,y) + d Z(a1,b|1,y) - 1/d.
  - K_y >= 0 is the hypothesis, and sum_b K_y = 1.
  - Averaging over a_{1-x} returns Z(a_x, b|x,y).
- **Corollary P.** Let lam = v*/v_c(S), Delta = P(S') - P(S) and c = v* v_c/(v_c - v*). Then
      P_{v*}(S') = lam P_{v_c}(S) + (1 - lam)(u + c Delta),
  and u + c Delta has entries >= 1/(2d^2), so it is local by Lemma U. QED

## 3. Verification and reproduction

All scripts are in `code/`. They need Python 3 with numpy, scipy and mpmath (sympy is not needed). Logs are in
`logs/`.

| What | Command | Result |
|---|---|---|
| Theorem PHI, 4 <= n <= 50000 | `python run_verify.py 4 50000` (blocks as in `logs/verify_*.log`) | ALL PASS |
| Theorem PHI, n >= 50001: the n-independent checks | `python asym_check.py` | PASS (`logs/asym_check.log`) |
| Lemma K, interval cross-check | `python kappa_mono.py 2000` | `logs/kappa_mono.log` |
| DS_r template, end to end | `python ms_model.py` | model = v P + (1-v) u to 1.4e-16 |
| LB, mode A and mode B models | `python lb_model.py` | 18 cases, error <= 1.7e-16, weights >= 0 |
| LB with random classical blocks, plus LP v_c | `python lb_classical.py` | 9 cases; LP equals v0 to 2e-16 |
| LB+ | `python lb_general.py` | v_c = v0 in all 16 cases with v_c(T) >= v_T; the one case with v_c(T) < v_T has v_c < v0 |
| LB (single block) and multi-block LP tables | `python local_block.py`, `python multi_local.py` | LP v_c equals v0 (`multi_local.py` prints R = 1/v_c; compare with 1/v0 = (d kbar + m)/(2d - K)) |
| Lemma U and Corollary P sanity | `python nbhd_check.py` | 0 failures in 120 LPs |

`core.py` holds the shared conventions: behaviour, DKZ bases, and the LP for v_c over all d^4 deterministic points.

## 4. What is not claimed
- C2 for general strategies at d >= 5.
- One-sided classical blocks: Alice's bases equal, Bob's not. This held in LP tests only.
- Rotated or perturbed sums beyond the explicit neighbourhoods of Corollary P.
- Theorem M was independently re-certified only for n <= 100. Statements with a DKZ block of size > 100 rely on
  Theorem M as proved in `../noise-dkz-threshold/` (computer-assisted for n <= 2001, written proof for n >= 2002).
