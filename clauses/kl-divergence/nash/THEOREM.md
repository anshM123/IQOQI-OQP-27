# The KL clause at d = 3: DKZ_3 is a Nash equilibrium (Theorem N)

Ansh Mishra, Aryan Senthilkumar. Folder `clauses/kl-divergence/nash/`.

2026-10-20. **Status:** proved, computer-assisted (the statement below only; the KL clause at d = 3 itself remains
OPEN). Not reviewed by outside experts.

## Statement

The setting and notation are those of `../THEOREM.md`:
- the scenario (2,2,3) and the maximally entangled state Phi_3;
- S^UNI, the van Dam-Gruenwald-Gill strength with uniform setting distribution;
- DKZ_3 = (A*, B*), with S0 = S^UNI(DKZ_3) = 0.05778302549332865 bits.

**Theorem N.**
- (Bob side) For every pair of Bob PVMs (B_0, B_1) on C^3: S^UNI(A*_0, A*_1; B_0, B_1) <= S0.
- (Alice side) For every pair of Alice PVMs (A_0, A_1): S^UNI(A_0, A_1; B*_0, B*_1) <= S0.

So neither party can increase the uniform-setting KL strength by changing only its own measurements: DKZ_3 is a Nash
equilibrium of this common-payoff game. Equality holds at DKZ_3. For the reduced problem of Theorem N' below,
Phi(A*, B; mu*) = S0 holds only at the symmetry images of DKZ_3's Bob bases.

**Scope.**
- Theorem N is a statement about unilateral deviations.
- It does **not** prove the KL clause of 27B(iii) at d = 3. That clause needs the maximum over both parties jointly,
  and it remains OPEN.
- Theorem N strengthens Theorem 3 of `../THEOREM.md` (strict local optimality) and the global optimality inside the
  Fourier-shift family (`../fourier-family/`).
- Only S^UNI is treated here.

The proof is computer-assisted. Every computation uses rigorous interval arithmetic with outward rounding, and logs,
sines and cosines are computed by series with Lagrange remainders (no C-library transcendentals).

## Proof

### 1. Lemma R (exact decoupling)

Every local model has the form Q(a, b | x, y) = sum_{a0,a1} mu(a0, a1) [a_x = a] K_y(b | a0, a1). Here mu is a law of
Alice's deterministic pair and K_0, K_1 are stochastic kernels; conversely, every such triple is local. Hence

    S^UNI(A; B_0, B_1) = min_mu (1/2) sum_y Phi(A, B_y; mu),
    Phi(A, B; mu) = min_K (1/2) sum_x D(P_xy || Q_xy(mu, K)).

With mu = mu* (the Alice marginal of the optimal local model of DKZ_3, Proposition K3(iv)):

    S^UNI(A*; B_0, B_1) <= max_B Phi(A*, B; mu*).

So the Bob side follows from **Theorem N':** max_B Phi(A*, B; mu*) <= S0. This is a 6-dimensional problem in Bob's basis
modulo column phases. PVMs of lower rank reduce to bases by coarse-graining (data processing).

### 2. Symmetries and domain

Write Bt for the steered Bob basis, so P(a, b | x, y) = |<a_x | Bt e_b>|^2 / 3. Phi(A*, ., mu*) is invariant under:
- **Column permutations** of Bt. These relabel b.
- **Complex conjugation.** It relabels Alice's outcomes, and mu*(m) is invariant under m -> 1 - m.
- **Left multiplication by D = diag(e^{i pi k/3}).**
  - <a_0 | D v> = <a_1 | v> and <a_1 | D v> = <(a-1)_0 | v>.
  - mu*(a0, a1) = f(a1 - a0) with f(0) = f(1) exactly (both equal 2(4 P2/12) + P1/12 in Proposition K3(iv)), so
    mu*(a1, a0 + 1) = mu*(a0, a1).
  - The kernel relabelling K'(b | a0, a1) = K(b | a1 - 1, a0) then gives p_0(K') = p_1(K) and
    p_1(K')(a, .) = p_0(K)(a - 1, .), so the divergence is unchanged.
  - D^2 = Z = diag(1, w, w^2).

In CKM coordinates (theta12, theta13, theta23, delta, f1, f2) this gives the domain
D' = [0, pi/2]^3 x [0, pi] x [0, pi/3] x [0, 2 pi], whose upper ends are rounded up, intersected with the region
R = {|Bt00| >= |Bt01| >= |Bt02|}. The global maximisers in D' ∩ R are the two DKZ copies (6,0,6) and (6,4,14)
(units pi/12), and sympy proves that they are exact symmetry images of DKZ's Bob bases.

### 3. Lemma E (exactness at the copies)

Let x_c be a copy, Kc the relabelled conditional kernel of p* (Proposition K3(iv)), and Mz any slope supported on
supp Kc with zero b-sums. For g(z) = (1/2) sum_x D(q_x(z) || p_x(Kc + Mz z)):

    g(0) = S0  and  grad g(0) = 0  exactly.

*Proof.*
1. q(0) is the DKZ level law (K3(ii)) and p(Kc) = p*. So g(0) = sum_k Q_k log r_k = S0 (K3(iii), K3(v)).
2. Since sum q' = 0, grad g(0) = (1/2) sum_c q_c' log r*_c - (1/2) sum_c r*_c (P Mz)_c.
3. The first sum is sum_k log r_k dPi_k = 0 by the exact criticality of the level probabilities (proof of Theorem 3,
   E4). That criticality holds in all 36 directions, Bob's included.
4. The second sum vanishes. Kc solves the convex single-setting problem (the optimum of Lemma R is optimal for each y),
   so KKT gives r_0(a0, b) + r_1(a1, b) = const(a0, a1) on supp Kc(. | a0, a1). The second sum is then
   sum_{a0,a1} mu*(a0, a1) const(a0, a1) sum_b Mz(b | a0, a1) = 0, by the zero b-sums. QED

### 4. Local certificates (Gram-Schmidt cubes)

Around each copy, use the chart Bt(z) = Btc Q(z), where z is the strictly lower part of L(Btc^H Bt) (an LU chart with
explicit inverse). The claim is Phi < S0 for 0 < |z|_inf <= 0.1.
- **Star cube**, radius 0.00509. By Lemma E and Taylor models of degree 3 with a quartic remainder,
  g(z) <= S0 - (lam/2)|z|^2 + A3 |z|_inf^3 + K4 |z|_inf^4 < S0. Here lam = 0.98 lam_min(-H) is certified by an
  interval Cholesky.
- **Rest of the cube**: a Taylor-model branch-and-bound with 121,016 and 121,006 certified leaves, respectively, which
  tile the cube exactly.
- Re-certified on 2026-10-19 with the current code (hashes in `certificates/local/CODE_SHA256.txt`): 104,780 leaves for (6,0,6) and 104,786 for (6,4,14), with worst ub - S0 = -2.89e-9 and -3.39e-9.

### 5. Global branch-and-bound outside the cubes: the tracking bound

On a box c + [-h, h] in CKM coordinates, write dq(y) = q(y) - q(c) and use the kernel model
K(y) = K0 + R dq(y):
- K0 is an exact dyadic stochastic kernel, with exact zeros on a face Z;
- R is exact (grid 2^-30), with zero rows on Z and exact zero b-sums.

Then p(y) = p0 + Lam dq(y), with Lam = P R, is affine in q(y). Since g_K = G o q with G convex, the Bregman divergence of
G gives the exact identity

    g_K(y) = F + w.dq(y) + (1/2) sum_c d(q_c(y), r0_c p_c(y)),       d(a, b) = a log(a/b) - a + b,

where F = g_K(c), r0 = q(c)/p0, w_k = (1/2)(log r0_k + 1) - (1/2) sum_c r0_c Lam_ck, and
q_c(y) - r0_c p_c(y) = (E dq)_c with E = I - diag(r0) Lam. The upper bound combines:
- d(a, b) <= kappa (a - b)^2, with kappa = min(1/b_lo, 1/(2 min(a_lo, b_lo)));
- Taylor expansion with one mean value per cell, applied to w.dq and E dq, using rigorous order-3 jets of q;
- shifts orthogonal to W = {zero row and column sums in each x-block}, which are exact because dq(y) lies in W;
- Young's inequality;
- a rigorous box QP (scaled Gershgorin, certified isotropic eigenvalue, Lagrangian dual with interval Cholesky).

The model is valid on the box when K(y) >= 0 there. This is checked entrywise by K0_e >= sum_i |(R q'(c))_e,i| h_i +
(1/2) sum |(R q''(box))_e,ij| h_i h_j, after which Phi <= g_K on the box.

The branch-and-bound:
- covers D' with 9,216 initial boxes;
- discards boxes rigorously outside R;
- accepts boxes inside a local cube (rigorous enclosure of z over the box);
- certifies a box when ub < S0.lo;
- otherwise bisects.

Result (2026-10-20):
- All 4,224 initial boxes that meet R are covered, and no box is unresolved.
- 73,881,732 evaluations: 51,580,895 certified boxes, 4,448,541 boxes rigorously outside R and 18,983 boxes inside the
  local cubes.
- The largest certified upper bound is S0.lo - 3.95e-10 nats. On that box the sampled true Phi is <= 0.32 S0; the bound
  is loose there but still below S0.

### 6. Alice side (party swap)

- P(a, b | x, y) is symmetric under exchanging the parties together with complex conjugation.
- After the exchange, conjugation turns Bob's shift pattern (1/4, -1/4) into (-1/4, 1/4).
- The phase unitary W = diag(e^{i pi k/6}) adds 1/4, giving (0, 1/2): Alice's pattern after relabelling the settings.
  Born probabilities are unchanged because Phi_3 is U (x) conj(U) invariant.
- S^UNI is invariant under party exchange and relabellings, so the Alice side is the Bob side of an equivalent problem.
QED

## Verification

- **Independent audit (three rounds, `audit/AUDIT_TRACK.md`).** It covers:
  - the mathematics of the tracking bound (proved);
  - the implementation, including high-precision containment and sampling checks on more than 2,000 certified boxes;
  - the compiled implementation;
  - the domain reduction and symmetries;
  - the local cube certificates.

  All reported issues were fixed before the final run.
- **Completeness check** (`check_run.py`, output in `certificates/global/CHECK_RUN_v22.txt`): COMPLETE. Every initial
  box has a result from the final engine, with no unresolved boxes, and the certified, outside-R and local volumes sum
  to the box volume.
- **Cross-check**: 32 randomly chosen initial boxes were re-run with the independent numpy implementation, and all
  were certified (708,273 evaluations, none unresolved). The two initial boxes containing DKZ copies, 3074 and 3090, were
  also re-run with the numpy implementation, including the local-cube handoff, and were fully certified.
- **Code hashes**: `certificates/global/CODE_SHA256_v22.txt` and `certificates/local/CODE_SHA256.txt`.

## Reproduction

See `README.md`.
