# The white-noise threshold of DKZ against all Bell inequalities, for every d

Ansh Mishra, Aryan Senthilkumar. 2026-10-10.

**Status:** proved.
- **Computer-assisted part:** 3 ≤ d ≤ 2001, with two separately written implementations.
- **Written proof:** d ≥ 2002, with its numerical constants checked in ball arithmetic.
- **Review:** no separate re-verification report yet; not reviewed by outside experts.

## Setting

- **Scenario.** The (2,2,d) Bell scenario: settings x, y ∈ {0, 1}, outcomes a, b ∈ Z_d.
  - L is the local polytope and u the uniform behaviour.
  - For a behaviour p, the critical visibility is v_c(p) = max{v ∈ [0, 1] : v p + (1 − v) u ∈ L}.
  - For a maximally entangled state Φ_D and balanced projective measurements (every projector of rank D/d), white noise
    on the state, ρ_v = v Φ_D + (1 − v) 1/D², produces exactly the behaviour v p + (1 − v) u.
  - So v_c(p) is the critical visibility against **all** Bell inequalities of the scenario.
- **The CGLMP value.**
  - I_ME(d) = (4/(d(d−1))) Σ_{j=1}^{d−1} (d − j)/cos(π j/(2d)) is the maximal CGLMP value on maximally entangled
    states. It is attained by the DKZ measurements, uniquely up to local unitaries ([`../../papers/math`](../../papers/math),
    Theorems A and B; ledger input A2).
  - κ_d := I_ME(d)/2.
  - CGLMP is a valid Bell inequality with local bound 2, so v_c(p) ≤ 2/I(p) for the CGLMP value I(p) in any labelling.
- **Adapted link variables** of a deterministic point (a0, a1, b0, b1):
  - n1 = b0 − a0, n2 = a0 − b1, n3 = a1 − b0, n4 = b1 − a1 + d − 1, all mod d in {0, …, d−1}.
  - Since n1 + … + n4 ≡ d − 1 (mod d), the functional β(p) := Σ_i E_p[n_i] satisfies β ≥ d − 1 on L.
  - Equality holds exactly on the C(d+2,3)·d deterministic points whose adapted variables form a composition of d − 1.
- **β is the CGLMP facet.** β is the CGLMP functional in DKZ's labelling: I′(p) = 4 − 2β(p)/(d − 1). It defines a facet
  of L (Masanes, Quantum Inf. Comput. 3, 345 (2003); exact affine-rank check for d = 3, 4 in `verify_local.py`).
- **The DKZ link law.** All four adapted link laws of the DKZ behaviour equal G_d(n) = 1/(2d² sin²(π(4n+1)/(4d))),
  n = 0, …, d − 1. Hence I(DKZ) = 4 − 8·E_G[n]/(d − 1) = I_ME(d).
- **The critical point.** q* := u + (p_DKZ − u)/κ_d. All four of its adapted link laws equal Q_d := G_d/κ_d + (1 − 1/κ_d)/d.

**CLAIM_d.** Q_d is a mixture, with all weights strictly positive, of the laws (1/4) Σ_{i=1}^4 δ_{π_i}, where π runs over
the compositions (equivalently, partitions) of d − 1 into four nonnegative parts.

## Main result

**Theorem (DKZ threshold and local optimality).** For every d ≥ 3:
1. **Exact threshold.** v_c(DKZ_d) = 2/I_ME(d). So the CGLMP inequality is an optimal Bell inequality for the DKZ
   behaviour under white noise: no Bell inequality of the (2,2,d) scenario detects the noisy DKZ behaviour at a visibility
   below 2/I_ME(d).
2. **Strict local optimality.** There is δ_d > 0 such that every behaviour p with uniform marginals and |p − p_DKZ| < δ_d
   has v_c(p) = 2/I′(p).
   - In particular, every balanced maximally entangled strategy (any local dimension D) whose behaviour lies in this
     neighbourhood has v_c(p) ≥ 2/I_ME(d), with equality only for p = p_DKZ.

The values are 2/I_ME(d) = 0.69615 (d = 3), 0.69055 (d = 4), 0.68716 (d = 5), …, decreasing to π²/(16·Catalan) ≈ 0.67344.

*Proof.* Theorem LOC below holds for every d for which CLAIM_d holds, and Theorem M proves CLAIM_d for every d ≥ 3.
Statement 1 is Theorem LOC (c) at p = p_DKZ. ∎

**What is not claimed.**
- This is not the full noise clause of 27B (ii) for d ≥ 5. It says DKZ's own threshold is exactly 2/I_ME(d), and that no
  nearby strategy does better.
- The full clause (no strategy at all does better) is proved for d ≤ 4 ([`../noise-complete-vn/`](../noise-complete-vn/))
  and, within covariant strategies, for d = 5, 6, 7 ([`../noise-covariant/`](../noise-covariant/)).

## Theorem LOC (local optimality, assuming CLAIM_d)

**Theorem LOC.** Assume CLAIM_d. Then:
- (a) q* is a strictly positive combination of all tight vertices of the CGLMP facet F*. So q* lies in the relative
  interior of F*, and F* is the only facet of L through q*.
- (b) There is r > 0 such that every q in aff(L) with β(q) = d − 1 and |q − q*| < r is local.
- (c) There is δ > 0 such that every behaviour p with uniform marginals and |p − p_DKZ| < δ has v_c(p) = 2/I′(p).

*Proof.*
- (a) Spread each weight w_π uniformly over the distinct permutations of π. This gives an exchangeable law ν > 0 on
  compositions whose four one-dimensional marginals are all Q_d.
  - Each composition n is the image of exactly one Z_d-orbit of d tight deterministic points, and their average t_n is the
    covariant behaviour with these link differences.
  - So Σ_n ν(n) t_n is covariant with the four link laws of q*, hence equals q*.
  - Expanding t_n gives weight ν(n(λ))/d > 0 to every tight vertex λ.
- (b) Take an affine basis of the facet hyperplane among the tight points. Then q − q* = Σ ν_λ λ with Σ ν_λ = 0 and
  |ν| ≤ C|q − q*|. For |q − q*| < min_λ μ_λ / C (μ the weights from (a)), all weights stay ≥ 0.
- (c) The point q(p) = u + (2/I′(p))(p − u) lies on the hyperplane β = d − 1, and it depends continuously on p near p_DKZ,
  with q(p_DKZ) = q*.
  - By (b), q(p) is local, so v_c(p) ≥ 2/I′(p).
  - Also v_c(p) ≤ 2/I′(p), because the CGLMP inequality I′ ≤ 2 is valid.
  - For maximally entangled p: I′ ≤ I_ME(d), with equality only for DKZ up to local unitaries (input A2, every relabelling,
    any D). So in a small ball, equality forces p = p_DKZ. ∎

**Remark (arbitrary PVM ranks, Lemma CG).** For projective measurements of arbitrary ranks on Φ_d (zero projectors
allowed), with behaviour p and white noise n_p, there is a rank-one PVM strategy p̃ on Φ_d with v_c(p; n_p) ≥ v_c(p̃; u).
- Refine each projector in an orthonormal basis adapted to ⊕_a ran(A^x_a). Then p = c(p̃) and n_p = c(u) for a
  coarse-graining c.
- c is linear and maps deterministic points to deterministic points, so c(L) ⊆ L.

## Theorem M: CLAIM_d holds for every d ≥ 3

Write S = d − 1.

**Lemma 1 (pairing).** Let π be a symmetric coupling of (Q, Q) with these properties:
- it is supported on T = {(x1, x2): x1 + x2 ≤ S} and positive on T;
- its sum law R(y) = Σ_{x1+x2=y} π(x1, x2) satisfies R(y) = R(S − y).

Then P(x) = π(x1, x2) π(x3, x4) / R(x1 + x2) is a coupling of four copies of Q on the compositions of S, and it is positive
on every composition. Symmetrising over the 4! orders gives CLAIM_d.

*Proof.*
- Draw (X1, X2) ~ π, then (X3, X4) ~ π conditioned on the sum S − X1 − X2.
- That conditioning event has the same R-probability, so the law of (X3, X4) is Σ_y R(S − y) π(· | S − y) = π. ∎

**Lemma 2 (core).** Split T into four parts:
- the interior I = {x1, x2 ≥ 1, x1 + x2 ≤ S − 1};
- the edges (x, 0), (0, x) for x ≥ 1;
- the antithetic cells (x, S − x) for 1 ≤ x ≤ S − 1;
- the cell (0, 0).

Let π_I ≥ 0 be symmetric on I, with marginal m_I and sum law R_I, and put F := m_I − R_I/2. Suppose:
- (C1) F(y) − F(S − y) = D(y) := Q(y) − Q(S − y) for 1 ≤ y ≤ S − 1;
- (C2) ρ := Q − m_I > 0 on 1, …, S − 1.

Put:
- A(x) := min(ρ(x), ρ(S − x))/2 on (x, S − x);
- E(x) := ρ(x) − A(x) on (x, 0) and (0, x), for 1 ≤ x ≤ S − 1;
- E(S) := Q(S) on (S, 0) and (0, S);
- z0 := Q(0) − Σ_{x≥1} E(x) on (0, 0).

Then π is a symmetric coupling of (Q, Q) on T with symmetric sum law. It is positive on T if π_I > 0 on I and z0 > 0.

*Proof.*
- **Marginals.** Row x ∈ {1, …, S−1} sums to m_I + A + E = Q. Row S is E(S) = Q(S). Row 0 is z0 + Σ E = Q(0).
- **Sum law in the middle.** For 1 ≤ y ≤ S − 1, R(y) = R_I(y) + 2E(y). Since A(y) = A(S − y), the symmetry
  R(y) = R(S − y) is equivalent to (C1).
- **Sum law at the ends (y = 0 vs y = S).** Σ_y (S − 2y) R(y) = S − 4E_Q[X] = 0, by the mean identity E_Q[X] = S/4. That
  identity is equivalent to I′(q*) = 2, i.e. to the definition of κ_d. The pairs y, S − y with 1 ≤ y ≤ S − 1 cancel, so
  S(R(0) − R(S)) = 0.
- **Positivity of the corner.** z0 ≥ Q(0) − Σ_{x≥1} ρ(x) ≥ 2Q(0) − 1. ∎

**The construction.** Put L := ⌊(S − 1)/2⌋ and M := S − L − 1.
- (a) **Regulariser.** Weight η′ > 0 on every interior cell with x1 + x2 ≤ M. Then
  F_η(z) = η′[max(0, M − z) − ((z − 1)/2)·1{2 ≤ z ≤ M}], supported on [1, M], and F_η(S − z) = 0 for z ≤ L.
- (b) **Families y = 1, …, L.** Weight w_y on every cell (t, S − y − t), t = 1, …, S − y − 1.
  - Their sums S − y lie in [S − L, S − 1], disjoint from (a).
  - The antisymmetric part of F_y on 1, …, L is w_y·1_[1,y] + ((S − y − 1)/2)·w_y·δ_y.
- So (C1) on 1, …, L, and by antisymmetry on all of 1, …, S − 1 (at y = S/2 both sides vanish), is the triangular system

  w_z = 2(D̃(z) − T(z))/(S − z + 1),  T(z) = Σ_{y=z+1}^{L} w_y,  D̃(z) = D(z) − F_η(z),  z = L, L−1, …, 1.

- Then m_I(x) = Σ_{y ≤ min(L, S−1−x)} w_y + η′·max(0, M − x), and every cell of I is covered by (a) or (b).
- So the construction proves CLAIM_d as soon as the following hold, with η′ := D(L)/(100 S):
  - (P1) D̃(z) > T(z) for 1 ≤ z ≤ L;
  - (P2) Q(x) > m_I(x) for 1 ≤ x ≤ S − 1;
  - (P3) 2Q(0) > 1.

### Positivity for 3 ≤ d ≤ 2001 (computer-assisted)

κ_d is computed from its definition κ_d = I(DKZ_d)/2 = 2 − 4E_G[n]/(d − 1), so the mean identity holds exactly.

`lemmaM_verify.py` checks (P1)–(P3) in ball arithmetic (python-flint, 120 bits) for every d = 3, …, 2001: ALL VERIFIED.
The worst margins are (D̃ − T)/D̃ ≥ 0.8021 and ρ/Q ≥ 0.9094, with ball radii about 1e-30.

`lemmaM_verify_iv.py` is separately written code in mpmath interval arithmetic:
- Part B repeats (P1)–(P3) for d = 3, …, 2001: ALL VERIFIED.
- Part A builds the full pairing matrix for d = 3, …, 150 and checks directly, without Lemma 2:
  - positivity on T and zero off T;
  - symmetry, marginals and the symmetric sum law.

  ALL VERIFIED.
- A tamper test (Q(3) + 1e-6) is detected.

Spot checks at d = 5000, 10000 and 40000 give margins 0.8017 and 0.9095.

### Positivity for d ≥ 2002 (written proof)

**Notation.**
- φ(t) = (4t+1)^{−2} − (4t+3)^{−2} > 0, strictly decreasing.
- Σ_{t≥0} φ(t) = C (Catalan's constant), and ∫_z^∞ φ = 1/(2(4z+1)(4z+3)).
- φ(t) ≤ 1/(15t³) for t ≥ 10 (from φ(t) = 16s/(16s² − 1)², s = t + 1/2).
- Φ(t) = Σ_{k≥0} φ(t + kd) and A′ = 8/(π²κ).

**Steps.**
- (i) **D is decreasing.** The partial fractions 1/sin²(πx) = π^{−2} Σ_k (x − k)^{−2} give
  G(n) = (8/π²) Σ_{k∈Z} (4(n − kd) + 1)^{−2}. Re-indexing the reflected terms gives D(z) = A′[Φ(z) − Φ(S − z)]. So D is
  strictly decreasing on 1, …, L, and D(L) > 0.
- (ii) **κ_d is close to its limit.** κ_d = κ_∞ − 32Δ_d/(π² S), with κ_∞ = 16C/π² and
  Δ_d = Σ_n n Φ(n) ∈ [0, Σ_{t≥1} t φ(t)] = [0, 0.0467916].
  - For S ≥ 2001 this gives 1.48483 ≤ κ_d ≤ 1.48491, A′ ≤ 0.54590 and c·d ≥ 0.32652, where c := (1 − 1/κ_d)/d ≤ Q.
  - The formula is checked against the closed form of I_ME(d)/2 in `lemmaM_constants.py`.
- **(P3).** Q(0) ≥ G(0)/κ ≥ (8/π²)/κ_∞ (from sin x ≤ x), so 2Q(0) − 1 ≥ 16/(π²κ_∞) − 1 = 0.0917 > 0.
- **(P1).** |F_η| ≤ η′S ≤ D(L)/100 ≤ D(z)/100, so D̃ ∈ [0.99D, 1.01D]. With γ = 0.99/4.04 it suffices to show

  (∗) Σ_{y=z+1}^{L} D(y) < γ(S + 3)D(z) for 1 ≤ z ≤ L.

  - By downward induction, w_y ≤ 2D̃(y)/(S − y + 1) ≤ 4.04 D(y)/(S + 3). So T(z) ≤ (4.04/(S + 3)) Σ_{y>z} D(y) < 0.99 D(z)
    ≤ D̃(z).
  - **Case z ≥ z1 := (S − 1)/2 − γ(S + 3).** The sum has L − z ≤ γ(S + 3) terms, each smaller than D(z).
  - **Case z < z1.** Here z + 1 < 0.255S and a := S − z > 0.745S ≥ 1490.
    - LHS ≤ A′ Σ_{t>z} φ(t) ≤ A′/(2(4z+1)(4z+3)).
    - D(z) ≥ A′[φ(z) − Φ(S − z)], with Φ(S − z) ≤ φ(a) + (1/d)∫_a^∞ φ ≤ 1/(15a³) + 1/(32Sa²).
    - Using 16(2z+1)/((4z+1)(4z+3)) ≥ 2/(z+1) and 2(4z+1)(4z+3) ≤ 32(z+1)², (∗) follows from
      γ((S+3)/S)[2/0.255 − 32(0.255)²(1/(15·0.745) + 1/32)/0.745²] ≥ 0.24505·7.392 = 1.811 > 1.
- **(P2).** m_I(x) ≤ Σ_y w_y + η′S ≤ (4.04/(S+3))·A′(C − 8/9) + D(L)/100 ≤ (0.05972 + 1e-9)/d < 0.32652/d ≤ c ≤ Q(x).
  This uses Σ_{y≤L} D(y) ≤ A′ Σ_{t≥1} φ(t) = A′(C − 8/9), with C − 8/9 = 0.0270767.

All numerical constants are enclosed in ball arithmetic by `lemmaM_constants.py`. ∎

**Earlier certificates.** CLAIM_d was certified before, for 3 ≤ d ≤ 100, by a different method: a relative-interior
certificate on the CGLMP face.
- `cert_local.py`: mpmath intervals with an exact rational basis inverse.
- `verify_local.py`: separately written, Python fractions only, for d ≤ 30.

They agree with Theorem M.

**How the construction was found.**
- The pairing linear program is feasible with margin about 3.7/d for d ≤ 200 (`lemmaM_pairing.py`, `lemmaM_structure.py`).
- A first product-core ansatz (`lemmaM_core.py`) works up to d = 1280, but its margin decays like log d
  (`lemmaM_margin.py`).
- The near-antithetic core above has margins that converge as d grows (0.802 and 0.9095).

**Numerical consistency.** A linear program over all d⁴ deterministic points gives v_c(DKZ_d) = 2/I_ME(d) to machine
precision for d = 3, …, 10 (`dkz_vc_lp.py`).

## Priority

As far as we found, this has been known only numerically, for small d:
- Kaszlikowski, Gnaciński, Żukowski, Miklaszewski and Zeilinger, Phys. Rev. Lett. 85, 4418 (2000), up to d = 9;
- Durt, Kaszlikowski and Żukowski, Phys. Rev. A 64, 024101 (2001), up to d = 16.

We found no proof for general d. Our search (2026-10-10) covered the web, arXiv and the openai/math release.
