# The Kullback–Leibler clause at d = 3: the Fourier-shift family, and reductions

Ansh Mishra, Aryan Senthilkumar. 2026-10-09/10.

The strengths S^UNI ≤ S^UC ≤ S^COR are the three statistical strengths of van Dam, Grünwald and Gill, as defined in
[`../THEOREM.md`](../THEOREM.md). Logarithms are natural unless "bits" is written.

S0 := S(DKZ_3) = 0.05778302549332865 bits = 0.0400521412049241968 nats. This is the same for all three strengths.

Whether DKZ_3 maximises the strength over all PVM strategies on Φ_3 (clause 27B (iii) at d = 3) remains **open**. The
following are known:
- DKZ_3 is a strict local maximiser ([`../THEOREM.md`](../THEOREM.md), Theorem 3).
- No numerical search has found anything larger.

This folder proves global optimality inside a natural three-parameter family, and records three reductions.

## Theorems F3 and F3′: global optimality in the Fourier-shift family

**The family F3** is the CGLMP/DKZ family with continuous shifts. With w = e^{2πi/3} and real s_x, t_y, the measurement
vectors are:
- Alice: |a⟩_x = 3^{−1/2} Σ_k w^{k(a + s_x)} |k⟩;
- Bob: |b⟩_y = 3^{−1/2} Σ_k w^{−k(b + t_y)} |k⟩.

**Its behaviours.**
- On Φ_3, q(a, b | x, y) = K(φ_xy + 2π(b − a)/3)/3, with K(ψ) = (3 + 4 cos ψ + 2 cos 2ψ)/9 and φ_xy = 2π(t_y − s_x)/3.
  This was checked against the state to 6e-16.
- **Coordinates.** z = (φ_00, φ_01, φ_10) ∈ R³, with φ_11 = φ_01 + φ_10 − φ_00. Every z occurs.
- **Relabellings.** Translations z ↦ z + (2π/3)k, k ∈ Z³, are outcome relabellings. So the fundamental domain
  [0, 2π/3]³, inside the covered box [0, 9/4]³, suffices.

**Theorem F3.** For every strategy of F3, S^UNI(q) ≤ S0. Equality holds if and only if z is a translate of (π/6, π/2, π/2)
or (π/2, π/6, π/6), i.e. if and only if the strategy is DKZ_3 up to relabelling.

**Theorem F3′.** For every strategy of F3, S^COR(q) ≤ S0, so S^UNI ≤ S^UC ≤ S^COR ≤ S0. Equality holds only at the
DKZ copies.

Both theorems are computer-assisted. The proof has five steps.
1. **Reduction.** F3 behaviours are shift-invariant. So S^UNI(z) = min_μ F(z; μ), with μ a law on the 27 reduced
   strategies (α, b0, b1), and F(z; w) ≥ S^UNI(z) for every sub-probability w.
2. **The copies (exact, sympy in Q(√3), `GLOBAL_fam3_exact.py`).** Among the 64 points of (π/6)Z³ in [0, 2π/3)³, eight
   have four DKZ-type link laws.
   - Exactly two are DKZ copies: (π/6)(1, 3, 3) and (π/6)(3, 1, 1). At both, criticality and the identities of the KKT
     model hold exactly.
   - At the other six, the minimal CGLMP level sum is 0, so they are not copies. They are ordinary points of the
     branch-and-bound.
3. **Local cubes.**
   - At each copy, the exact KKT model plus a dyadic first-order correction gives F(z_c) = S0 and ∇F(z_c) = 0 exactly.
   - A Cholesky factorisation in ball arithmetic shows that the Hessian enclosure over the cube |z − z_c|_∞ ≤ 1e-3 is
     negative definite. So F < S0 on the punctured cube.
   - For S^COR, a link depends on z only through its own phase, so each link Hessian alone is singular. A dyadic quadratic
     correction that equalises the four link Hessians removes this. Every link then has D_l(z_c) = S0 and ∇D_l(z_c) = 0
     exactly, and negative-definite Hessian enclosures on a cube of radius 2e-4.
4. **Branch-and-bound over [0, 9/4]³** with exact dyadic bisection. A box is certified by any of three rigorous upper
   bounds, computed in ball arithmetic (python-flint, 106 bits):
   - (a) the copy model plus Taylor (boxes within 0.12 of a copy);
   - (b) a model fitted at the centre, with a first-order slope plus Taylor, using the complete per-cell derivatives of
     Q log(Q/P), and with a dual bound for the quadratic;
   - (c) a separable bound: a constant model, each link's supremum over its phase interval by subdivision and convexity.

   For S^COR, the weak duality S^COR ≤ min_p max_l D(q_l ‖ p_l) is used with minimax weights at the centre.
5. **Runs.**
   - **S^UNI** (`GLOBAL_fam3BB.py run`, 509 s): [0, 9/4]³ is tiled exactly by 37,863 certified boxes. The smallest gap is
     S0 − UB = 2.28e-9 nats.
   - **S^COR** (`GLOBAL_fam3COR.py run 0 2` and `run 1 2`, two halves of about 1,400 s each): 189,371 boxes. The smallest
     gap is 2.69e-13 nats.
   - The certificates (box centres, half-widths, methods and stored models) are `GLOBAL_fam3BB_cert.npz`,
     `GLOBAL_fam3COR_cert_part0of2.npz` and `GLOBAL_fam3COR_cert_part1of2.npz`.

**Checks.**
- **Certificate re-check** (`GLOBAL_fam3_recheck.py uni` and `cor`). This checks:
  - the exact tiling, via the bisection tree in fractions;
  - the cubes, re-certified;
  - every bound, recomputed from the stored models.

  Result: CERTIFICATE RE-CHECKED for both strengths. This re-check uses the same bound functions as the runs, so it is a
  reproducibility check, not a separate implementation.
- **Separately written checks**, in mpmath interval arithmetic:
  - both local cubes for S^UNI (`GLOBAL_fam3_cube_ivcheck.py`) and for S^COR (`GLOBAL_fam3COR_cube_ivcheck.py`): the
    model is valid, and the interval Cholesky of −[H] succeeds;
  - a random sample of 400 separable-bound boxes for each strength (`GLOBAL_fam3_sep_ivcheck.py`): all are below S0.

## Three reductions for the full problem

**Lemma R (Alice-joint decoupling; proved).** For a strategy (A, B_0, B_1), with A = (A_0, A_1), let
q_x(A, B)(a, b) = |(A_x† conj(B))_{ab}|²/3. Then for every law μ of (a0, a1) on Z_3²:
- S^UNI(q) ≤ (1/2)[Φ(A, B_0; μ) + Φ(A, B_1; μ)], with Φ(A, B; μ) := min_K (1/2) Σ_x D(q_x(A, B) ‖ p_x(μ, K));
- S^COR(q) ≤ max_y Ψ(A, B_y; μ), with Ψ(A, B; μ) := min_K max_x D(q_x(A, B) ‖ p_x(μ, K)).

Here K ranges over kernels K(b | a0, a1), and p_x(μ, K)(a, b) = Σ_{(a0,a1): a_x = a} μ(a0, a1) K(b | a0, a1).

*Proof.* p(a0, a1, b0, b1) = μ(a0, a1) K_0(b0 | a0, a1) K_1(b1 | a0, a1) is a mixture of deterministic strategies, and its
link (x, y) is p_x(μ, K_y). Minimise the y-terms separately. For S^COR use max_σ min_p ≤ min_p max_σ. ∎

**Consequence.** "No Bob strategy beats DKZ_3 against DKZ_3's Alice" follows from the single six-dimensional inequality
max_B Φ(A*, B; μ*) ≤ S0. Here μ* is Alice's marginal of the symmetric decomposition of the optimal local model.
Numerically (`GLOBAL_lemmaR_test.py`), the inequality holds with equality at DKZ: 40 random-start maximisations found no
value above S0. A rigorous proof would be a six-dimensional branch-and-bound.

**Lemma JM (one-sided local hidden states; proved).** Let Alice use bases (α^x_a), and let Bob's steered states φ^y_b be
the columns of conj(B_y). For any jointly measurable POVM pair E = (E^0, E^1) on C³ with parent POVM M_{a0a1}, the
behaviour p(a, b | x, y) = ⟨φ^y_b | E^x_a | φ^y_b⟩/3 is local. Writing π_φ(M) for the outcome law of the measurement M
on the state φ, this gives:
- S^UNI(q) ≤ (1/2) max_φ Σ_x D(π_φ(A_x) ‖ π_φ(E^x));
- S^COR(q) ≤ max_x max_φ D(π_φ(A_x) ‖ π_φ(E^x)).

*Proof.* P(a0, a1, b0, b1) = (tr M_{a0a1}/3)·K_0(b0 | a0a1)·K_1(b1 | a0a1), with
K_y(b | a0a1) = ⟨φ^y_b | M_{a0a1} | φ^y_b⟩/tr M_{a0a1}, is a probability law whose (x, y) marginal is p_xy. ∎

These bounds are **not** tight at DKZ_3 (`jm_relax.py`, convex programs): the best one gives 0.0578727 bits > S0. So the
optimal local model of DKZ_3 is not of this form.

**Proposition H (no hull argument; proved).** Let I be the CGLMP_3 functional in DKZ_3's labelling, and let G be any set
of behaviours such that every non-covariant g ∈ G satisfies I(g) ≤ I_ME − ε, for a fixed ε > 0. Then for every chart
direction z at DKZ_3 whose first-order image Jz has a nonzero non-covariant component, p(sz) ∉ conv(G) for all small s > 0.
- G may contain:
  - every covariant maximally entangled behaviour (all of F3, the whole DFT + phase family);
  - all their relabellings and local post-processings;
  - all local behaviours.
- Consequence: no argument through convex hulls of covariant families, plus relabellings, post-processings and local
  models, can prove the clause at d = 3.

*Proof.* Let π⊥ be the projection onto the orthogonal complement of the covariant subspace, and Δ := I_ME − I (affine,
≥ 0 on G).
- **Upper bound on π⊥.** For p = Σ μ_i g_i, π⊥(p − p_DKZ) = Σ_{non-covariant g_i} μ_i π⊥(g_i). So
  |π⊥(p − p_DKZ)| ≤ (C/ε)Δ(p).
- **Along the curve p(sz).** |π⊥(p(sz) − p_DKZ)| = s|π⊥Jz| + O(s²). But Δ(p(sz)) = O(s²), because DKZ_3 maximises I.
  This contradicts the bound for small s.
- **Why the listed families qualify.**
  - A relabelling with mixed signs maps a covariant behaviour with non-constant link laws to a non-covariant one, which
    cannot approach p_DKZ.
  - A deterministic non-bijective post-processing produces an outcome of probability 0, hence I < I_ME strictly.
  - Compactness gives ε. ∎

**Numerics** (`lead1_hull.py`).
- The Jacobian of the 36-parameter chart at DKZ_3 has rank 9 (random strategies: 16). Its image is 3 covariant
  directions plus 6 non-covariant ones.
- A linear-programming radial test against 134,673 generators puts p(sz) outside the hull along the transverse directions,
  for every s tested from 1e-3 to 0.4.

## Files and commands

Run from this folder with `OMP_NUM_THREADS=1`. The scripts need python-flint, mpmath, numpy, scipy and sympy, and cvxpy
for `jm_relax.py`.

| Command | What it does | Log |
|---|---|---|
| `python GLOBAL_fam3_exact.py` | the copies, exactly | `logs/GLOBAL_fam3_exact.log` |
| `python GLOBAL_fam3BB.py run` | Theorem F3: branch-and-bound, writes `GLOBAL_fam3BB_cert.npz` | `logs/GLOBAL_fam3BB_run3.log` |
| `python GLOBAL_fam3COR.py run 0 2`, `python GLOBAL_fam3COR.py run 1 2` | Theorem F3′: the two halves, write `GLOBAL_fam3COR_cert_part*of2.npz` | `logs/GLOBAL_fam3COR_run5_part0.log`, `..._part1.log` |
| `python GLOBAL_fam3_recheck.py uni`, `python GLOBAL_fam3_recheck.py cor` | re-check of the certificates (20 s and 3 min) | `logs/GLOBAL_fam3_recheck_uni.log`, `logs/GLOBAL_fam3_recheck_cor.log` |
| `python GLOBAL_fam3_cube_ivcheck.py`, `python GLOBAL_fam3COR_cube_ivcheck.py` | the local cubes, mpmath intervals | `logs/GLOBAL_fam3_cube_ivcheck.log`, `logs/GLOBAL_fam3COR_cube_ivcheck.log` |
| `python GLOBAL_fam3_sep_ivcheck.py uni 400`, `... cor 400` | 400 random separable-bound boxes, mpmath intervals | `logs/GLOBAL_fam3_sep_ivcheck_uni.log`, `..._cor.log` |
| `python GLOBAL_lemmaR_test.py` | Lemma R at DKZ_3 (numerical) | `logs/GLOBAL_lemmaR_test.log` |
| `python lead1_hull.py`, `python jm_relax.py` | Proposition H and Lemma JM numerics (`c3core.py` is their helper) | `logs/lead1_hull.log`, `logs/jm_relax_dkz.log` |

**Other logs.**
- `GLOBAL_fam3BB_run.log` and `GLOBAL_fam3BB_run2.log` were stopped by hand. The first used a bound that was too weak;
  the second was restarted only to write the certificate.
- The S^COR runs 1–4 were stopped by hand and superseded by run 5, which uses exact minimax weights and the
  equal-gradient slope.
- `GLOBAL_fam3_recheck.log` is an earlier re-check of the S^UNI certificate.
- None of these superseded runs is used in the proof.
- In `jm_relax_dkz.log`, local file paths in solver warnings were shortened.
