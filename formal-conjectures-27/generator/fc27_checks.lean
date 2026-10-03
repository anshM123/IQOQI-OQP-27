/- ### Basic facts and sanity checks for the definitions of Part 0 -/

namespace OpenQuantumProblem27

open Matrix
open scoped Kronecker

section ProblemChecks

/-- The maximally entangled state is a unit vector. -/
@[category test, AMS 15 81]
theorem norm_maxEntangledState (D : ℕ) [NeZero D] : ‖maxEntangledState D‖ = 1 := by
  have hD : (0 : ℝ) < D := Nat.cast_pos.2 (NeZero.pos D)
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type]
  have h : ∀ i : Fin D, ∑ j : Fin D, ‖(maxEntangledState D) (i, j)‖ ^ 2 = (D : ℝ)⁻¹ := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [maxEntangledState, Ne.symm hji])
      (by simp)]
    simp [maxEntangledState, norm_inv, Real.sq_sqrt hD.le]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- $\operatorname{Tr}(|u\rangle\langle v| M) = \langle v| M |u\rangle$. -/
@[category API, AMS 15 81]
theorem trace_vecMulVec_mul {n : Type*} [Fintype n] (u v : n → ℂ) (M : Matrix n n ℂ) :
    (vecMulVec u v * M).trace = v ⬝ᵥ (M *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, vecMulVec_apply, dotProduct, mulVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The Born rule on the maximally entangled state**:
$\operatorname{Tr}[|\Phi_D\rangle\langle\Phi_D| (A \otimes B)] = \operatorname{Tr}(A^{T} B) / D$. -/
@[category API, AMS 15 81]
theorem bornProb_maxEntangledState {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    bornProb (densityMatrix (maxEntangledState D)) A B = (Aᵀ * B).trace.re / D := by
  set c : ℂ := ((Real.sqrt D : ℝ) : ℂ)⁻¹ with hc
  have hcc : c * star c = ((D : ℝ) : ℂ)⁻¹ := by
    rw [hc, star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg D)]
  set φ : Fin D × Fin D → ℂ := fun ij => if ij.1 = ij.2 then c else 0 with hφ
  have hφ' : WithLp.ofLp (maxEntangledState D) = φ := rfl
  have hrow : ∀ i : Fin D, ((A ⊗ₖ B) *ᵥ φ) (i, i) = ∑ k, A i k * B i k * c := by
    intro i
    simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, hφ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hlk => by simp [Ne.symm hlk]) (by simp)]
    simp
  have hdiag : ∀ i : Fin D, ∑ j : Fin D, ((A ⊗ₖ B) *ᵥ φ) (i, j) * star (φ (i, j)) =
      ((A ⊗ₖ B) *ᵥ φ) (i, i) * star c := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [hφ, Ne.symm hji]) (by simp)]
    simp [hφ]
  have htr : (Aᵀ * B).trace = ∑ i : Fin D, ∑ k : Fin D, A i k * B i k := by
    rw [Matrix.trace, Finset.sum_comm]
    simp [Matrix.diag, mul_apply, transpose_apply]
  have key : ((A ⊗ₖ B) *ᵥ φ) ⬝ᵥ star φ = ((D : ℝ) : ℂ)⁻¹ * (Aᵀ * B).trace := by
    rw [dotProduct, Fintype.sum_prod_type]
    simp only [Pi.star_apply]
    rw [Finset.sum_congr rfl fun i _ => hdiag i, htr, ← hcc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow i, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [bornProb, densityMatrix, hφ', trace_vecMulVec_mul, dotProduct_comm, key,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul, inv_mul_eq_div]

/- #### Complete von Neumann measurements -/

@[category API, AMS 15 81]
theorem vonNeumannMeasurement_apply {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (a i j : Fin d) :
    vonNeumannMeasurement U a i j = U i a * star (U j a) := by
  rw [vonNeumannMeasurement, mul_apply, Finset.sum_eq_single a]
  · simp [conjTranspose_apply]
  · intro l _ hla
    simp [hla]
  · simp

/-- The projection $U |a\rangle\langle a| U^{\dagger}$ is $|u_a\rangle\langle u_a|$ for the column
$u_a$ of `U`. -/
@[category API, AMS 15 81]
theorem vonNeumannMeasurement_eq_vecMulVec {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (a : Fin d) :
    vonNeumannMeasurement U a = vecMulVec (fun j => U j a) (star fun j => U j a) := by
  ext i j
  rw [vonNeumannMeasurement_apply, vecMulVec_apply]
  rfl

@[category API, AMS 15 81]
lemma unitary_conjTranspose_mul {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : Uᴴ * U = 1 := by
  have h := mem_unitaryGroup_iff'.1 hU
  rwa [star_eq_conjTranspose] at h

@[category API, AMS 15 81]
lemma unitary_mul_conjTranspose {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : U * Uᴴ = 1 := by
  have h := mem_unitaryGroup_iff.1 hU
  rwa [star_eq_conjTranspose] at h

@[category API, AMS 15 81]
lemma sum_single_self_one (d : ℕ) : ∑ a : Fin d, single a a (1 : ℂ) = 1 := by
  ext i j
  rw [Matrix.sum_apply, Finset.sum_eq_single i]
  · by_cases hij : i = j <;> simp [one_apply, hij]
  · intro b _ hbi
    simp [hbi]
  · simp

/-- A complete von Neumann measurement is a projective measurement. -/
@[category test, AMS 15 81]
theorem isProjectiveMeasurement_vonNeumannMeasurement {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : IsProjectiveMeasurement (vonNeumannMeasurement U) := by
  have h1 := unitary_conjTranspose_mul hU
  have h2 := unitary_mul_conjTranspose hU
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · unfold vonNeumannMeasurement
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_single, star_one, Matrix.mul_assoc]
  · unfold vonNeumannMeasurement
    calc U * single a a 1 * Uᴴ * (U * single a a 1 * Uᴴ)
        = U * (single a a 1 * (Uᴴ * U) * single a a 1) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * single a a 1 * Uᴴ := by
          rw [h1, Matrix.mul_one, single_mul_single_same, mul_one, Matrix.mul_assoc]
  · unfold vonNeumannMeasurement
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_self_one, Matrix.mul_one, h2]

/-- The projections of a complete von Neumann measurement have rank one (trace $1$). -/
@[category test, AMS 15 81]
theorem trace_vonNeumannMeasurement {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) (a : Fin d) : (vonNeumannMeasurement U a).trace = 1 := by
  rw [vonNeumannMeasurement, trace_mul_comm, ← Matrix.mul_assoc, unitary_conjTranspose_mul hU,
    Matrix.one_mul, trace_single_eq_same]

/- #### The local unitaries that fix $\Phi_d$ -/

/-- $(u \otimes v) \Phi_d$ has the coordinates of $d^{-1/2} \, u v^{T}$. -/
@[category API, AMS 15 81]
theorem kronecker_mulVec_maxEntangledState_apply {d : ℕ} (u v : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    ((u ⊗ₖ v) *ᵥ WithLp.ofLp (maxEntangledState d)) (i, j) =
      ((Real.sqrt d : ℝ) : ℂ)⁻¹ * (u * vᵀ) i j := by
  simp only [maxEntangledState, mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_apply, transpose_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The local unitaries that leave $\Phi_d$ invariant** are the $u \otimes \bar u$: for a unitary
`u` and any matrix `v`, $(u \otimes v) \Phi_d = \Phi_d$ if and only if $v = \bar u$. These are the
local unitaries of the uniqueness condition `IsDKZUpToLocalUnitary` (Part 87). -/
@[category test, AMS 15 81]
theorem kronecker_mulVec_maxEntangledState_eq_iff {d : ℕ} [NeZero d]
    (u v : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ unitaryGroup (Fin d) ℂ) :
    (u ⊗ₖ v) *ᵥ WithLp.ofLp (maxEntangledState d) = WithLp.ofLp (maxEntangledState d) ↔
      v = u.map star := by
  have hc : ((Real.sqrt d : ℝ) : ℂ)⁻¹ ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos d)
    exact inv_ne_zero (by exact_mod_cast this.ne')
  have h1 := unitary_mul_conjTranspose hu
  have h2 := unitary_conjTranspose_mul hu
  -- `(u ⊗ v) Φ = Φ` says exactly `u * vᵀ = 1`
  have key : (u ⊗ₖ v) *ᵥ WithLp.ofLp (maxEntangledState d) = WithLp.ofLp (maxEntangledState d) ↔
      u * vᵀ = 1 := by
    constructor
    · intro h
      ext i j
      have e := congrFun h (i, j)
      rw [kronecker_mulVec_maxEntangledState_apply] at e
      simp only [maxEntangledState] at e
      rw [one_apply]
      split_ifs at e ⊢ with hij
      · exact mul_left_cancel₀ hc (e.trans (mul_one _).symm)
      · exact (mul_eq_zero.1 e).resolve_left hc
    · intro h
      funext ⟨i, j⟩
      rw [kronecker_mulVec_maxEntangledState_apply, h, one_apply]
      simp only [maxEntangledState]
      split_ifs <;> simp
  rw [key]
  constructor
  · intro h
    have hvT : vᵀ = uᴴ := by
      calc vᵀ = (uᴴ * u) * vᵀ := by rw [h2, Matrix.one_mul]
        _ = uᴴ * (u * vᵀ) := Matrix.mul_assoc _ _ _
        _ = uᴴ := by rw [h, Matrix.mul_one]
    rw [← transpose_transpose v, hvT]
    ext i j
    rfl
  · intro h
    have hT : (u.map star)ᵀ = uᴴ := by
      ext i j
      rfl
    rw [h, hT, h1]

/- #### The CGLMP inequality: local models give at least $d - 1$ -/

@[category API, AMS 15 81]
lemma sum_sum_deterministicBehaviour_mul {d : ℕ} (f g : Fin 2 → Fin d) (x y : Fin 2)
    (F : Fin d → Fin d → ℝ) :
    ∑ a : Fin d, ∑ b : Fin d, deterministicBehaviour f g x y a b * F a b = F (f x) (g y) := by
  simp only [deterministicBehaviour, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (f x), Finset.sum_eq_single (g y)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [ha]
  · simp

/-- The value of the CGLMP functional for a deterministic strategy. -/
@[category API, AMS 15 81]
theorem cglmpFunctional_deterministicBehaviour {d : ℕ} (f g : Fin 2 → Fin d) :
    cglmpFunctional (deterministicBehaviour f g) =
      ((((f 0 : ℕ) - (g 0 : ℕ) : ℤ) % d : ℤ) : ℝ) + ((((g 0 : ℕ) - (f 1 : ℕ) : ℤ) % d : ℤ) : ℝ) +
        ((((f 1 : ℕ) - (g 1 : ℕ) : ℤ) % d : ℤ) : ℝ) +
        ((((g 1 : ℕ) - (f 0 : ℕ) - 1 : ℤ) % d : ℤ) : ℝ) := by
  simp only [cglmpFunctional, Finset.sum_add_distrib]
  rw [sum_sum_deterministicBehaviour_mul f g 0 0 (fun a b => ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ)),
    sum_sum_deterministicBehaviour_mul f g 1 0 (fun a b => ((((b : ℕ) - (a : ℕ) : ℤ) % d : ℤ) : ℝ)),
    sum_sum_deterministicBehaviour_mul f g 1 1 (fun a b => ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ)),
    sum_sum_deterministicBehaviour_mul f g 0 1
      (fun a b => ((((b : ℕ) - (a : ℕ) - 1 : ℤ) % d : ℤ) : ℝ))]

/-- **The CGLMP inequality for deterministic strategies**: the functional is at least $d - 1$. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_deterministicBehaviour_ge {d : ℕ} [NeZero d] (f g : Fin 2 → Fin d) :
    (d : ℝ) - 1 ≤ cglmpFunctional (deterministicBehaviour f g) := by
  rw [cglmpFunctional_deterministicBehaviour]
  have hd : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  set t₁ : ℤ := ((f 0 : ℕ) - (g 0 : ℕ) : ℤ)
  set t₂ : ℤ := ((g 0 : ℕ) - (f 1 : ℕ) : ℤ)
  set t₃ : ℤ := ((f 1 : ℕ) - (g 1 : ℕ) : ℤ)
  set t₄ : ℤ := ((g 1 : ℕ) - (f 0 : ℕ) - 1 : ℤ)
  have hsum : t₁ + t₂ + t₃ + t₄ = -1 := by ring
  have e₁ := Int.mul_ediv_add_emod t₁ d
  have e₂ := Int.mul_ediv_add_emod t₂ d
  have e₃ := Int.mul_ediv_add_emod t₃ d
  have e₄ := Int.mul_ediv_add_emod t₄ d
  have n₁ := Int.emod_nonneg t₁ hd.ne'
  have n₂ := Int.emod_nonneg t₂ hd.ne'
  have n₃ := Int.emod_nonneg t₃ hd.ne'
  have n₄ := Int.emod_nonneg t₄ hd.ne'
  set Q : ℤ := t₁ / d + t₂ / d + t₃ / d + t₄ / d with hQ
  have hS : t₁ % d + t₂ % d + t₃ % d + t₄ % d = -1 - d * Q := by
    rw [hQ]
    linear_combination e₁ + e₂ + e₃ + e₄ + hsum
  have hQneg : Q ≤ -1 := by
    rcases le_or_gt Q (-1) with h | h
    · exact h
    · have : 0 ≤ (d : ℤ) * Q := mul_nonneg hd.le (by omega)
      linarith
  have hdQ : (d : ℤ) * Q ≤ -(d : ℤ) := by nlinarith
  have hZ : (d : ℤ) - 1 ≤ t₁ % d + t₂ % d + t₃ % d + t₄ % d := by linarith
  have hR : (((d : ℤ) - 1 : ℤ) : ℝ) ≤ ((t₁ % d + t₂ % d + t₃ % d + t₄ % d : ℤ) : ℝ) := by
    exact_mod_cast hZ
  push_cast at hR
  exact hR

/-- The local bound $d - 1$ is attained, by the strategy in which both parties always output `0`. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_deterministicBehaviour_zero {d : ℕ} [NeZero d] :
    cglmpFunctional (deterministicBehaviour (d := d) (fun _ => 0) (fun _ => 0)) = (d : ℝ) - 1 := by
  rw [cglmpFunctional_deterministicBehaviour]
  have hd : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  have hm : ((-1 : ℤ) % d) = d - 1 :=
    ((Int.ediv_emod_unique (q := -1) (r := (d : ℤ) - 1) hd).2 ⟨by ring, by omega, by omega⟩).2
  simp only [Fin.val_zero, Nat.cast_zero, sub_self, Int.zero_emod, Int.cast_zero, zero_add,
    zero_sub, hm]
  push_cast
  ring

@[category API, AMS 15 81]
lemma sum_four_linear {d : ℕ} {ι : Type*} (S : Finset ι) (q : ι → ℝ) (P : ι → Behaviour d)
    (c₁ c₂ c₃ c₄ : Fin d → Fin d → ℝ) :
    ∑ a : Fin d, ∑ b : Fin d, ((∑ i ∈ S, q i * P i 0 0 a b) * c₁ a b +
      (∑ i ∈ S, q i * P i 1 0 a b) * c₂ a b + (∑ i ∈ S, q i * P i 1 1 a b) * c₃ a b +
      (∑ i ∈ S, q i * P i 0 1 a b) * c₄ a b) =
    ∑ i ∈ S, q i * ∑ a : Fin d, ∑ b : Fin d, (P i 0 0 a b * c₁ a b + P i 1 0 a b * c₂ a b +
      P i 1 1 a b * c₃ a b + P i 0 1 a b * c₄ a b) := by
  have inner : ∀ a b : Fin d, (∑ i ∈ S, q i * P i 0 0 a b) * c₁ a b +
      (∑ i ∈ S, q i * P i 1 0 a b) * c₂ a b + (∑ i ∈ S, q i * P i 1 1 a b) * c₃ a b +
      (∑ i ∈ S, q i * P i 0 1 a b) * c₄ a b =
      ∑ i ∈ S, q i * (P i 0 0 a b * c₁ a b + P i 1 0 a b * c₂ a b + P i 1 1 a b * c₃ a b +
        P i 0 1 a b * c₄ a b) := by
    intro a b
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [inner]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- **The CGLMP inequality**: every local model gives at least $d - 1$. -/
@[category test, AMS 15 81]
theorem le_cglmpFunctional_of_isLocalBehaviour {d : ℕ} [NeZero d] {p : Behaviour d}
    (hp : IsLocalBehaviour p) : (d : ℝ) - 1 ≤ cglmpFunctional p := by
  obtain ⟨q, hq0, hq1, hpq⟩ := hp
  have hp' : p = fun x y a b => ∑ s, q s * deterministicBehaviour s.1 s.2 x y a b := by
    funext x y a b
    exact hpq x y a b
  have hlin : cglmpFunctional p = ∑ s, q s * cglmpFunctional (deterministicBehaviour s.1 s.2) := by
    rw [hp']
    exact sum_four_linear Finset.univ q (fun s => deterministicBehaviour s.1 s.2) _ _ _ _
  rw [hlin]
  calc (d : ℝ) - 1 = ∑ s, q s * ((d : ℝ) - 1) := by rw [← Finset.sum_mul, hq1, one_mul]
    _ ≤ ∑ s, q s * cglmpFunctional (deterministicBehaviour s.1 s.2) :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (cglmpFunctional_deterministicBehaviour_ge s.1 s.2) (hq0 s)

/- #### Measuring in the computational basis does not violate the CGLMP inequality -/

/-- On the maximally entangled state, measuring both systems in the computational basis gives
perfectly correlated, uniformly random outputs. -/
@[category test, AMS 15 81]
theorem bornProb_maxEntangledState_single {D : ℕ} (a b : Fin D) :
    bornProb (densityMatrix (maxEntangledState D)) (single a a 1) (single b b 1) =
      if a = b then 1 / (D : ℝ) else 0 := by
  rw [bornProb_maxEntangledState, transpose_single]
  by_cases h : a = b
  · subst h
    rw [single_mul_single_same, trace_single_eq_same, if_pos rfl]
    simp
  · rw [if_neg h]
    simp [h]

@[category API, AMS 15 81]
lemma vonNeumannMeasurement_one {d : ℕ} (a : Fin d) : vonNeumannMeasurement 1 a = single a a 1 := by
  simp [vonNeumannMeasurement]

/-- On $\Phi_d$, measuring both systems in the computational basis for both inputs gives exactly
the local bound $d - 1$: there is no violation without the Fourier-phase bases. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_computationalBasis {d : ℕ} [NeZero d] :
    cglmpFunctional (vonNeumannBehaviour d (fun _ => 1) (fun _ => 1)) = (d : ℝ) - 1 := by
  have hd : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hp : ∀ x y : Fin 2, ∀ a b : Fin d,
      vonNeumannBehaviour d (fun _ => 1) (fun _ => 1) x y a b = if a = b then 1 / (d : ℝ) else 0 := by
    intro x y a b
    simp only [vonNeumannBehaviour, quantumBehaviour, vonNeumannMeasurement_one]
    exact bornProb_maxEntangledState_single a b
  have hm : ((((0 : ℤ) - 1) % d : ℤ)) = d - 1 :=
    ((Int.ediv_emod_unique (q := -1) (r := (d : ℤ) - 1) hd).2 ⟨by ring, by omega, by omega⟩).2
  simp only [cglmpFunctional, hp]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_eq_single a (fun b _ hba => by simp [Ne.symm hba])
    (by simp)]
  simp only [if_true, sub_self, Int.zero_emod, Int.cast_zero, mul_zero, zero_add, add_zero, hm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/- #### The CGLMP expression of Collins et al. and the functional of the OQP page -/

/-- The weight of a difference `r` of outputs in `cglmpExpr`:
$W(r) = \sum_{k < \lfloor d/2 \rfloor} (1 - \frac{2k}{d-1})([r = k] - [r = -k-1])$. -/
noncomputable def cglmpWeight (d : ℕ) (r : ZMod d) : ℝ :=
  ∑ k ∈ Finset.range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
    ((if r = ((k : ℤ) : ZMod d) then 1 else 0) - (if r = ((-(k : ℤ) - 1 : ℤ) : ZMod d) then 1 else 0))

/-- $W(r) = 1 - \frac{2 r}{d - 1}$ for the representative $r \in \{0, \dots, d-1\}$. -/
@[category API, AMS 15 81]
theorem cglmpWeight_eq {d : ℕ} (hd : 2 ≤ d) (r : ZMod d) :
    cglmpWeight d r = 1 - 2 * (r.val : ℝ) / ((d : ℝ) - 1) := by
  have : NeZero d := ⟨by omega⟩
  set n := r.val with hn
  have hnd : n < d := ZMod.val_lt r
  have hr : r = ((n : ℕ) : ZMod d) := (ZMod.natCast_zmod_val r).symm
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : ∀ k ∈ Finset.range (d / 2), (r = ((k : ℤ) : ZMod d)) ↔ n = k := by
    intro k hk
    have hk' : k < d := by rw [Finset.mem_range] at hk; omega
    rw [hr, Int.cast_natCast, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hnd,
      Nat.mod_eq_of_lt hk']
  have h2 : ∀ k ∈ Finset.range (d / 2), (r = ((-(k : ℤ) - 1 : ℤ) : ZMod d)) ↔ n = d - 1 - k := by
    intro k hk
    have hk' : k < d := by rw [Finset.mem_range] at hk; omega
    have hcast : ((-(k : ℤ) - 1 : ℤ) : ZMod d) = ((d - 1 - k : ℕ) : ZMod d) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
      push_cast
      ring
    rw [hcast, hr, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hnd,
      Nat.mod_eq_of_lt (by omega : d - 1 - k < d)]
  have hW : cglmpWeight d r = ∑ k ∈ Finset.range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
      ((if n = k then 1 else 0) - (if k = d - 1 - n then 1 else 0)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    congr 2
    · exact if_congr (h1 k hk) rfl rfl
    · refine if_congr ?_ rfl rfl
      rw [h2 k hk]
      have : k < d := by rw [Finset.mem_range] at hk; omega
      omega
  rw [hW]
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_range]
  by_cases hA : n < d / 2
  · have hB : ¬ d - 1 - n < d / 2 := by omega
    rw [if_pos hA, if_neg hB, sub_zero]
  · by_cases hB : d - 1 - n < d / 2
    · rw [if_neg hA, if_pos hB, zero_sub]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      field_simp
      push_cast
      ring
    · rw [if_neg hA, if_neg hB, sub_zero]
      have hn2 : 2 * n = d - 1 := by omega
      have hn2' : (2 : ℝ) * n = (d : ℝ) - 1 := by
        rw [← Nat.cast_ofNat, ← Nat.cast_mul, hn2, Nat.cast_sub (by omega), Nat.cast_one]
      field_simp
      linarith

/-- One link of `cglmpExpr`: the weighted differences of the probabilities that a difference
`L a b` of outputs takes the values `k` and `-k-1` add up to the expectation of $W(L)$. -/
@[category API, AMS 15 81]
lemma sum_weight_link {d : ℕ} (P : Fin d → Fin d → ℝ) (L : Fin d → Fin d → ZMod d) :
    ∑ k ∈ Finset.range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
      ((∑ a : Fin d, ∑ b : Fin d, if L a b = ((k : ℤ) : ZMod d) then P a b else 0) -
        ∑ a : Fin d, ∑ b : Fin d, if L a b = ((-(k : ℤ) - 1 : ℤ) : ZMod d) then P a b else 0) =
    ∑ a : Fin d, ∑ b : Fin d, P a b * cglmpWeight d (L a b) := by
  simp only [cglmpWeight, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- **The two forms of the CGLMP functional agree**: for every behaviour `p` in which each
$p(\cdot,\cdot \mid x,y)$ is a probability distribution, the CGLMP expression of Collins et al. is
$I_d(p) = 4 - \frac{2}{d-1} F(p')$, where $F$ is the functional of the OQP page and $p'$ is `p`
with the two inputs exchanged. In particular $I_d(p) \le 2$ if and only if $F(p') \ge d - 1$. -/
@[category API, AMS 15 81]
theorem cglmpExpr_eq_cglmpFunctional {d : ℕ} (hd : 2 ≤ d) (p : Behaviour d)
    (hp : ∀ x y, ∑ a, ∑ b, p x y a b = 1) :
    cglmpExpr p = 4 - 2 * cglmpFunctional (swapInputs p) / ((d : ℝ) - 1) := by
  have : NeZero d := ⟨by omega⟩
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- the eight probabilities as indicator sums of the four links
  have e : ∀ u v w : ZMod d, (u = v + w) ↔ (u - v = w) := fun u v w => by
    constructor <;> intro h <;> linear_combination h
  have pA : ∀ (x y : Fin 2) (k : ℤ), probAEqBAdd p x y k = ∑ a : Fin d, ∑ b : Fin d,
      if ((a : ℕ) : ZMod d) - ((b : ℕ) : ZMod d) = (k : ZMod d) then p x y a b else 0 := by
    intro x y k
    unfold probAEqBAdd
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => if_congr (e _ _ _) rfl rfl
  have pB : ∀ (x y : Fin 2) (k : ℤ), probBEqAAdd p x y k = ∑ a : Fin d, ∑ b : Fin d,
      if ((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d) = (k : ZMod d) then p x y a b else 0 := by
    intro x y k
    unfold probBEqAAdd
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => if_congr (e _ _ _) rfl rfl
  have pB' : ∀ (x y : Fin 2) (k : ℤ), probBEqAAdd p x y (k + 1) = ∑ a : Fin d, ∑ b : Fin d,
      if ((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d) - 1 = (k : ZMod d) then p x y a b else 0 := by
    intro x y k
    unfold probBEqAAdd
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => if_congr ?_ rfl rfl
    push_cast
    constructor <;> intro h <;> linear_combination h
  have pB'' : ∀ (x y : Fin 2) (k : ℤ), probBEqAAdd p x y (-k) = ∑ a : Fin d, ∑ b : Fin d,
      if ((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d) - 1 = ((-k - 1 : ℤ) : ZMod d) then p x y a b
        else 0 := by
    intro x y k
    unfold probBEqAAdd
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => if_congr ?_ rfl rfl
    push_cast
    constructor <;> intro h <;> linear_combination h
  -- the expression as the expectation of the weights of the four links
  have hI : cglmpExpr p = ∑ a, ∑ b,
      (p 0 0 a b * cglmpWeight d (((a : ℕ) : ZMod d) - ((b : ℕ) : ZMod d)) +
        p 1 0 a b * cglmpWeight d (((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d) - 1) +
        p 1 1 a b * cglmpWeight d (((a : ℕ) : ZMod d) - ((b : ℕ) : ZMod d)) +
        p 0 1 a b * cglmpWeight d (((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d))) := by
    have l1 := sum_weight_link (p 0 0) fun a b => ((a : ℕ) : ZMod d) - ((b : ℕ) : ZMod d)
    have l2 := sum_weight_link (p 1 0) fun a b => ((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d) - 1
    have l3 := sum_weight_link (p 1 1) fun a b => ((a : ℕ) : ZMod d) - ((b : ℕ) : ZMod d)
    have l4 := sum_weight_link (p 0 1) fun a b => ((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d)
    simp only [Finset.sum_add_distrib]
    rw [← l1, ← l2, ← l3, ← l4, cglmpExpr]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pA 0 0 k, pB' 1 0 k, pA 1 1 k, pB 0 1 k, pA 0 0 (-(k : ℤ) - 1), pB'' 1 0 k,
      pA 1 1 (-(k : ℤ) - 1), pB 0 1 (-(k : ℤ) - 1)]
    ring
  -- the weights in terms of `m(t) = t mod d`
  have hval : ∀ t : ℤ, (((t : ZMod d).val : ℕ) : ℝ) = ((t % d : ℤ) : ℝ) := by
    intro t
    rw [← ZMod.val_intCast t]
    push_cast
    rfl
  have w1 : ∀ a b : Fin d, cglmpWeight d (((a : ℕ) : ZMod d) - ((b : ℕ) : ZMod d)) =
      1 - 2 * ((((a : ℕ) - (b : ℕ) : ℤ) % d : ℤ) : ℝ) / ((d : ℝ) - 1) := by
    intro a b
    rw [cglmpWeight_eq hd, ← hval]
    push_cast
    rfl
  have w2 : ∀ a b : Fin d, cglmpWeight d (((b : ℕ) : ZMod d) - ((a : ℕ) : ZMod d) - 1) =
      1 - 2 * ((((b : ℕ) - (a : ℕ) - 1 : ℤ) % d : ℤ) : ℝ) / ((d : ℝ) - 1) := by
    intro a b
    rw [cglmpWeight_eq hd, ← hval]
    push_cast
    rfl
  rw [hI]
  simp only [w1, w2]
  have hsum4 : ∑ a : Fin d, ∑ b : Fin d, (p 0 0 a b + p 1 0 a b + p 1 1 a b + p 0 1 a b) = 4 := by
    simp only [Finset.sum_add_distrib, hp]
    norm_num
  have hd1' : (d : ℝ) - 1 ≠ 0 := hd1.ne'
  have h0 : (0 : Fin 2).rev = 1 := rfl
  have h1 : (1 : Fin 2).rev = 0 := rfl
  simp only [cglmpFunctional, swapInputs, h0, h1]
  rw [← hsum4, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  field_simp
  ring

/- #### The case $d = 2$: Tsirelson's bound -/

/-- For $d = 2$ the DKZ value is Tsirelson's bound: $I_{ME}(2) = 2\sqrt{2}$. -/
@[category test, AMS 15 81]
theorem cglmpMaxEntValue_two : cglmpMaxEntValue 2 = 2 * Real.sqrt 2 := by
  have hI : Finset.Ico 1 2 = {1} := rfl
  have hc : Real.cos (Real.pi * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ))) = Real.sqrt 2 / 2 := by
    rw [show Real.pi * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ)) = Real.pi / 4 by push_cast; ring]
    exact Real.cos_pi_div_four
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  rw [cglmpMaxEntValue, hI, Finset.sum_singleton, hc]
  push_cast
  field_simp
  nlinarith [hs]

end ProblemChecks

end OpenQuantumProblem27
