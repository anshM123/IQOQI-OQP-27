import CGLMPRigidity.Rigidity

/-!
# From support polynomials to the rigidity hypotheses (Proposition 2.5 of `RIGIDITY.md`)

* `CGLMPRigidity.eq_of_modes`: if the three nontrivial `ℤ/4`-Fourier modes (chain modes) of a family
  `(ℓ₀, ℓ₁, ℓ₂, ℓ₃)` vanish, all four entries are equal (equal links `(E_n)`).
* `CGLMPRigidity.two_valued_iff_linear`: for a unitary `X`, `(X - 1)(X - i) = 0` is equivalent to the
  linear relation `X⋆ - (1 - i) - i X = 0`.
* `CGLMPRigidity.V_eq`: the first-link element `V_n = U⋆ - (1 - i) zⁿ - i z²ⁿ U` equals
  `zⁿ (X⋆ - (1 - i) - i X)` for `X = zⁿ U`; hence `V_n = 0` iff `(X - 1)(X - i) = 0`.
-/

namespace CGLMPRigidity

open Complex

/-- Proposition 2.5(a). -/
theorem eq_of_modes {M : Type*} [AddCommGroup M] [Module ℂ M] {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : M}
    (h₁ : ℓ₀ + (-I) • ℓ₁ + (-1 : ℂ) • ℓ₂ + I • ℓ₃ = 0)
    (h₂ : ℓ₀ + (-1 : ℂ) • ℓ₁ + ℓ₂ + (-1 : ℂ) • ℓ₃ = 0)
    (h₃ : ℓ₀ + I • ℓ₁ + (-1 : ℂ) • ℓ₂ + (-I) • ℓ₃ = 0) :
    ℓ₀ = ℓ₁ ∧ ℓ₁ = ℓ₂ ∧ ℓ₂ = ℓ₃ := by
  have k₁ : (4 : ℂ) • (ℓ₀ - ℓ₁) = 0 := by
    linear_combination (norm := skip) (1 - I) • h₁ + (2 : ℂ) • h₂ + (1 + I) • h₃
    match_scalars <;> cring
  have k₂ : (4 : ℂ) • (ℓ₁ - ℓ₂) = 0 := by
    linear_combination (norm := skip) (1 + I) • h₁ + (-2 : ℂ) • h₂ + (1 - I) • h₃
    match_scalars <;> cring
  have k₃ : (4 : ℂ) • (ℓ₂ - ℓ₃) = 0 := by
    linear_combination (norm := skip) (-1 + I) • h₁ + (2 : ℂ) • h₂ + (-1 - I) • h₃
    match_scalars <;> cring
  have cancel : ∀ x : M, (4 : ℂ) • x = 0 → x = 0 := by
    intro x hx
    have h := congrArg (fun y => (4 : ℂ)⁻¹ • y) hx
    simp only [smul_smul, smul_zero] at h
    rwa [inv_mul_cancel₀ (by norm_num : (4 : ℂ) ≠ 0), one_smul] at h
  exact ⟨sub_eq_zero.1 (cancel _ k₁), sub_eq_zero.1 (cancel _ k₂), sub_eq_zero.1 (cancel _ k₃)⟩

section Algebra

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- For a unitary `X`, the two-eigenvalue relation is equivalent to a linear relation. -/
theorem two_valued_iff_linear {X : A} (hX : IsU X) :
    (X - 1) * (X - I • 1) = 0 ↔ star X - (1 - I) • (1 : A) - I • X = 0 := by
  constructor
  · intro h
    have hii := two_valued_ii hX h
    linear_combination (norm := skip) (-I) • hii
    match_scalars <;> cring
  · intro h
    -- multiply the linear relation by `i X` on the left
    have h1 : (I • X) * (star X - (1 - I) • (1 : A) - I • X) = 0 := by rw [h, mul_zero]
    have e : (I • X) * (star X - (1 - I) • (1 : A) - I • X)
        = I • (1 : A) - (I * (1 - I)) • X - (I * I) • (X * X) := by
      simp only [mul_sub, smul_mul_assoc, mul_smul_comm, hX.2, mul_one, smul_smul]
      module
    have e2 : (X - 1) * (X - I • 1) = X * X - (1 + I) • X + I • (1 : A) := by
      simp only [mul_sub, sub_mul, mul_smul_comm, mul_one, one_mul]
      module
    rw [e] at h1
    rw [e2]
    linear_combination (norm := skip) h1
    match_scalars <;> cring

/-- The first-link element `V_n` in terms of `X = zⁿ U`. -/
theorem V_eq {U : A} {z : ℂ} (hz : star z * z = 1) (n : ℕ) :
    star U - ((1 - I) * z ^ n) • (1 : A) - (I * z ^ (2 * n)) • U
      = z ^ n • (star (z ^ n • U) - (1 - I) • (1 : A) - I • (z ^ n • U)) := by
  have hzn : z ^ n * star z ^ n = 1 := by rw [← mul_pow, mul_comm, hz, one_pow]
  rw [star_smul, star_pow]
  simp only [smul_sub, smul_smul, hzn, one_smul]
  module

/-- **Rigidity from the support conditions (C2).** If the three nontrivial chain modes of the
`n = 1` links vanish and the first-link elements `V_n` vanish for `1 ≤ n ≤ d / 2 + 1` (which is what
Proposition 2.4 gives for an optimal strategy when these polynomials lie in the support of the SOS
certificate), then the strategy is in canonical DKZ form (conclusion of `rigidity`). Here
`w⁻¹ = z⋆ ^ 4` and the fourth link is `w⁻¹ R₄ R₁⋆`. -/
theorem rigidity_of_support (hC : ∀ x : A, star x * x = 0 → x = 0)
    {d : ℕ} {z : ℂ} (hz : star z * z = 1) (hzd : z ^ d = I)
    {R₁ R₂ R₃ R₄ : A} (hR₁ : IsU R₁) (hR₂ : IsU R₂) (hR₃ : IsU R₃)
    (hp₁ : R₁ ^ d = 1) (hp₂ : R₂ ^ d = 1)
    (hM₁ : R₁ * star R₂ + (-I) • (R₂ * star R₃) + (-1 : ℂ) • (R₃ * star R₄)
        + I • (star z ^ 4 • (R₄ * star R₁)) = 0)
    (hM₂ : R₁ * star R₂ + (-1 : ℂ) • (R₂ * star R₃) + R₃ * star R₄
        + (-1 : ℂ) • (star z ^ 4 • (R₄ * star R₁)) = 0)
    (hM₃ : R₁ * star R₂ + I • (R₂ * star R₃) + (-1 : ℂ) • (R₃ * star R₄)
        + (-I) • (star z ^ 4 • (R₄ * star R₁)) = 0)
    (hV : ∀ n, 1 ≤ n → n ≤ d / 2 + 1 →
      star (R₁ ^ n * star R₂ ^ n) - ((1 - I) * z ^ n) • (1 : A)
        - (I * z ^ (2 * n)) • (R₁ ^ n * star R₂ ^ n) = 0) :
    ∃ p : A, IsStarProjection p ∧
      R₂ = z • ((1 - (1 + I) • p) * R₁) ∧ R₃ = z • ((1 - (1 + I) • p) * R₂) ∧
      R₄ = z • ((1 - (1 + I) • p) * R₃) ∧
      (∀ j k l m, k < d → l < d →
        mu R₁ p j k * mu R₁ p l m = if k = l then mu R₁ p j m else 0) ∧
      (∀ j k, star (mu R₁ p j k) = mu R₁ p k j) ∧
      (∑ j ∈ Finset.range d, mu R₁ p j j = 1) ∧
      R₁ = ∑ j ∈ Finset.range d, mu R₁ p ((j + 1) % d) j := by
  obtain ⟨h01, h12, -⟩ := eq_of_modes hM₁ hM₂ hM₃
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    simp at hz
  have hT : ∀ n, 1 ≤ n → n ≤ d / 2 + 1 →
      (z ^ n • (R₁ ^ n * star R₂ ^ n) - 1) * (z ^ n • (R₁ ^ n * star R₂ ^ n) - I • 1) = 0 := by
    intro n h1 h2
    have hU : IsU (R₁ ^ n * star R₂ ^ n) :=
      (hR₁.pow n).mul (by rw [← star_pow]; exact (hR₂.pow n).star')
    have hX : IsU (z ^ n • (R₁ ^ n * star R₂ ^ n)) :=
      hU.smul (by rw [star_pow, ← mul_pow, hz, one_pow])
    rw [two_valued_iff_linear hX]
    have hv := hV n h1 h2
    rw [V_eq hz n] at hv
    rcases smul_eq_zero.1 hv with h0 | h0
    · exact absurd h0 (pow_ne_zero n hz0)
    · exact h0
  exact rigidity hC hz hzd hR₁ hR₂ hR₃ hp₁ hp₂ h01 h12 hT

end Algebra

end CGLMPRigidity
