import Mathlib

/-!
# Algebraic rigidity of the DKZ strategy for CGLMP on maximally entangled states

Machine-checked version of Section 3 of `iqoqi/programs/oqp27B_all/C_rigidity/RIGIDITY.md`
(IQOQI Open Quantum Problem 27B: the optimal CGLMP observables on a maximally entangled state are
necessarily of Durt-Kaszlikowski-Zukowski form).

Setting: `A` is a unital `*`-algebra over `ℂ` in which `star x * x = 0` implies `x = 0`
(every C*-algebra; in particular `Matrix (Fin D) (Fin D) ℂ`). A strategy is a family of
unitaries `R₁ R₂ R₃ R₄` with `R₁ ^ d = R₂ ^ d = 1`, and `z` is a unimodular scalar with `z ^ d = i`
(in the application `z = exp (2 π i / (4 d))`).

Main results:
* `CGLMPRigidity.jordan`: for star projections `P`, `Q`, the product
  `X = (1 + (i - 1) P) (1 + (i - 1) Q)` satisfies `(X - 1) (X - i) = 0` only if `P * Q = 0`.
* `CGLMPRigidity.rigidity`: if the first three links agree, `R₁ R₂⋆ = R₂ R₃⋆ = R₃ R₄⋆`, and the
  two-eigenvalue relations `(z ^ n R₁ ^ n R₂⋆ ^ n - 1) (z ^ n R₁ ^ n R₂⋆ ^ n - i) = 0` hold for
  `1 ≤ n ≤ d / 2 + 1`, then there is a star projection `p` such that
  `R_{k+1} = z (1 - (1 + i) p) R_k` (`k = 1, 2, 3`) and the elements
  `e j k = R₁ ^ j * p * star R₁ ^ k` (`j, k < d`) form a system of `d × d` matrix units with
  `∑ e j j = 1` and `R₁ = ∑ e ((j + 1) % d) j`: the canonical DKZ form.
* `CGLMPRigidity.dvd_of_rigidity`: for `D × D` complex matrices this forces `d ∣ D`.
-/

set_option linter.unusedSectionVars false

namespace CGLMPRigidity

open Complex

/-- Closes identities between polynomial expressions in `Complex.I` with rational coefficients. -/
macro "cring" : tactic => `(tactic| (apply Complex.ext <;> simp <;> ring))

lemma I_sub_one_ne_zero : (I - 1 : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

lemma star_I_sub_one : star (I - 1 : ℂ) = -I - 1 := by
  cring

section Basic

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- `U` is unitary. -/
def IsU (U : A) : Prop := star U * U = 1 ∧ U * star U = 1

lemma IsU.mul {U V : A} (hU : IsU U) (hV : IsU V) : IsU (U * V) := by
  constructor
  · rw [star_mul, mul_assoc, ← mul_assoc (star U), hU.1, one_mul, hV.1]
  · rw [star_mul, mul_assoc, ← mul_assoc V, hV.2, one_mul, hU.2]

lemma IsU.star' {U : A} (hU : IsU U) : IsU (star U) := by
  constructor
  · rw [star_star]; exact hU.2
  · rw [star_star]; exact hU.1

lemma IsU.pow {U : A} (hU : IsU U) : ∀ n : ℕ, IsU (U ^ n)
  | 0 => by simp [IsU]
  | n + 1 => by rw [pow_succ]; exact (hU.pow n).mul hU

lemma IsU.smul {U : A} (hU : IsU U) {c : ℂ} (hc : star c * c = 1) : IsU (c • U) := by
  have hc' : c * star c = 1 := by rw [mul_comm]; exact hc
  constructor
  · rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hc, one_smul, hU.1]
  · rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hc', one_smul, hU.2]

lemma IsU.star_pow_mul_pow {R : A} (hR : IsU R) (n : ℕ) : star R ^ n * R ^ n = 1 := by
  rw [← star_pow]; exact (hR.pow n).1

lemma IsU.pow_mul_star_pow {R : A} (hR : IsU R) (n : ℕ) : R ^ n * star R ^ n = 1 := by
  rw [← star_pow]; exact (hR.pow n).2

/-- The quarter-phase unitary `1 + (i - 1) P` (eigenvalue `1` on `ker P`, `i` on `ran P`). -/
noncomputable def qp (P : A) : A := 1 + (I - 1 : ℂ) • P

lemma qp_mul_qp (P Q : A) :
    qp P * qp Q = 1 + (I - 1 : ℂ) • P + (I - 1 : ℂ) • Q + ((I - 1) * (I - 1) : ℂ) • (P * Q) := by
  simp only [qp, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_smul]
  module

lemma star_qp {P : A} (hP : star P = P) : star (qp P) = 1 + (-I - 1 : ℂ) • P := by
  simp only [qp, star_add, star_one, star_smul, hP, star_I_sub_one]

lemma qp_zero : qp (0 : A) = 1 := by simp [qp]

lemma qp_isU {P : A} (hP : IsStarProjection P) : IsU (qp P) := by
  obtain ⟨h1, h2⟩ := isStarProjection_iff'.1 hP
  have key : ∀ a b : ℂ, a + b + a * b = 0 → (1 + a • P) * (1 + b • P) = 1 := by
    intro a b hab
    have e : (1 + a • P) * (1 + b • P) = 1 + (a + b + a * b) • P := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
        smul_smul, h1]
      module
    rw [e, hab, zero_smul, add_zero]
  constructor
  · rw [star_qp h2, qp]; exact key _ _ (by cring)
  · rw [star_qp h2, qp]; exact key _ _ (by cring)

lemma qp_mul_qp_of_mul_eq_zero {P Q : A} (hPQ : P * Q = 0) : qp P * qp Q = qp (P + Q) := by
  rw [qp_mul_qp, hPQ, smul_zero, add_zero, qp, smul_add, add_assoc]

/-- Lemma 3.1 (ii): a unitary `X` with `(X - 1)(X - i) = 0` satisfies `X + i X⋆ = (1 + i) 1`. -/
lemma two_valued_ii {X : A} (hX : IsU X) (h : (X - 1) * (X - I • 1) = 0) :
    X + I • star X = (1 + I) • (1 : A) := by
  have h2 : star X * ((X - 1) * (X - I • 1)) = 0 := by rw [h, mul_zero]
  have e : star X * ((X - 1) * (X - I • 1)) = X - I • 1 - 1 + I • star X := by
    simp only [mul_sub, sub_mul, mul_smul_comm, mul_one, one_mul, ← mul_assoc, hX.1]
    module
  rw [e] at h2
  linear_combination (norm := module) h2

/-- Lemma 3.1: a unitary with spectrum in `{1, i}` is a quarter-phase unitary `qp E` for the
star projection `E = (i - 1)⁻¹ (X - 1)`. -/
lemma exists_proj_of_two_valued {X : A} (hX : IsU X) (h : (X - 1) * (X - I • 1) = 0) :
    IsStarProjection ((I - 1 : ℂ)⁻¹ • (X - 1)) ∧ X = qp ((I - 1 : ℂ)⁻¹ • (X - 1)) := by
  have hne := I_sub_one_ne_zero
  have hsq : (X - 1) * (X - 1) = (I - 1 : ℂ) • (X - 1) := by
    have e : (X - 1) * (X - 1) = (X - 1) * (X - I • 1) + (X - 1) * ((I - 1 : ℂ) • (1 : A)) := by
      rw [← mul_add]
      congr 1
      rw [sub_smul, one_smul]
      abel
    rw [e, h, zero_add, mul_smul_comm, mul_one]
  have hstar : star X = (1 - I : ℂ) • (1 : A) + I • X := by
    have hii := two_valued_ii hX h
    have e : star X = (-I : ℂ) • (I • star X) := by
      rw [smul_smul]
      have : (-I * I : ℂ) = 1 := by cring
      rw [this, one_smul]
    rw [e]
    have e2 : I • star X = (1 + I) • (1 : A) - X := by rw [← hii]; abel
    rw [e2]
    match_scalars <;> cring
  have hc : star ((I - 1 : ℂ)⁻¹) * I = (I - 1 : ℂ)⁻¹ := by
    rw [star_inv₀, star_I_sub_one]
    have h1 : (-I - 1 : ℂ) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
    rw [inv_mul_eq_iff_eq_mul₀ h1, eq_mul_inv_iff_mul_eq₀ hne]
    cring
  refine ⟨?_, ?_⟩
  · rw [isStarProjection_iff']
    constructor
    · rw [smul_mul_assoc, mul_smul_comm, smul_smul, hsq, smul_smul, mul_assoc,
        inv_mul_cancel₀ hne, mul_one]
    · rw [star_smul, star_sub, star_one, hstar]
      have e : (1 - I : ℂ) • (1 : A) + I • X - 1 = I • (X - 1) := by module
      rw [e, smul_smul, hc]
  · rw [qp, smul_smul, mul_inv_cancel₀ hne, one_smul]
    abel

/-- Lemma 3.2 (Jordan-type lemma). If `P`, `Q` are star projections and the product of the
quarter-phase unitaries `X = qp P * qp Q` satisfies `(X - 1)(X - i) = 0`, then `P * Q = 0`. -/
theorem jordan (hC : ∀ x : A, star x * x = 0 → x = 0) {P Q : A}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (h : (qp P * qp Q - 1) * (qp P * qp Q - I • 1) = 0) : P * Q = 0 := by
  obtain ⟨hP1, hP2⟩ := isStarProjection_iff'.1 hP
  obtain ⟨hQ1, hQ2⟩ := isStarProjection_iff'.1 hQ
  have hX : IsU (qp P * qp Q) := (qp_isU hP).mul (qp_isU hQ)
  have hii := two_valued_ii hX h
  rw [star_mul, star_qp hQ2, star_qp hP2] at hii
  simp only [qp, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add] at hii
  -- the relation `X + i X⋆ = (1 + i) 1` reduces to `-2i PQ - 2 QP = 0`
  have key : ((-2 : ℂ) * I) • (P * Q) + (-2 : ℂ) • (Q * P) = 0 := by
    linear_combination (norm := skip) hii
    match_scalars <;> cring
  have hPP : ∀ x : A, x * P * P = x * P := fun x => by rw [mul_assoc, hP1]
  have hPQP : P * Q * P = 0 := by
    have h3 : P * (((-2 : ℂ) * I) • (P * Q) + (-2 : ℂ) • (Q * P)) * P = 0 := by
      rw [key, mul_zero, zero_mul]
    have e : P * (((-2 : ℂ) * I) • (P * Q) + (-2 : ℂ) • (Q * P)) * P
        = ((-2 : ℂ) * I + (-2 : ℂ)) • (P * Q * P) := by
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hP1, hPP]
      module
    rw [e] at h3
    have hc : ((-2 : ℂ) * I + (-2 : ℂ)) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
    rcases smul_eq_zero.1 h3 with h0 | h0
    · exact absurd h0 hc
    · exact h0
  have hQP : Q * P = 0 := by
    apply hC
    rw [star_mul, hP2, hQ2]
    calc P * Q * (Q * P) = P * (Q * Q) * P := by simp only [mul_assoc]
      _ = 0 := by rw [hQ1, hPQP]
  calc P * Q = star (Q * P) := by rw [star_mul, hP2, hQ2]
    _ = 0 := by rw [hQP, star_zero]

end Basic

section Rigidity

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The conjugates `P j = R ^ j * p * R⋆ ^ j`. -/
def cP (R p : A) (j : ℕ) : A := R ^ j * p * star R ^ j

/-- `prodQ n = qp (P (n - 1)) * ⋯ * qp (P 0)`. -/
noncomputable def prodQ (R p : A) : ℕ → A
  | 0 => 1
  | n + 1 => qp (cP R p n) * prodQ R p n

/-- Partial sums `E k = P 0 + ⋯ + P (k - 1)`. -/
def cE (R p : A) (k : ℕ) : A := ∑ j ∈ Finset.range k, cP R p j

/-- The candidate matrix units `e j k = R ^ j * p * R⋆ ^ k`. -/
def mu (R p : A) (j k : ℕ) : A := R ^ j * p * star R ^ k

lemma cP_isStarProjection {R p : A} (hR : IsU R) (hp : IsStarProjection p) (j : ℕ) :
    IsStarProjection (cP R p j) := by
  obtain ⟨h1, h2⟩ := isStarProjection_iff'.1 hp
  rw [isStarProjection_iff']
  constructor
  · calc cP R p j * cP R p j = R ^ j * p * (star R ^ j * R ^ j) * p * star R ^ j := by
          simp only [cP, mul_assoc]
      _ = R ^ j * (p * p) * star R ^ j := by
          rw [hR.star_pow_mul_pow, mul_one]; simp only [mul_assoc]
      _ = cP R p j := by rw [h1]; rfl
  · simp only [cP, star_mul, star_pow, star_star, h2, mul_assoc]

lemma cP_selfAdjoint {R p : A} (hR : IsU R) (hp : IsStarProjection p) (j : ℕ) :
    star (cP R p j) = cP R p j :=
  (isStarProjection_iff'.1 (cP_isStarProjection hR hp j)).2

lemma cP_zero (R p : A) : cP R p 0 = p := by simp [cP]

lemma conj_cP (R p : A) (i l : ℕ) : R ^ i * cP R p l * star R ^ i = cP R p (i + l) := by
  rw [cP, cP, show star R ^ (i + l) = star R ^ l * star R ^ i by rw [add_comm, pow_add], pow_add]
  simp only [mul_assoc]

lemma cP_add_period {R : A} (p : A) {d : ℕ} (hd : R ^ d = 1) (j : ℕ) :
    cP R p (j + d) = cP R p j := by
  have hs : star R ^ d = 1 := by rw [← star_pow, hd, star_one]
  simp only [cP, pow_add, hd, hs, mul_one]

lemma conj_qp {R : A} (hR : IsU R) (p : A) (n : ℕ) :
    R ^ n * qp p * star R ^ n = qp (cP R p n) := by
  simp only [qp, mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hR.pow_mul_star_pow, cP]

/-- Lemma 3.3 (product formula), in the form `R ^ n (R⋆ qp p) ^ n = qp (P (n-1)) ⋯ qp (P 0)`. -/
lemma prod_formula {R : A} (hR : IsU R) (p : A) :
    ∀ n : ℕ, R ^ n * (star R * qp p) ^ n = prodQ R p n
  | 0 => by simp [prodQ]
  | n + 1 => by
    rw [prodQ, ← prod_formula hR p n, ← conj_qp hR p n, pow_succ R n, pow_succ' (star R * qp p) n]
    calc R ^ n * R * (star R * qp p * (star R * qp p) ^ n)
        = R ^ n * (R * star R) * qp p * (star R * qp p) ^ n := by simp only [mul_assoc]
      _ = R ^ n * qp p * (star R ^ n * R ^ n) * (star R * qp p) ^ n := by
          rw [hR.2, hR.star_pow_mul_pow, mul_one, mul_one]
      _ = R ^ n * qp p * star R ^ n * (R ^ n * (star R * qp p) ^ n) := by simp only [mul_assoc]

/-- The product formula with the phase: if `R₂⋆ = z⋆ (R₁⋆ qp p)` then
`z ^ n R₁ ^ n R₂⋆ ^ n = prodQ R₁ p n`. -/
lemma zpow_link {R₁ R₂ p : A} {z : ℂ} (hz : star z * z = 1) (hR₁ : IsU R₁)
    (h : star R₂ = star z • (star R₁ * qp p)) (n : ℕ) :
    z ^ n • (R₁ ^ n * star R₂ ^ n) = prodQ R₁ p n := by
  rw [h, smul_pow, mul_smul_comm, smul_smul, ← mul_pow, mul_comm z, hz, one_pow, one_smul,
    prod_formula hR₁]

lemma cE_succ (R p : A) (k : ℕ) : cE R p (k + 1) = cE R p k + cP R p k := by
  simp [cE, Finset.sum_range_succ]

lemma cE_mul_cP {R p : A} (hR : IsU R) (hp : IsStarProjection p) {k j : ℕ} (hj : j < k)
    (horth : ∀ i < k, i ≠ j → cP R p i * cP R p j = 0) : cE R p k * cP R p j = cP R p j := by
  rw [cE, Finset.sum_mul, Finset.sum_eq_single j]
  · exact (isStarProjection_iff'.1 (cP_isStarProjection hR hp j)).1
  · intro i hi hij
    exact horth i (Finset.mem_range.1 hi) hij
  · intro hj'
    exact absurd (Finset.mem_range.2 hj) hj'

/-- If `P 0, …, P (k-1)` are mutually orthogonal, `E k` is a star projection and
`prodQ k = qp (E k)`. -/
lemma cE_prop {R p : A} (hR : IsU R) (hp : IsStarProjection p) :
    ∀ k : ℕ, (∀ i j, i < k → j < k → i ≠ j → cP R p i * cP R p j = 0) →
      IsStarProjection (cE R p k) ∧ prodQ R p k = qp (cE R p k)
  | 0, _ => by
    refine ⟨by simp [cE], ?_⟩
    simp [prodQ, cE, qp]
  | k + 1, h => by
    have h' : ∀ i j, i < k → j < k → i ≠ j → cP R p i * cP R p j = 0 :=
      fun i j hi hj hij => h i j (by omega) (by omega) hij
    obtain ⟨hE, hprod⟩ := cE_prop hR hp k h'
    have hEP : cE R p k * cP R p k = 0 := by
      rw [cE, Finset.sum_mul]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact h i k (by omega) (by omega) (by omega)
    have hPE : cP R p k * cE R p k = 0 := by
      rw [cE, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact h k i (by omega) (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [cE_succ]
      exact hE.add (cP_isStarProjection hR hp k) hEP
    · rw [prodQ, hprod, cE_succ, qp_mul_qp_of_mul_eq_zero hPE, add_comm]

/-- Lemma 3.4 (orthogonality induction): two-valuedness of `prodQ n` for `2 ≤ n ≤ K + 1` makes
`P 0, …, P K` mutually orthogonal. -/
lemma orth_upto (hC : ∀ x : A, star x * x = 0 → x = 0) {R p : A} (hR : IsU R)
    (hp : IsStarProjection p) (K : ℕ)
    (hT : ∀ n, 2 ≤ n → n ≤ K + 1 → (prodQ R p n - 1) * (prodQ R p n - I • 1) = 0) :
    ∀ k, k ≤ K → ∀ i j, i ≤ k → j ≤ k → i ≠ j → cP R p i * cP R p j = 0 := by
  intro k
  induction k with
  | zero => intro _ i j hi hj hij; exact absurd (show i = j by omega) hij
  | succ k ih =>
    intro hk i j hi hj hij
    have hprev := ih (by omega)
    have hlt : ∀ i j, i < k + 1 → j < k + 1 → i ≠ j → cP R p i * cP R p j = 0 :=
      fun i j hi hj hij => hprev i j (by omega) (by omega) hij
    obtain ⟨hE, hprod⟩ := cE_prop hR hp (k + 1) hlt
    have hTk := hT (k + 1 + 1) (by omega) (by omega)
    rw [prodQ, hprod] at hTk
    have hPE : cP R p (k + 1) * cE R p (k + 1) = 0 :=
      jordan hC (cP_isStarProjection hR hp (k + 1)) hE hTk
    have hnew : ∀ j, j < k + 1 → cP R p (k + 1) * cP R p j = 0 := by
      intro j hj
      have hEj := cE_mul_cP hR hp hj (fun i hi hij => hlt i j hi hj hij)
      rw [← hEj, ← mul_assoc, hPE, zero_mul]
    have hnew' : ∀ j, j < k + 1 → cP R p j * cP R p (k + 1) = 0 := by
      intro j hj
      rw [← cP_selfAdjoint hR hp j, ← cP_selfAdjoint hR hp (k + 1), ← star_mul, hnew j hj,
        star_zero]
    rcases Nat.lt_or_ge i (k + 1) with hi' | hi'
    · rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · exact hlt i j hi' hj' hij
      · have hj2 : j = k + 1 := by omega
        subst hj2
        exact hnew' i hi'
    · have hi2 : i = k + 1 := by omega
      subst hi2
      exact hnew j (by omega)

/-- Lemma 3.5 (cyclic transport): with `R ^ d = 1`, orthogonality of `P 0, …, P (d / 2)` implies
that `P 0, …, P (d - 1)` are mutually orthogonal. -/
lemma orth_all {R p : A} (hR : IsU R) (hp : IsStarProjection p) {d : ℕ} (hd : R ^ d = 1)
    (horth : ∀ i j, i ≤ d / 2 → j ≤ d / 2 → i ≠ j → cP R p i * cP R p j = 0) :
    ∀ i j, i < d → j < d → i ≠ j → cP R p i * cP R p j = 0 := by
  have conj0 : ∀ i r, cP R p i * cP R p (i + r) = R ^ i * (cP R p 0 * cP R p r) * star R ^ i := by
    intro i r
    have e0 : cP R p i = R ^ i * cP R p 0 * star R ^ i := by rw [conj_cP, add_zero]
    rw [e0, ← conj_cP R p i r]
    calc R ^ i * cP R p 0 * star R ^ i * (R ^ i * cP R p r * star R ^ i)
        = R ^ i * cP R p 0 * (star R ^ i * R ^ i) * cP R p r * star R ^ i := by
          simp only [mul_assoc]
      _ = R ^ i * (cP R p 0 * cP R p r) * star R ^ i := by
          rw [hR.star_pow_mul_pow, mul_one]; simp only [mul_assoc]
  have hlt : ∀ i j, i < j → j < d → cP R p i * cP R p j = 0 := by
    intro i j hij hj
    by_cases hr : j - i ≤ d / 2
    · have e : cP R p i * cP R p j = cP R p i * cP R p (i + (j - i)) := by
        congr 2; omega
      rw [e, conj0, horth 0 (j - i) (by omega) hr (by omega), mul_zero, zero_mul]
    · have e : cP R p j * cP R p i = cP R p j * cP R p (j + (d - (j - i))) := by
        rw [← cP_add_period p hd i]
        congr 2; omega
      have h0 : cP R p j * cP R p i = 0 := by
        rw [e, conj0, horth 0 (d - (j - i)) (by omega) (by omega) (by omega), mul_zero, zero_mul]
      rw [← cP_selfAdjoint hR hp i, ← cP_selfAdjoint hR hp j, ← star_mul, h0, star_zero]
  intro i j hi hj hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hlt i j h hj
  · rw [← cP_selfAdjoint hR hp i, ← cP_selfAdjoint hR hp j, ← star_mul, hlt j i h hi, star_zero]

/-- Lemma 3.7 (matrix units), multiplication rule. -/
lemma mu_mul {R p : A} (hR : IsU R) (hp : IsStarProjection p) {d : ℕ}
    (horth : ∀ i j, i < d → j < d → i ≠ j → cP R p i * cP R p j = 0)
    (j k l m : ℕ) (hk : k < d) (hl : l < d) :
    mu R p j k * mu R p l m = if k = l then mu R p j m else 0 := by
  obtain ⟨h1, h2⟩ := isStarProjection_iff'.1 hp
  -- `p R^r p = 0` for `0 < r < d`
  have hA : ∀ r, 0 < r → r < d → p * R ^ r * p = 0 := by
    intro r hr0 hrd
    have h0 : p * (R ^ r * p * star R ^ r) = 0 := by
      have := horth 0 r (by omega) hrd (by omega)
      rwa [cP_zero, cP] at this
    calc p * R ^ r * p = p * R ^ r * p * (star R ^ r * R ^ r) := by
          rw [hR.star_pow_mul_pow, mul_one]
      _ = p * (R ^ r * p * star R ^ r) * R ^ r := by simp only [mul_assoc]
      _ = 0 := by rw [h0, zero_mul]
  split_ifs with hkl
  · rw [← hkl]
    simp only [mu]
    calc R ^ j * p * star R ^ k * (R ^ k * p * star R ^ m)
        = R ^ j * p * (star R ^ k * R ^ k) * p * star R ^ m := by simp only [mul_assoc]
      _ = R ^ j * p * star R ^ m := by
          rw [hR.star_pow_mul_pow, mul_one, mul_assoc (R ^ j) p p, h1]
  · rcases Nat.lt_or_gt_of_ne hkl with h | h
    · obtain ⟨r, rfl⟩ : ∃ r, l = k + r := ⟨l - k, by omega⟩
      simp only [mu]
      calc R ^ j * p * star R ^ k * (R ^ (k + r) * p * star R ^ m)
          = R ^ j * p * (star R ^ k * R ^ k) * R ^ r * p * star R ^ m := by
            simp only [pow_add, mul_assoc]
        _ = R ^ j * (p * R ^ r * p) * star R ^ m := by
            rw [hR.star_pow_mul_pow, mul_one]; simp only [mul_assoc]
        _ = 0 := by rw [hA r (by omega) (by omega), mul_zero, zero_mul]
    · obtain ⟨s, rfl⟩ : ∃ s, k = l + s := ⟨k - l, by omega⟩
      have hB : p * star R ^ s * p = 0 := by
        have := congrArg star (hA s (by omega) (by omega))
        simpa [star_mul, star_pow, h2, mul_assoc] using this
      simp only [mu]
      calc R ^ j * p * star R ^ (l + s) * (R ^ l * p * star R ^ m)
          = R ^ j * p * star R ^ s * (star R ^ l * R ^ l) * p * star R ^ m := by
            rw [show star R ^ (l + s) = star R ^ s * star R ^ l by rw [add_comm, pow_add]]
            simp only [mul_assoc]
        _ = R ^ j * (p * star R ^ s * p) * star R ^ m := by
            rw [hR.star_pow_mul_pow, mul_one]; simp only [mul_assoc]
        _ = 0 := by rw [hB, mul_zero, zero_mul]

lemma mu_star (R p : A) (hp : IsStarProjection p) (j k : ℕ) : star (mu R p j k) = mu R p k j := by
  obtain ⟨-, h2⟩ := isStarProjection_iff'.1 hp
  simp only [mu, star_mul, star_pow, star_star, h2, mul_assoc]

lemma R_eq_sum {R : A} (p : A) {d : ℕ} (hd : R ^ d = 1) (hE : cE R p d = 1) :
    R = ∑ j ∈ Finset.range d, mu R p ((j + 1) % d) j := by
  calc R = R * cE R p d := by rw [hE, mul_one]
    _ = ∑ j ∈ Finset.range d, R * cP R p j := by rw [cE, Finset.mul_sum]
    _ = ∑ j ∈ Finset.range d, mu R p ((j + 1) % d) j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [cP, mu, ← mul_assoc, ← mul_assoc, ← pow_succ', pow_eq_pow_mod (j + 1) hd]

/-- **Theorem 3.8 (algebraic rigidity).** Unitaries `R₁ … R₄` with `R₁ ^ d = R₂ ^ d = 1`, equal first
three links and the two-eigenvalue relations for `1 ≤ n ≤ d / 2 + 1` are in canonical DKZ form:
there is a star projection `p` with `R_{k+1} = z (1 - (1 + i) p) R_k`, and
`e j k = R₁ ^ j p R₁⋆ ^ k` (`j, k < d`) are `d × d` matrix units with `∑ e j j = 1`, in which
`R₁ = ∑ e ((j + 1) % d) j` is the cyclic shift. -/
theorem rigidity (hC : ∀ x : A, star x * x = 0 → x = 0)
    {d : ℕ} {z : ℂ} (hz : star z * z = 1) (hzd : z ^ d = I)
    {R₁ R₂ R₃ R₄ : A} (hR₁ : IsU R₁) (hR₂ : IsU R₂) (hR₃ : IsU R₃)
    (hp₁ : R₁ ^ d = 1) (hp₂ : R₂ ^ d = 1)
    (hE₁ : R₁ * star R₂ = R₂ * star R₃) (hE₂ : R₂ * star R₃ = R₃ * star R₄)
    (hT : ∀ n, 1 ≤ n → n ≤ d / 2 + 1 →
      (z ^ n • (R₁ ^ n * star R₂ ^ n) - 1) * (z ^ n • (R₁ ^ n * star R₂ ^ n) - I • 1) = 0) :
    ∃ p : A, IsStarProjection p ∧
      R₂ = z • ((1 - (1 + I) • p) * R₁) ∧ R₃ = z • ((1 - (1 + I) • p) * R₂) ∧
      R₄ = z • ((1 - (1 + I) • p) * R₃) ∧
      (∀ j k l m, k < d → l < d →
        mu R₁ p j k * mu R₁ p l m = if k = l then mu R₁ p j m else 0) ∧
      (∀ j k, star (mu R₁ p j k) = mu R₁ p k j) ∧
      (∑ j ∈ Finset.range d, mu R₁ p j j = 1) ∧
      R₁ = ∑ j ∈ Finset.range d, mu R₁ p ((j + 1) % d) j := by
  have hzz : z * star z = 1 := by rw [mul_comm]; exact hz
  -- Step 1: the projection `p` from the relation for `n = 1`.
  have hXU : IsU (z • (R₁ * star R₂)) := (hR₁.mul hR₂.star').smul hz
  have hT1 : (z • (R₁ * star R₂) - 1) * (z • (R₁ * star R₂) - I • 1) = 0 := by
    simpa [pow_one] using hT 1 le_rfl (by omega)
  obtain ⟨hproj, hXq⟩ := exists_proj_of_two_valued hXU hT1
  set p : A := (I - 1 : ℂ)⁻¹ • (z • (R₁ * star R₂) - 1) with hpdef
  have hp2 : star p = p := (isStarProjection_iff'.1 hproj).2
  have hD : star (qp p) = 1 - (1 + I) • p := by
    rw [star_qp hp2]
    module
  -- Step 2: every link equal to `R₁ R₂⋆` gives `R_{k+1} = z D R_k`.
  have link : ∀ S T : A, IsU S → S * star T = R₁ * star R₂ → T = z • (star (qp p) * S) := by
    intro S T hS h
    have h1 : z • (S * star T) = qp p := by rw [h]; exact hXq
    have h2 : star z • (T * star S) = star (qp p) := by
      rw [← h1, star_smul, star_mul, star_star]
    have h3 : star (qp p) * S = star z • T := by
      rw [← h2, smul_mul_assoc, mul_assoc, hS.1, mul_one]
    rw [h3, smul_smul, hzz, one_smul]
  have e2 := link R₁ R₂ hR₁ rfl
  have e3 := link R₂ R₃ hR₂ hE₁.symm
  have e4 := link R₃ R₄ hR₃ (hE₂.symm.trans hE₁.symm)
  -- Step 3: product formula.
  have hstar2 : star R₂ = star z • (star R₁ * qp p) := by
    conv_lhs => rw [e2]
    rw [star_smul, star_mul, star_star]
  have hprod : ∀ n, z ^ n • (R₁ ^ n * star R₂ ^ n) = prodQ R₁ p n := zpow_link hz hR₁ hstar2
  -- Step 4: orthogonality of `P 0, …, P (d/2)`, then of all `P j`, `j < d`.
  have hTn : ∀ n, 2 ≤ n → n ≤ d / 2 + 1 → (prodQ R₁ p n - 1) * (prodQ R₁ p n - I • 1) = 0 := by
    intro n hn1 hn2
    rw [← hprod n]
    exact hT n (by omega) hn2
  have horth0 := orth_upto hC hR₁ hproj (d / 2) hTn (d / 2) le_rfl
  have horth := orth_all hR₁ hproj hp₁ horth0
  -- Step 5: resolution of the identity.
  obtain ⟨-, hprodE⟩ := cE_prop hR₁ hproj d (fun i j hi hj hij => horth i j hi hj hij)
  have hsd : star R₂ ^ d = 1 := by rw [← star_pow, hp₂, star_one]
  have hEd : cE R₁ p d = 1 := by
    have h1 : qp (cE R₁ p d) = I • (1 : A) := by
      rw [← hprodE, ← hprod d, hp₁, hsd, hzd, mul_one]
    have h2 : (I - 1 : ℂ) • cE R₁ p d = (I - 1 : ℂ) • (1 : A) := by
      rw [qp] at h1
      have h3 : (I - 1 : ℂ) • (1 : A) = I • (1 : A) - 1 := by rw [sub_smul, one_smul]
      rw [h3, ← h1]
      abel
    have := congrArg (fun x => (I - 1 : ℂ)⁻¹ • x) h2
    simpa [smul_smul, inv_mul_cancel₀ I_sub_one_ne_zero] using this
  refine ⟨p, hproj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hD]; exact e2
  · rw [← hD]; exact e3
  · rw [← hD]; exact e4
  · intro j k l m hk hl
    exact mu_mul hR₁ hproj horth j k l m hk hl
  · intro j k
    exact mu_star R₁ p hproj j k
  · exact hEd
  · exact R_eq_sum p hp₁ hEd

end Rigidity

section Matrices

open scoped ComplexOrder in
/-- **Theorem 3.9 (dimension).** For `D × D` complex matrices satisfying the hypotheses of
`rigidity`, `d` divides `D`. -/
theorem dvd_of_rigidity {D d : ℕ} {z : ℂ} (hz : star z * z = 1) (hzd : z ^ d = I)
    {R₁ R₂ R₃ R₄ : Matrix (Fin D) (Fin D) ℂ} (hR₁ : IsU R₁) (hR₂ : IsU R₂) (hR₃ : IsU R₃)
    (hp₁ : R₁ ^ d = 1) (hp₂ : R₂ ^ d = 1)
    (hE₁ : R₁ * star R₂ = R₂ * star R₃) (hE₂ : R₂ * star R₃ = R₃ * star R₄)
    (hT : ∀ n, 1 ≤ n → n ≤ d / 2 + 1 →
      (z ^ n • (R₁ ^ n * star R₂ ^ n) - 1) * (z ^ n • (R₁ ^ n * star R₂ ^ n) - I • 1) = 0) :
    d ∣ D := by
  have hC : ∀ x : Matrix (Fin D) (Fin D) ℂ, star x * x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.star_eq_conjTranspose] at hx
    exact Matrix.conjTranspose_mul_self_eq_zero.1 hx
  obtain ⟨p, hp, -, -, -, hmu, -, hsum, -⟩ :=
    rigidity hC hz hzd hR₁ hR₂ hR₃ hp₁ hp₂ hE₁ hE₂ hT
  have hmu00 : mu R₁ p 0 0 = p := by simp [mu]
  have htr : ∀ j, j < d → (mu R₁ p j j).trace = p.trace := by
    intro j hj
    have e : mu R₁ p j j = mu R₁ p j 0 * mu R₁ p 0 j := by
      rw [hmu j 0 0 j (by omega) (by omega), if_pos rfl]
    rw [e, Matrix.trace_mul_comm, hmu 0 j j 0 hj hj, if_pos rfl, hmu00]
  have hD : (D : ℂ) = d * p.trace := by
    have h1 := congrArg Matrix.trace hsum
    rw [Matrix.trace_sum, Matrix.trace_one, Fintype.card_fin,
      Finset.sum_congr rfl (fun j hj => htr j (Finset.mem_range.1 hj))] at h1
    rw [← h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hidem : IsIdempotentElem (Matrix.toLin' p) := by
    have h1 : p * p = p := (isStarProjection_iff'.1 hp).1
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h1]
  have hrank : p.trace = (Module.finrank ℂ (LinearMap.range (Matrix.toLin' p)) : ℂ) := by
    rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace]
  refine ⟨Module.finrank ℂ (LinearMap.range (Matrix.toLin' p)), ?_⟩
  have h2 : (D : ℂ) = ((d * Module.finrank ℂ (LinearMap.range (Matrix.toLin' p)) : ℕ) : ℂ) := by
    rw [hD, hrank]; push_cast; ring
  exact_mod_cast h2

end Matrices

end CGLMPRigidity
