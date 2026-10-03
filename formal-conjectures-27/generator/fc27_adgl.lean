/- ### A related question: the maximally entangled state is not optimal for $d = 3$

Acín, Durt, Gisin and Latorre (2002) observed that the CGLMP inequality is violated more strongly
by non-maximally entangled states than by $\Phi_3$. Here: with the DKZ measurements, the state
$(|00\rangle + \tfrac{4}{5} |11\rangle + |22\rangle) / \sqrt{2 + 16/25}$ gives the value
$\frac{82}{33} - \frac{80}{99}\sqrt{3} \approx 1.0852$ of the CGLMP functional, below the minimum
$\frac{24 - 8\sqrt{3}}{9} \approx 1.1271$ over all complete von Neumann measurements on $\Phi_3$
(`adglState_beats_maxEntangledState`). -/

namespace OpenQuantumProblem27

open Matrix
open scoped Kronecker

section RelatedQuestion

/-- The state $(|00\rangle + \gamma |11\rangle + |22\rangle) / \sqrt{2 + \gamma^2}$ of two qutrits. -/
noncomputable def adglState (γ : ℝ) : BipartiteState 3 :=
  WithLp.toLp 2 fun ij => if ij.1 = ij.2 then
    ((((if (ij.1 : ℕ) = 1 then γ else 1) / Real.sqrt (2 + γ ^ 2)) : ℝ) : ℂ) else 0

@[category API, AMS 15 81]
theorem dkzUnitaryA_apply (d : ℕ) (x : Fin 2) (j k : Fin d) :
    dkzUnitaryA d x j k = ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
      Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * (((k : ℕ) : ℂ) + (dkzAlpha x : ℂ)) / d)) := by
  simp only [dkzUnitaryA, phaseDiagonal, dftMatrix, diagonal_mul, conjTranspose_apply, of_apply,
    star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj, map_div₀,
    map_mul, Complex.conj_I, map_ofNat, Complex.conj_natCast]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

@[category API, AMS 15 81]
theorem dkzUnitaryB_apply (d : ℕ) (y : Fin 2) (j l : Fin d) :
    dkzUnitaryB d y j l = ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) * (((l : ℕ) : ℂ) - (dkzBeta y : ℂ)) / d) := by
  simp only [dkzUnitaryB, phaseDiagonal, dftMatrix, diagonal_mul, of_apply]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The Born rule for rank-one projections**: in a pure state $\psi$,
$\operatorname{Tr}[|\psi\rangle\langle\psi| \, (|v\rangle\langle v| \otimes |w\rangle\langle w|)]
= |\langle v \otimes w | \psi\rangle|^2$. -/
@[category API, AMS 15 81]
theorem bornProb_vecMulVec {D : ℕ} (ψ : BipartiteState D) (v w : Fin D → ℂ) :
    bornProb (densityMatrix ψ) (vecMulVec v (star v)) (vecMulVec w (star w)) =
      Complex.normSq (∑ i, ∑ j, star (v i) * star (w j) * WithLp.ofLp ψ (i, j)) := by
  set φ : Fin D × Fin D → ℂ := WithLp.ofLp ψ with hφ
  set c := ∑ i, ∑ j, star (v i) * star (w j) * φ (i, j) with hc
  have hM : (vecMulVec v (star v) ⊗ₖ vecMulVec w (star w)) *ᵥ φ = fun ij => v ij.1 * w ij.2 * c := by
    funext ij
    obtain ⟨i, j⟩ := ij
    simp only [mulVec, dotProduct, kroneckerMap_apply, vecMulVec_apply, Fintype.sum_prod_type,
      Pi.star_apply, hc]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hs : star φ ⬝ᵥ (fun ij => v ij.1 * w ij.2 * c) = star c * c := by
    rw [hc, star_sum, Finset.sum_mul, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.star_apply, star_mul', star_star]
    ring
  rw [bornProb, densityMatrix, trace_vecMulVec_mul, hM, hs, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- $|1 + \gamma e^{i\theta} + e^{2 i\theta}|^2 = (\gamma + 2\cos\theta)^2$. -/
@[category API, AMS 15 81]
theorem normSq_one_add_exp (γ θ : ℝ) :
    Complex.normSq (1 + (γ : ℂ) * Complex.exp (θ * Complex.I) + Complex.exp (2 * θ * Complex.I)) =
      (γ + 2 * Real.cos θ) ^ 2 := by
  have h : 1 + (γ : ℂ) * Complex.exp (θ * Complex.I) + Complex.exp (2 * θ * Complex.I) =
      Complex.exp (θ * Complex.I) * ((γ + 2 * Real.cos θ : ℝ) : ℂ) := by
    have e1 : Complex.exp (θ * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      simp
    have e2 : Complex.exp (2 * θ * Complex.I) =
        Complex.exp (θ * Complex.I) * Complex.exp (θ * Complex.I) := by
      rw [← Complex.exp_add]
      ring_nf
    push_cast
    rw [Complex.cos, e2]
    linear_combination -e1
  rw [h, Complex.normSq_mul, Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I,
    one_pow, one_mul, Complex.normSq_ofReal]
  ring

/-- $4(\alpha_x + \beta_y)$ for the DKZ phases. -/
def dkzKappa : Fin 2 → Fin 2 → ℤ := ![![1, 3], ![-1, 1]]

@[category API, AMS 15 81]
lemma dkzAlpha_add_dkzBeta (x y : Fin 2) :
    (dkzAlpha x : ℝ) + dkzBeta y = (dkzKappa x y : ℝ) / 4 := by
  fin_cases x <;> fin_cases y <;> norm_num [dkzAlpha, dkzBeta, dkzKappa]

/-- The behaviour of the DKZ measurements on the state `adglState γ`. -/
@[category API, AMS 15 81]
theorem bornProb_adglState (γ : ℝ) (x y : Fin 2) (a b : Fin 3) :
    bornProb (densityMatrix (adglState γ)) (vonNeumannMeasurement (dkzUnitaryA 3 x) a)
      (vonNeumannMeasurement (dkzUnitaryB 3 y) b) =
      (γ + 2 * Real.cos (2 * Real.pi * ((((4 * (a : ℕ) - 4 * (b : ℕ) + dkzKappa x y : ℤ)) : ℝ) / 4) / 3)) ^ 2 /
        (9 * (2 + γ ^ 2)) := by
  set θ : ℝ := 2 * Real.pi * ((((4 * (a : ℕ) - 4 * (b : ℕ) + dkzKappa x y : ℤ)) : ℝ) / 4) / 3 with hθ
  have hN : 0 < 2 + γ ^ 2 := by positivity
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ = (1 / 3 : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast
    ring
  -- the product of the conjugated basis vectors is a power of `exp (i θ)`
  have hprod : ∀ i : Fin 3, star (dkzUnitaryA 3 x i a) * star (dkzUnitaryB 3 y i b) =
      (1 / 3 : ℂ) * Complex.exp (((i : ℕ) : ℂ) * θ * Complex.I) := by
    intro i
    rw [dkzUnitaryA_apply, dkzUnitaryB_apply, star_mul', star_mul', Complex.star_def,
      ← Complex.exp_conj, ← Complex.exp_conj]
    simp only [map_inv₀, Complex.conj_ofReal, map_neg, map_div₀, map_mul, map_sub, map_add,
      Complex.conj_I, map_ofNat, Complex.conj_natCast, Nat.cast_ofNat]
    rw [mul_mul_mul_comm, hs3, ← Complex.exp_add]
    congr 2
    have hk := dkzAlpha_add_dkzBeta x y
    rw [hθ]
    push_cast
    have hk' : (dkzAlpha x : ℂ) + (dkzBeta y : ℂ) = (dkzKappa x y : ℂ) / 4 := by
      exact_mod_cast hk
    linear_combination (2 * Real.pi * ((i : ℕ) : ℂ) / 3 * Complex.I) * hk'
  rw [vonNeumannMeasurement_eq_vecMulVec, vonNeumannMeasurement_eq_vecMulVec, bornProb_vecMulVec]
  -- only the diagonal of the state contributes
  have hdiag : ∀ i : Fin 3, ∑ j : Fin 3, star (dkzUnitaryA 3 x i a) * star (dkzUnitaryB 3 y j b) *
      WithLp.ofLp (adglState γ) (i, j) =
      star (dkzUnitaryA 3 x i a) * star (dkzUnitaryB 3 y i b) *
        ((((if (i : ℕ) = 1 then γ else 1) / Real.sqrt (2 + γ ^ 2)) : ℝ) : ℂ) := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [adglState, Ne.symm hji]) (by simp)]
    simp [adglState]
  rw [Finset.sum_congr rfl fun i _ => hdiag i, Fin.sum_univ_three]
  simp only [hprod]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    zero_mul, Complex.exp_zero, one_mul, if_true, if_false, OfNat.ofNat_ne_one, zero_ne_one]
  have hfac : (1 / 3 : ℂ) * 1 * (((1 / Real.sqrt (2 + γ ^ 2)) : ℝ) : ℂ) +
      (1 / 3 : ℂ) * Complex.exp (θ * Complex.I) * (((γ / Real.sqrt (2 + γ ^ 2)) : ℝ) : ℂ) +
      (1 / 3 : ℂ) * Complex.exp (2 * θ * Complex.I) * (((1 / Real.sqrt (2 + γ ^ 2)) : ℝ) : ℂ) =
      (((1 / (3 * Real.sqrt (2 + γ ^ 2))) : ℝ) : ℂ) *
        (1 + (γ : ℂ) * Complex.exp (θ * Complex.I) + Complex.exp (2 * θ * Complex.I)) := by
    push_cast
    ring
  rw [hfac, Complex.normSq_mul, normSq_one_add_exp, Complex.normSq_ofReal]
  have hsq : Real.sqrt (2 + γ ^ 2) * Real.sqrt (2 + γ ^ 2) = 2 + γ ^ 2 := Real.mul_self_sqrt hN.le
  have hsq0 : Real.sqrt (2 + γ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  field_simp
  rw [Real.sq_sqrt hN.le]
  ring

@[category API, AMS 15 81]
lemma cos_quarter (k : ℤ) : Real.cos (2 * Real.pi * ((k : ℝ) / 4) / 3) =
    Real.cos (((k % 12 : ℤ) : ℝ) * Real.pi / 6) := by
  have hk : (k : ℝ) = ((k % 12 : ℤ) : ℝ) + ((k / 12 : ℤ) : ℝ) * 12 := by
    exact_mod_cast (by omega : k = k % 12 + k / 12 * 12)
  rw [show 2 * Real.pi * ((k : ℝ) / 4) / 3 =
      ((k % 12 : ℤ) : ℝ) * Real.pi / 6 + ((k / 12 : ℤ) : ℝ) * (2 * Real.pi) by rw [hk]; ring]
  exact Real.cos_add_int_mul_two_pi _ _

/-- $\cos(k \pi / 6)$ for the odd residues $k$ modulo $12$. -/
@[category API, AMS 15 81]
lemma cos_odd_mul_pi_div_six (r : ℤ) (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 9 ∨ r = 11) :
    Real.cos ((r : ℝ) * Real.pi / 6) =
      if r = 1 ∨ r = 11 then Real.sqrt 3 / 2 else if r = 5 ∨ r = 7 then -(Real.sqrt 3 / 2) else 0 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [if_pos (Or.inl rfl), show ((1 : ℤ) : ℝ) * Real.pi / 6 = Real.pi / 6 by push_cast; ring,
      Real.cos_pi_div_six]
  · rw [if_neg (by decide), if_neg (by decide),
      show ((3 : ℤ) : ℝ) * Real.pi / 6 = Real.pi / 2 by push_cast; ring, Real.cos_pi_div_two]
  · rw [if_neg (by decide), if_pos (Or.inl rfl),
      show ((5 : ℤ) : ℝ) * Real.pi / 6 = Real.pi - Real.pi / 6 by push_cast; ring, Real.cos_pi_sub,
      Real.cos_pi_div_six]
  · rw [if_neg (by decide), if_pos (Or.inr rfl),
      show ((7 : ℤ) : ℝ) * Real.pi / 6 = Real.pi / 6 + Real.pi by push_cast; ring, Real.cos_add_pi,
      Real.cos_pi_div_six]
  · rw [if_neg (by decide), if_neg (by decide),
      show ((9 : ℤ) : ℝ) * Real.pi / 6 = Real.pi / 2 + Real.pi by push_cast; ring, Real.cos_add_pi,
      Real.cos_pi_div_two, neg_zero]
  · rw [if_pos (Or.inr rfl),
      show ((11 : ℤ) : ℝ) * Real.pi / 6 = -(Real.pi / 6) + 2 * Real.pi by push_cast; ring,
      Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_six]

@[category API, AMS 15 81]
lemma cos_quarter_val (k : ℤ) (hk : k % 2 = 1) : Real.cos (2 * Real.pi * ((k : ℝ) / 4) / 3) =
    if k % 12 = 1 ∨ k % 12 = 11 then Real.sqrt 3 / 2
      else if k % 12 = 5 ∨ k % 12 = 7 then -(Real.sqrt 3 / 2) else 0 := by
  rw [cos_quarter, cos_odd_mul_pi_div_six (k % 12) (by omega)]

/-- **The value for the non-maximally entangled state** `adglState (4/5)` with the DKZ
measurements: $rac{82}{33} - rac{80}{99}\sqrt{3}$. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_adglState :
    cglmpFunctional (quantumBehaviour (densityMatrix (adglState (4 / 5)))
      (fun x => vonNeumannMeasurement (dkzUnitaryA 3 x))
      (fun y => vonNeumannMeasurement (dkzUnitaryB 3 y))) = 82 / 33 - 80 / 99 * Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [cglmpFunctional, quantumBehaviour, bornProb_adglState, Fin.sum_univ_three]
  simp (disch := norm_num [dkzKappa]) only [cos_quarter_val]
  norm_num [dkzKappa]
  ring_nf
  nlinarith [h3]

/-- $I_{ME}(3) = rac{4}{3} + rac{8\sqrt{3}}{9}$. -/
@[category test, AMS 15 81]
theorem cglmpMaxEntValue_three : cglmpMaxEntValue 3 = 4 / 3 + 8 * Real.sqrt 3 / 9 := by
  have hI : Finset.Ico 1 3 = {1, 2} := rfl
  have hc1 : Real.cos (Real.pi * ((1 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ))) = Real.sqrt 3 / 2 := by
    rw [show Real.pi * ((1 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ)) = Real.pi / 6 by push_cast; ring]
    exact Real.cos_pi_div_six
  have hc2 : Real.cos (Real.pi * ((2 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ))) = 1 / 2 := by
    rw [show Real.pi * ((2 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ)) = Real.pi / 3 by push_cast; ring]
    exact Real.cos_pi_div_three
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := by positivity
  rw [cglmpMaxEntValue, hI, Finset.sum_pair (by norm_num), hc1, hc2]
  push_cast
  field_simp
  nlinarith [hs]

end RelatedQuestion

end OpenQuantumProblem27
