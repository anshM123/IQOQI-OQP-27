import OQP27.RigidityClassical

/-!
# The classical Theorem B for `d = 2` (module L6)

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Theorem B (the case `d = 2`, i.e. CHSH).

`OQP27.Rig.classicalTheoremB_two`: the hypothesis `OQP27.Rig.Hyp_ClassicalTheoremB 2` holds. For `d = 2`,
`F(a) = Re[h_1 i^{a_1 - a_0}]` with `h_1 = √2 - i√2`, so `F(a) ∈ {√2, √2, -√2, -√2}` according to
`a_1 - a_0 ∈ {0, 1, 2, 3}`, `F_DKZ = √2`, and the maximisers `a_1 - a_0 ∈ {0, 1}` are exactly the one-step
configurations. This shows in particular that the hypothesis is satisfiable as stated. No hypotheses.
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset

namespace OQP27.Rig

lemma clockFa_two (a : Fin 2 → ZMod 4) : clockFa a = (hm 2 1 * I ^ (a 1 - a 0).val).re := by
  unfold clockFa
  simp [Fin.sum_univ_two]

lemma hm_two_one :
    hm 2 1 = ((1 / Real.cos (Real.pi / 4) : ℝ) : ℂ) - I * ((1 / Real.cos (Real.pi / 4) : ℝ) : ℂ) := by
  unfold hm
  have e : Real.pi * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ)) = Real.pi / 4 := by push_cast; ring
  rw [e, Real.sin_pi_div_four, ← Real.cos_pi_div_four]

lemma FDKZ_two : FDKZ 2 = 1 / Real.cos (Real.pi / 4) := by
  unfold FDKZ
  have e : Real.pi * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ)) = Real.pi / 4 := by push_cast; ring
  rw [show Finset.Ico 1 2 = {1} from rfl, Finset.sum_singleton, e]
  push_cast
  ring

/-- **Theorem B for `d = 2`.** -/
theorem classicalTheoremB_two : Hyp_ClassicalTheoremB 2 := by
  intro a
  set c : ℝ := 1 / Real.cos (Real.pi / 4) with hc
  have hcpos : 0 < c := by
    rw [hc, Real.cos_pi_div_four]
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    positivity
  rw [clockFa_two, hm_two_one, FDKZ_two, ← hc]
  have key : ∀ s : ZMod 4, s = a 1 - a 0 →
      ((c : ℂ) - I * (c : ℂ)) * I ^ s.val = ((c : ℂ) - I * (c : ℂ)) * I ^ (a 1 - a 0).val := by
    intro s hs; rw [hs]
  have hcases : ∀ s : ZMod 4, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by decide
  rcases hcases (a 1 - a 0) with h | h | h | h
  · -- `a_1 = a_0`: value `c`, one-step with `r = 0`
    rw [h]
    have hv : (((c : ℂ) - I * (c : ℂ)) * I ^ (0 : ZMod 4).val).re = c := by
      simp [show (0 : ZMod 4).val = 0 from rfl]
    rw [hv]
    refine ⟨le_rfl, fun _ => ⟨a 0 - 1, 0, by norm_num, fun k => ?_⟩⟩
    have h10 : a 1 = a 0 := by linear_combination h
    fin_cases k <;> simp [h10]
  · -- `a_1 = a_0 + 1`: value `c`, one-step with `r = 1`
    rw [h]
    have hv : (((c : ℂ) - I * (c : ℂ)) * I ^ (1 : ZMod 4).val).re = c := by
      simp [show (1 : ZMod 4).val = 1 from rfl]
    rw [hv]
    refine ⟨le_rfl, fun _ => ⟨a 0, 1, by norm_num, fun k => ?_⟩⟩
    have h10 : a 1 = a 0 + 1 := by linear_combination h
    fin_cases k <;> simp [h10]
  · rw [h]
    have hv : (((c : ℂ) - I * (c : ℂ)) * I ^ (2 : ZMod 4).val).re = -c := by
      simp [show (2 : ZMod 4).val = 2 from rfl, pow_two]
    rw [hv]
    refine ⟨by linarith, fun h' => absurd h' (by linarith)⟩
  · rw [h]
    have hv : (((c : ℂ) - I * (c : ℂ)) * I ^ (3 : ZMod 4).val).re = -c := by
      simp [show (3 : ZMod 4).val = 3 from rfl, pow_succ]
    rw [hv]
    refine ⟨by linarith, fun h' => absurd h' (by linarith)⟩

end OQP27.Rig
