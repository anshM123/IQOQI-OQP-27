import OQP27.ClassicalDefs
import OQP27.CellClausen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The junction estimates for the classical Theorem B (module L7)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Lemma `lem:junction` (junction function) and the
margin `|e(1)| > 2 sc + fw` used after it (`eq:margin`).

With `κ(u) = cot(π u/N)` (`kap`), the smoothed kernel `κ̄` (`kbar`, `kbarR`) and the junction term
`e = κ - κ̄` (`ejun`) of `OQP27/ClassicalDefs.lean`, this file proves:

* `cot_le_kbarR`: `cot(π m/N) ≤ κ̄(m)` for `1 ≤ m`, `2(m+1) ≤ N`
  (`junc_cot_le_kbarR`: for all real `1 ≤ m ≤ N/2`);
* `kbarR_sub_cot_le`: `κ̄(m) - cot(π m/N) ≤ (N/π)/(6m(m²-1))` for `2 ≤ m`, `2(m+1) ≤ N`;
* `kbarR_one_sub_cot`: `κ̄(1) - cot(π/N) > (7/24) N/π` for `N ≥ 8`;
* `kap_neg`, `kbar_neg`, `ejun_neg`: `κ`, `κ̄` and `e` are odd on `ℤ_N`;
* `kap_strictAnti`: `κ(v+1) < κ(v)` for `1 ≤ v`, `v + 2 ≤ N`;
* `ejun_nonpos`: `e(v) ≤ 0` for `1 ≤ v ≤ N/2` (Lemma `lem:junction`(3));
* `junction_margin`: `2 sc + fw < -e(1) = |e(1)|` for `N ≥ 8`, where `sc = scSum N e` and
  `fw = fwSum N e` (Lemma `lem:junction`(3),(4) and the comparison of constants after it).

No hypotheses remain: every statement is proved from Mathlib and the facts on the Clausen function
proved in `OQP27/CellClausen.lean`.

## Route

This is a variant of the paper's proof.  The paper expands `e` in the partial-fraction series of
`π cot(π s)` (Lemma `lem:junction`(1),(2)); we work with the Clausen function directly.  Put
`Φ = -Cl₂` and `h = 2π/N`.  Then `κ̄(m) = (N²/(2π²)) (Φ((m+1)h) + Φ((m-1)h) - 2Φ(mh))`
(`junc_kbarR_eq`) and, on `(0, 2π)`, `Φ' = log(2 sin(·/2))` and `Φ'' = ½ cot(·/2)`
(`junc_hasDerivAt_Phi`, `junc_hasDerivAt_ell`).  The comparison lemmas `junc_master_le` and
`junc_master_ge` bound a second difference `f(x+h) + f(x-h) - 2f(x)` by `c h²/2 + k h⁴/12` from above
(or below) when `f''(x+t) + f''(x-t)` is bounded by `c + k t²` for `0 < t < h`; the proof is two
monotonicity arguments.  They are applied to
* `f = Φ`, with the midpoint convexity of `cot`
  (`cot(a+τ) + cot(a-τ) = 2 sin a cos a/(sin²a - sin²τ)`): this gives `κ̄(m) ≥ cot(π m/N)`;
* `f = Φ`, with `½ cot(y/2) = 1/y + g₂(y)` and the concavity of `g₂` (from Lazarević's inequality
  `z³ cos z ≤ sin³ z`, itself from `sin z ≥ z - z³/6` and `cos z ≤ 1 - z²/2 + z⁴/24`): this gives
  `κ̄(m) - cot(π m/N) ≤ (N/π)/(6m(m²-1))`;
* `f = Φ - y log y` at `x = h`, with `g₂(y) ≥ -y/8` (from `cot z ≥ 1/z - z/2`): this gives
  `κ̄(1) ≥ 2 log 2 · N/π - π/(2N)`, while `cot(π/N) ≤ N/π`.
The sums are bounded by telescoping: `∑_{m ≥ 2} (3m-2)/(6m(m²-1)) = 7/24` (`junc_sum_closed`), so
`2 sc + fw ≤ (7/24) N/π < |e(1)|`.
-/

set_option autoImplicit false

namespace OQP27.ClassB

open Real

/-! ## Monomials -/

lemma junc_hasDerivAt_sq (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
  simpa using hasDerivAt_pow 2 t

lemma junc_hasDerivAt_cube (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
  simpa using hasDerivAt_pow 3 t

lemma junc_hasDerivAt_four (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
  simpa using hasDerivAt_pow 4 t

/-! ## A second-difference comparison lemma -/

/-- **Second differences from a bound on the second derivative.**  If `f'' = G` on `(x - h, x + h)`
and `G(x + t) + G(x - t) ≤ c + k t²` for `0 < t < h`, then
`f(x + h) + f(x - h) - 2 f(x) ≤ c h²/2 + k h⁴/12`. -/
theorem junc_master_le {f f' G : ℝ → ℝ} {x h c k : ℝ} (hh : 0 < h)
    (hf : ContinuousOn f (Set.Icc (x - h) (x + h)))
    (hf' : ∀ y ∈ Set.Ioo (x - h) (x + h), HasDerivAt f (f' y) y)
    (hG : ∀ y ∈ Set.Ioo (x - h) (x + h), HasDerivAt f' (G y) y)
    (hb : ∀ t ∈ Set.Ioo 0 h, G (x + t) + G (x - t) ≤ c + k * t ^ 2) :
    f (x + h) + f (x - h) - 2 * f x ≤ c * h ^ 2 / 2 + k * h ^ 4 / 12 := by
  have mem_p : ∀ t, |t| < h → x + t ∈ Set.Ioo (x - h) (x + h) := fun t ht =>
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have mem_m : ∀ t, |t| < h → x - t ∈ Set.Ioo (x - h) (x + h) := fun t ht =>
    ⟨by linarith [le_abs_self t], by linarith [neg_abs_le t]⟩
  -- the derivative `ψ'(t) = f'(x+t) - f'(x-t) - c t - k t³/3` of the comparison function
  have hψ'd : ∀ t, |t| < h →
      HasDerivAt (fun s => f' (x + s) - f' (x - s) - c * s - k * s ^ 3 / 3)
        (G (x + t) + G (x - t) - c - k * t ^ 2) t := by
    intro t ht
    have d1 := HasDerivAt.comp_const_add x t (hG _ (mem_p t ht))
    have d2 := HasDerivAt.comp_const_sub x t (hG _ (mem_m t ht))
    have d3 : HasDerivAt (fun s : ℝ => c * s) c t := by
      simpa using (hasDerivAt_id' t).const_mul c
    have d4 : HasDerivAt (fun s : ℝ => k * s ^ 3 / 3) (k * t ^ 2) t :=
      (((junc_hasDerivAt_cube t).const_mul k).div_const 3).congr_deriv (by ring)
    exact (((d1.fun_sub d2).fun_sub d3).fun_sub d4).congr_deriv (by ring)
  have hanti' : AntitoneOn (fun s => f' (x + s) - f' (x - s) - c * s - k * s ^ 3 / 3)
      (Set.Ico 0 h) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 h)
      (f' := fun t => G (x + t) + G (x - t) - c - k * t ^ 2)
    · intro t ht
      exact (hψ'd t (by rw [abs_of_nonneg ht.1]; exact ht.2)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      exact (hψ'd t (by rw [abs_of_pos ht.1]; exact ht.2)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      linarith [hb t ht]
  have hψ'le : ∀ t ∈ Set.Ico 0 h, f' (x + t) - f' (x - t) - c * t - k * t ^ 3 / 3 ≤ 0 := by
    intro t ht
    have := hanti' ⟨le_refl 0, hh⟩ ht ht.1
    simp only [add_zero, sub_zero, mul_zero] at this
    linarith
  have hanti : AntitoneOn
      (fun s => f (x + s) + f (x - s) - 2 * f x - c * s ^ 2 / 2 - k * s ^ 4 / 12) (Set.Icc 0 h) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 h)
      (f' := fun s => f' (x + s) - f' (x - s) - c * s - k * s ^ 3 / 3)
    · have c1 : ContinuousOn (fun s => f (x + s)) (Set.Icc 0 h) := by
        refine hf.comp (by fun_prop) ?_
        intro s hs
        simp only [Set.mem_Icc] at hs ⊢
        constructor <;> linarith
      have c2 : ContinuousOn (fun s => f (x - s)) (Set.Icc 0 h) := by
        refine hf.comp (by fun_prop) ?_
        intro s hs
        simp only [Set.mem_Icc] at hs ⊢
        constructor <;> linarith
      exact (((c1.add c2).sub continuousOn_const).sub (by fun_prop)).sub (by fun_prop)
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : |t| < h := by rw [abs_of_pos ht.1]; exact ht.2
      have d1 := HasDerivAt.comp_const_add x t (hf' _ (mem_p t ht'))
      have d2 := HasDerivAt.comp_const_sub x t (hf' _ (mem_m t ht'))
      have d3 : HasDerivAt (fun s : ℝ => c * s ^ 2 / 2) (c * t) t :=
        (((junc_hasDerivAt_sq t).const_mul c).div_const 2).congr_deriv (by ring)
      have d4 : HasDerivAt (fun s : ℝ => k * s ^ 4 / 12) (k * t ^ 3 / 3) t :=
        (((junc_hasDerivAt_four t).const_mul k).div_const 12).congr_deriv (by ring)
      exact ((((((d1.fun_add d2).sub_const (2 * f x)).fun_sub d3).fun_sub d4).congr_deriv
        (by ring))).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hψ'le t ⟨ht.1.le, ht.2⟩
  have := hanti ⟨le_refl 0, hh.le⟩ ⟨hh.le, le_refl h⟩ hh.le
  simp only [add_zero, sub_zero] at this
  linarith

/-- The lower-bound version of `junc_master_le`. -/
theorem junc_master_ge {f f' G : ℝ → ℝ} {x h c k : ℝ} (hh : 0 < h)
    (hf : ContinuousOn f (Set.Icc (x - h) (x + h)))
    (hf' : ∀ y ∈ Set.Ioo (x - h) (x + h), HasDerivAt f (f' y) y)
    (hG : ∀ y ∈ Set.Ioo (x - h) (x + h), HasDerivAt f' (G y) y)
    (hb : ∀ t ∈ Set.Ioo 0 h, c + k * t ^ 2 ≤ G (x + t) + G (x - t)) :
    c * h ^ 2 / 2 + k * h ^ 4 / 12 ≤ f (x + h) + f (x - h) - 2 * f x := by
  have := junc_master_le (f := fun y => -f y) (f' := fun y => -f' y) (G := fun y => -G y)
    (c := -c) (k := -k) hh hf.neg (fun y hy => (hf' y hy).fun_neg)
    (fun y hy => (hG y hy).fun_neg)
    (fun t ht => by linarith [hb t ht])
  beta_reduce at this
  linarith

/-! ## Elementary trigonometric inequalities -/

/-- `sin z ≥ z - z³/6` for `z ≥ 0`. -/
lemma junc_sin_ge {z : ℝ} (hz : 0 ≤ z) : z - z ^ 3 / 6 ≤ Real.sin z := by
  have hmono : MonotoneOn (fun w : ℝ => Real.sin w - w + w ^ 3 / 6) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun w => Real.cos w - 1 + w ^ 2 / 2)
    · exact (by fun_prop : Continuous fun w : ℝ => Real.sin w - w + w ^ 3 / 6).continuousOn
    · intro w _
      have h3 : HasDerivAt (fun s : ℝ => s ^ 3 / 6) (w ^ 2 / 2) w :=
        ((junc_hasDerivAt_cube w).div_const 6).congr_deriv (by ring)
      exact (((Real.hasDerivAt_sin w).fun_sub (hasDerivAt_id' w)).fun_add h3).hasDerivWithinAt
    · intro w _
      linarith [(Real.one_sub_sq_div_two_le_cos : 1 - w ^ 2 / 2 ≤ Real.cos w)]
  have := hmono (Set.mem_Ici.mpr le_rfl) hz hz
  simp only [Real.sin_zero] at this
  linarith

/-- `cos z ≤ 1 - z²/2 + z⁴/24` for `z ≥ 0`. -/
lemma junc_cos_le {z : ℝ} (hz : 0 ≤ z) : Real.cos z ≤ 1 - z ^ 2 / 2 + z ^ 4 / 24 := by
  have hmono : MonotoneOn (fun w : ℝ => 1 - w ^ 2 / 2 + w ^ 4 / 24 - Real.cos w) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun w => -w + w ^ 3 / 6 + Real.sin w)
    · exact (by fun_prop :
        Continuous fun w : ℝ => 1 - w ^ 2 / 2 + w ^ 4 / 24 - Real.cos w).continuousOn
    · intro w _
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) w w :=
        ((junc_hasDerivAt_sq w).div_const 2).congr_deriv (by ring)
      have h4 : HasDerivAt (fun s : ℝ => s ^ 4 / 24) (w ^ 3 / 6) w :=
        ((junc_hasDerivAt_four w).div_const 24).congr_deriv (by ring)
      exact (((((hasDerivAt_const w (1 : ℝ)).fun_sub h2).fun_add h4).fun_sub
        (Real.hasDerivAt_cos w)).congr_deriv (by ring)).hasDerivWithinAt
    · intro w hw
      rw [interior_Ici] at hw
      linarith [junc_sin_ge (le_of_lt hw)]
  have := hmono (Set.mem_Ici.mpr le_rfl) hz hz
  simp only [Real.cos_zero] at this
  linarith

/-- Lazarević's inequality `z³ cos z ≤ sin³ z` on `(0, π/2]`. -/
lemma junc_lazarevic {z : ℝ} (hz : 0 < z) (hz2 : z ≤ π / 2) :
    z ^ 3 * Real.cos z ≤ Real.sin z ^ 3 := by
  have hs := junc_sin_ge hz.le
  have hc := junc_cos_le hz.le
  have hz2' : z ≤ 2 := by linarith [Real.pi_lt_d2]
  have hzsq : z ^ 2 ≤ 4 := by nlinarith
  have hpos : 0 ≤ z - z ^ 3 / 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hzsq hz.le]
  have h1 : (z - z ^ 3 / 6) ^ 3 ≤ Real.sin z ^ 3 := pow_le_pow_left₀ hpos hs 3
  have h2 : z ^ 3 * (1 - z ^ 2 / 2 + z ^ 4 / 24) ≤ (z - z ^ 3 / 6) ^ 3 := by
    have e : (z - z ^ 3 / 6) ^ 3 - z ^ 3 * (1 - z ^ 2 / 2 + z ^ 4 / 24) =
        z ^ 7 * (9 - z ^ 2) / 216 := by ring
    have : 0 ≤ z ^ 7 * (9 - z ^ 2) / 216 := by
      apply div_nonneg _ (by norm_num)
      exact mul_nonneg (by positivity) (by linarith)
    linarith
  have h3 : z ^ 3 * Real.cos z ≤ z ^ 3 * (1 - z ^ 2 / 2 + z ^ 4 / 24) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  linarith

/-- `cot z ≥ 1/z - z/2` on `(0, π/2]`. -/
lemma junc_cot_ge {z : ℝ} (hz : 0 < z) (hz2 : z ≤ π / 2) : 1 / z - z / 2 ≤ Real.cot z := by
  have hpi := Real.pi_pos
  have hs : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz (by linarith)
  have hc : 0 ≤ Real.cos z := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hz2⟩
  have hc2 : 1 - z ^ 2 / 2 ≤ Real.cos z := Real.one_sub_sq_div_two_le_cos
  have hs2 : Real.sin z ≤ z := Real.sin_le hz.le
  have hz0 : z ≠ 0 := hz.ne'
  have e : 1 / z - z / 2 = (2 - z ^ 2) / (2 * z) := by field_simp
  rw [e, Real.cot_eq_cos_div_sin, div_le_div_iff₀ (by positivity) hs]
  rcases le_or_gt (z ^ 2) 2 with h | h
  · nlinarith [mul_le_mul_of_nonneg_left hs2 (by linarith : (0 : ℝ) ≤ 2 - z ^ 2),
      mul_le_mul_of_nonneg_left hc2 (by linarith : (0 : ℝ) ≤ 2 * z)]
  · nlinarith [mul_pos (by linarith : (0 : ℝ) < z ^ 2 - 2) hs, mul_nonneg hc hz.le]

/-- Midpoint convexity of `cot`: `2 cot a ≤ cot(a + τ) + cot(a - τ)` for `0 < τ < a ≤ π/2`. -/
lemma junc_cot_midpoint {a τ : ℝ} (hτ : 0 < τ) (hτa : τ < a) (ha : a ≤ π / 2) :
    2 * Real.cot a ≤ Real.cot (a + τ) + Real.cot (a - τ) := by
  have hpi := Real.pi_pos
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : 0 < Real.sin (a + τ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2 : 0 < Real.sin (a - τ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ha⟩
  have hsum : Real.cot (a + τ) + Real.cot (a - τ) =
      2 * Real.sin a * Real.cos a / (Real.sin (a + τ) * Real.sin (a - τ)) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, div_add_div _ _ hs1.ne' hs2.ne']
    congr 1
    rw [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
    linear_combination (2 * Real.sin a * Real.cos a) * Real.sin_sq_add_cos_sq τ
  have hprod : Real.sin (a + τ) * Real.sin (a - τ) = Real.sin a ^ 2 - Real.sin τ ^ 2 := by
    rw [Real.sin_add, Real.sin_sub]
    linear_combination Real.sin a ^ 2 * Real.sin_sq_add_cos_sq τ -
      Real.sin τ ^ 2 * Real.sin_sq_add_cos_sq a
  have hP : 0 < Real.sin (a + τ) * Real.sin (a - τ) := mul_pos hs1 hs2
  have hP2 : Real.sin (a + τ) * Real.sin (a - τ) ≤ Real.sin a ^ 2 := by
    rw [hprod]; nlinarith [sq_nonneg (Real.sin τ)]
  have hl : 2 * Real.cot a = 2 * Real.sin a * Real.cos a / Real.sin a ^ 2 := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  rw [hsum, hl]
  exact div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hsa.le) hca) hP hP2

/-- `(cot z - 1/z)' = -1/sin² z + 1/z²`. -/
lemma junc_hasDerivAt_r {z : ℝ} (hz : 0 < z) (hzπ : z < π) :
    HasDerivAt (fun w => Real.cot w - w⁻¹) (-(Real.sin z ^ 2)⁻¹ + (z ^ 2)⁻¹) z := by
  have hs : Real.sin z ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hz hzπ).ne'
  have e : (fun w => Real.cot w - w⁻¹) = fun w => Real.cos w / Real.sin w - w⁻¹ := by
    funext w
    rw [Real.cot_eq_cos_div_sin]
  rw [e]
  have h1 : -Real.sin z * Real.sin z - Real.cos z * Real.cos z = -1 := by
    linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq z
  exact (((Real.hasDerivAt_cos z).fun_div (Real.hasDerivAt_sin z) hs).fun_sub
    (hasDerivAt_inv hz.ne')).congr_deriv (by rw [h1]; ring)

/-- `(-1/sin² z + 1/z²)' = 2 cos z/sin³ z - 2/z³`. -/
lemma junc_hasDerivAt_r' {z : ℝ} (hz : 0 < z) (hzπ : z < π) :
    HasDerivAt (fun w => -(Real.sin w ^ 2)⁻¹ + (w ^ 2)⁻¹)
      (2 * Real.cos z / Real.sin z ^ 3 - 2 / z ^ 3) z := by
  have hs : Real.sin z ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hz hzπ).ne'
  have hz0 : z ≠ 0 := hz.ne'
  have h1 : HasDerivAt (fun w => Real.sin w ^ 2) (2 * Real.sin z * Real.cos z) z :=
    ((Real.hasDerivAt_sin z).fun_pow 2).congr_deriv (by norm_num)
  have h2 := junc_hasDerivAt_sq z
  exact (((h1.fun_inv (pow_ne_zero 2 hs)).fun_neg).fun_add
    (h2.fun_inv (pow_ne_zero 2 hz0))).congr_deriv (by field_simp; ring)

/-- `(cot z - 1/z)'' ≤ 0` on `(0, π/2]`. -/
lemma junc_r''_nonpos {w : ℝ} (hw : 0 < w) (hw2 : w ≤ π / 2) :
    2 * Real.cos w / Real.sin w ^ 3 - 2 / w ^ 3 ≤ 0 := by
  have hs : 0 < Real.sin w := Real.sin_pos_of_pos_of_lt_pi hw (by linarith [Real.pi_pos])
  have hl := junc_lazarevic hw hw2
  rw [sub_nonpos, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Midpoint concavity of `cot z - 1/z` on `(0, π/2]`. -/
lemma junc_r_midpoint {a τ : ℝ} (hτ : 0 < τ) (hτa : τ < a) (haτ : a + τ ≤ π / 2) :
    (Real.cot (a + τ) - (a + τ)⁻¹) + (Real.cot (a - τ) - (a - τ)⁻¹) -
      2 * (Real.cot a - a⁻¹) ≤ 0 := by
  have hpi := Real.pi_pos
  have := junc_master_le (f := fun w => Real.cot w - w⁻¹)
    (f' := fun w => -(Real.sin w ^ 2)⁻¹ + (w ^ 2)⁻¹)
    (G := fun w => 2 * Real.cos w / Real.sin w ^ 3 - 2 / w ^ 3) (x := a) (h := τ) (c := 0) (k := 0)
    hτ
    (fun y hy => (junc_hasDerivAt_r (by linarith [hy.1]) (by linarith [hy.2])).continuousAt.continuousWithinAt)
    (fun y hy => junc_hasDerivAt_r (by linarith [hy.1]) (by linarith [hy.2]))
    (fun y hy => junc_hasDerivAt_r' (by linarith [hy.1]) (by linarith [hy.2]))
    (fun s hs => by
      have h1 := junc_r''_nonpos (w := a + s) (by linarith [hs.1]) (by linarith [hs.2])
      have h2 := junc_r''_nonpos (w := a - s) (by linarith [hs.2]) (by linarith [hs.1])
      linarith)
  beta_reduce at this
  linarith

/-! ## The second antiderivative `Φ = -Cl₂` of `½ cot(·/2)` -/

lemma junc_sin_half_ne {y : ℝ} (hy : 0 < y) (hy2 : y < 2 * π) : Real.sin (y / 2) ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'

/-- `ℓ'(y) = ½ cot(y/2)` where `ℓ(y) = log(2 sin(y/2))`. -/
lemma junc_hasDerivAt_ell {y : ℝ} (hy : Real.sin (y / 2) ≠ 0) :
    HasDerivAt Cell.ell (Real.cot (y / 2) / 2) y := by
  have h1 : HasDerivAt (fun u : ℝ => 2 * Real.sin (u / 2)) (2 * (Real.cos (y / 2) * (1 / 2))) y :=
    (((hasDerivAt_id' y).div_const 2).sin).const_mul 2
  have h2 := h1.log (mul_ne_zero two_ne_zero hy)
  have e : Real.cot (y / 2) / 2 = 2 * (Real.cos (y / 2) * (1 / 2)) / (2 * Real.sin (y / 2)) := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  rw [e]
  exact h2

lemma junc_measurable_ell : Measurable Cell.ell := by
  unfold Cell.ell
  exact Real.measurable_log.comp (by fun_prop : Continuous fun u : ℝ => 2 * Real.sin (u / 2)).measurable

/-- `Φ' = ℓ` on `(0, 2π)`, where `Φ = -Cl₂`. -/
lemma junc_hasDerivAt_Phi {y : ℝ} (hy0 : 0 < y) (hy : y < 2 * π) :
    HasDerivAt (fun u => -clausen2 u) (Cell.ell y) y := by
  have e : (fun u => -clausen2 u) = fun u => ∫ θ in (0 : ℝ)..u, Cell.ell θ := by
    funext u
    rw [Cell.clausen2_eq_neg_integral, neg_neg]
  rw [e]
  exact intervalIntegral.integral_hasDerivAt_right (Cell.intervalIntegrable_ell 0 y)
    junc_measurable_ell.aestronglyMeasurable.stronglyMeasurableAtFilter
    (junc_hasDerivAt_ell (junc_sin_half_ne hy0 hy)).continuousAt

/-- `κ̄` as a second difference of `Φ = -Cl₂` with step `h = 2π/N`. -/
lemma junc_kbarR_eq (N : ℕ) (m : ℝ) :
    kbarR N m = (N : ℝ) ^ 2 / (2 * π ^ 2) *
      ((-clausen2 (m * (2 * π / N) + 2 * π / N)) + (-clausen2 (m * (2 * π / N) - 2 * π / N)) -
        2 * (-clausen2 (m * (2 * π / N)))) := by
  unfold kbarR
  rw [show 2 * π * m / N = m * (2 * π / N) by ring,
    show 2 * π * (m + 1) / N = m * (2 * π / N) + 2 * π / N by ring,
    show 2 * π * (m - 1) / N = m * (2 * π / N) - 2 * π / N by ring]
  ring

/-- Lower bound for the second difference of `Φ`: `Δ²Φ(x) ≥ h² · ½ cot(x/2)` for
`h ≤ x ≤ π`. -/
lemma junc_delta2_lower {x h : ℝ} (hh : 0 < h) (hxh : h ≤ x) (hxπ : x ≤ π) :
    Real.cot (x / 2) * h ^ 2 / 2 ≤
      (-clausen2 (x + h)) + (-clausen2 (x - h)) - 2 * (-clausen2 x) := by
  have key := junc_master_ge (f := fun u => -clausen2 u) (f' := Cell.ell)
    (G := fun u => Real.cot (u / 2) / 2) (x := x) (h := h) (c := Real.cot (x / 2)) (k := 0) hh
    Cell.continuous_clausen2.neg.continuousOn
    (fun y hy => junc_hasDerivAt_Phi (by linarith [hy.1]) (by linarith [hy.2]))
    (fun y hy => junc_hasDerivAt_ell (junc_sin_half_ne (by linarith [hy.1]) (by linarith [hy.2])))
    (fun t ht => by
      have := junc_cot_midpoint (a := x / 2) (τ := t / 2) (by linarith [ht.1]) (by linarith [ht.2])
        (by linarith)
      rw [show x / 2 + t / 2 = (x + t) / 2 by ring, show x / 2 - t / 2 = (x - t) / 2 by ring] at this
      linarith)
  beta_reduce at key
  linarith

/-- The pointwise bound behind the upper estimate. -/
lemma junc_upper_pointwise {x h t : ℝ} (ht : 0 < t) (hth : t < h) (hxh : h < x)
    (hxπ : x + h ≤ π) :
    Real.cot ((x + t) / 2) / 2 + Real.cot ((x - t) / 2) / 2 ≤
      Real.cot (x / 2) + 2 / (x * (x ^ 2 - h ^ 2)) * t ^ 2 := by
  have hr := junc_r_midpoint (a := x / 2) (τ := t / 2) (by linarith) (by linarith) (by linarith)
  rw [show x / 2 + t / 2 = (x + t) / 2 by ring, show x / 2 - t / 2 = (x - t) / 2 by ring] at hr
  simp only [inv_div] at hr
  have hx : 0 < x := by linarith
  have hxt : 0 < x - t := by linarith
  have hxt' : 0 < x + t := by linarith
  have hD : 0 < x ^ 2 - h ^ 2 := by nlinarith
  have hD' : x ^ 2 - h ^ 2 < x ^ 2 - t ^ 2 := by nlinarith
  have hx0 : x ≠ 0 := hx.ne'
  have hxt0 : x - t ≠ 0 := hxt.ne'
  have hxt0' : x + t ≠ 0 := hxt'.ne'
  have hDt : x ^ 2 - t ^ 2 ≠ 0 := by nlinarith
  have ha : 2 / (x + t) + 2 / (x - t) - 2 * (2 / x) ≤ 2 * (2 / (x * (x ^ 2 - h ^ 2)) * t ^ 2) := by
    have e : 2 / (x + t) + 2 / (x - t) - 2 * (2 / x) = 4 * t ^ 2 / (x * (x ^ 2 - t ^ 2)) := by
      field_simp
      ring
    rw [e]
    calc 4 * t ^ 2 / (x * (x ^ 2 - t ^ 2)) ≤ 4 * t ^ 2 / (x * (x ^ 2 - h ^ 2)) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hx hD)
            (mul_le_mul_of_nonneg_left hD'.le hx.le)
      _ = 2 * (2 / (x * (x ^ 2 - h ^ 2)) * t ^ 2) := by ring
  linarith

/-- Upper bound for the second difference of `Φ` at `x = m h`, `m > 1`, `(m + 1) h ≤ π`. -/
lemma junc_delta2_upper {m h : ℝ} (hh : 0 < h) (hm : 1 < m) (hmh : (m + 1) * h ≤ π) :
    (-clausen2 (m * h + h)) + (-clausen2 (m * h - h)) - 2 * (-clausen2 (m * h)) ≤
      Real.cot (m * h / 2) * h ^ 2 / 2 + h / (6 * m * (m ^ 2 - 1)) := by
  have hpi := Real.pi_pos
  have hxh : h < m * h := by nlinarith
  have hxπ : m * h + h ≤ π := by linarith
  have key := junc_master_le (f := fun u => -clausen2 u) (f' := Cell.ell)
    (G := fun u => Real.cot (u / 2) / 2) (x := m * h) (h := h) (c := Real.cot (m * h / 2))
    (k := 2 / (m * h * ((m * h) ^ 2 - h ^ 2))) hh Cell.continuous_clausen2.neg.continuousOn
    (fun y hy => junc_hasDerivAt_Phi (by linarith [hy.1]) (by linarith [hy.2]))
    (fun y hy => junc_hasDerivAt_ell (junc_sin_half_ne (by linarith [hy.1]) (by linarith [hy.2])))
    (fun t ht => junc_upper_pointwise ht.1 ht.2 hxh hxπ)
  have hm0 : m ≠ 0 := by linarith
  have hh0 : h ≠ 0 := hh.ne'
  have hm1 : m ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < m ^ 2 - 1).ne'
  have hmh1 : (m * h) ^ 2 - h ^ 2 ≠ 0 := by
    rw [show (m * h) ^ 2 - h ^ 2 = h ^ 2 * (m ^ 2 - 1) by ring]
    exact mul_ne_zero (pow_ne_zero 2 hh0) hm1
  have e : 2 / (m * h * ((m * h) ^ 2 - h ^ 2)) * h ^ 4 / 12 = h / (6 * m * (m ^ 2 - 1)) := by
    field_simp
    ring
  beta_reduce at key
  linarith

/-- `½ cot(y/2) - 1/y ≥ -y/8` on `(0, π]`. -/
lemma junc_g2_ge {y : ℝ} (hy : 0 < y) (hyπ : y ≤ π) : -y / 8 ≤ Real.cot (y / 2) / 2 - y⁻¹ := by
  have hc := junc_cot_ge (z := y / 2) (by linarith) (by linarith)
  rw [one_div_div, div_eq_mul_inv] at hc
  linarith

/-- Lower bound for the second difference at `x = h`, via `Φ₂(y) = Φ(y) - y log y`. -/
lemma junc_delta2_one {h : ℝ} (hh : 0 < h) (h2 : 2 * h ≤ π) :
    2 * h * Real.log 2 - h ^ 3 / 8 ≤ 2 * clausen2 h - clausen2 (2 * h) - clausen2 0 := by
  have hpi := Real.pi_pos
  have key := junc_master_ge (f := fun y => -clausen2 y - y * Real.log y)
    (f' := fun y => Cell.ell y - (Real.log y + 1))
    (G := fun y => Real.cot (y / 2) / 2 - y⁻¹) (x := h) (h := h) (c := -h / 4) (k := 0) hh
    ((Cell.continuous_clausen2.neg.sub Real.continuous_mul_log).continuousOn)
    (fun y hy => by
      have hy0 : 0 < y := by linarith [hy.1]
      exact (junc_hasDerivAt_Phi hy0 (by linarith [hy.2])).fun_sub
        (Real.hasDerivAt_mul_log hy0.ne'))
    (fun y hy => by
      have hy0 : 0 < y := by linarith [hy.1]
      exact (junc_hasDerivAt_ell (junc_sin_half_ne hy0 (by linarith [hy.2]))).fun_sub
        ((Real.hasDerivAt_log hy0.ne').add_const 1))
    (fun t ht => by
      have h1 := junc_g2_ge (y := h + t) (by linarith [ht.1]) (by linarith [ht.2])
      have h2 := junc_g2_ge (y := h - t) (by linarith [ht.2]) (by linarith [ht.1])
      linarith)
  beta_reduce at key
  rw [sub_self, show h + h = 2 * h by ring, Real.log_mul two_ne_zero hh.ne'] at key
  linarith

/-! ## The estimates -/

/-- `cot(π m/N) ≤ κ̄(m)` for real `1 ≤ m ≤ N/2`. -/
lemma junc_cot_le_kbarR {N : ℕ} {m : ℝ} (hN : 0 < N) (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    Real.cot (π * m / N) ≤ kbarR N m := by
  have hpi := Real.pi_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi0 : π ≠ 0 := hpi.ne'
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have hh : 0 < 2 * π / N := by positivity
  have hxh : 2 * π / N ≤ m * (2 * π / N) := le_mul_of_one_le_left hh.le hm
  have hxπ : m * (2 * π / N) ≤ π := by
    rw [mul_div_assoc', div_le_iff₀ hNr]
    nlinarith
  have key := junc_delta2_lower hh hxh hxπ
  rw [junc_kbarR_eq]
  have e1 : (N : ℝ) ^ 2 / (2 * π ^ 2) * ((2 * π / N) ^ 2 / 2) = 1 := by
    field_simp
  have e : Real.cot (π * m / N) = (N : ℝ) ^ 2 / (2 * π ^ 2) *
      (Real.cot (m * (2 * π / N) / 2) * (2 * π / N) ^ 2 / 2) := by
    rw [show m * (2 * π / N) / 2 = π * m / N by ring]
    linear_combination (-Real.cot (π * m / N)) * e1
  rw [e]
  exact mul_le_mul_of_nonneg_left key (by positivity)

theorem cot_le_kbarR {N m : ℕ} (hm : 1 ≤ m) (hmN : 2 * (m + 1) ≤ N) :
    Real.cot (π * (m : ℝ) / N) ≤ kbarR N m := by
  have h2 : 2 * m ≤ N := by omega
  exact junc_cot_le_kbarR (by omega) (by exact_mod_cast hm) (by exact_mod_cast h2)

theorem kbarR_sub_cot_le {N m : ℕ} (hm : 2 ≤ m) (hmN : 2 * (m + 1) ≤ N) :
    kbarR N m - Real.cot (π * (m : ℝ) / N) ≤ (N / π) / (6 * m * ((m : ℝ) ^ 2 - 1)) := by
  have hpi := Real.pi_pos
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hpi0 : π ≠ 0 := hpi.ne'
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (1 : ℝ) < m := by linarith
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < (m : ℝ) ^ 2 - 1).ne'
  have hmN' : 2 * ((m : ℝ) + 1) ≤ N := by exact_mod_cast hmN
  have hh : 0 < 2 * π / N := by positivity
  have hmh : ((m : ℝ) + 1) * (2 * π / N) ≤ π := by
    rw [mul_div_assoc', div_le_iff₀ hNr]
    nlinarith
  have key := junc_delta2_upper hh hm' hmh
  rw [junc_kbarR_eq]
  rw [show (m : ℝ) * (2 * π / N) / 2 = π * m / N by ring] at key
  have e1 : (N : ℝ) ^ 2 / (2 * π ^ 2) * ((2 * π / N) ^ 2 / 2) = 1 := by
    field_simp
  have e2 : (N : ℝ) ^ 2 / (2 * π ^ 2) * ((2 * π / N) / (6 * m * ((m : ℝ) ^ 2 - 1))) =
      (N / π) / (6 * m * ((m : ℝ) ^ 2 - 1)) := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / (2 * π ^ 2))
  have e4 : (N : ℝ) ^ 2 / (2 * π ^ 2) * (Real.cot (π * m / N) * (2 * π / N) ^ 2 / 2 +
      2 * π / N / (6 * m * ((m : ℝ) ^ 2 - 1))) =
      Real.cot (π * m / N) + (N / π) / (6 * m * ((m : ℝ) ^ 2 - 1)) := by
    linear_combination Real.cot (π * m / N) * e1 + e2
  linarith

theorem kbarR_one_sub_cot {N : ℕ} (hN : 8 ≤ N) :
    (N / π) * (7 / 24) < kbarR N 1 - Real.cot (π / N) := by
  have hpi := Real.pi_pos
  have hpi2 : π < 315 / 100 := lt_of_lt_of_le Real.pi_lt_d2 (by norm_num)
  have hL : (6931 : ℝ) / 10000 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by linarith
  have hpi0 : π ≠ 0 := hpi.ne'
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have hh : 0 < 2 * π / N := by positivity
  have h2 : 2 * (2 * π / N) ≤ π := by
    rw [mul_div_assoc', div_le_iff₀ hNr]
    nlinarith
  have key := junc_delta2_one hh h2
  have hk : kbarR N 1 = (N : ℝ) ^ 2 / (2 * π ^ 2) *
      (2 * clausen2 (2 * π / N) - clausen2 (2 * (2 * π / N)) - clausen2 0) := by
    unfold kbarR
    rw [show 2 * π * (1 : ℝ) / N = 2 * π / N by ring,
      show 2 * π * ((1 : ℝ) + 1) / N = 2 * (2 * π / N) by ring,
      show 2 * π * ((1 : ℝ) - 1) / N = 0 by ring]
  have hval : (N : ℝ) ^ 2 / (2 * π ^ 2) * (2 * (2 * π / N) * Real.log 2 - (2 * π / N) ^ 3 / 8) =
      2 * (N / π) * Real.log 2 - (π / N) / 2 := by
    field_simp
    ring
  have hlow : 2 * (N / π) * Real.log 2 - (π / N) / 2 ≤ kbarR N 1 := by
    rw [hk, ← hval]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  have hcot : Real.cot (π / N) ≤ N / π := by
    have hz : 0 < π / N := by positivity
    have hz2 : π / N < π / 2 := by
      rw [div_lt_div_iff₀ hNr (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have ht := Real.lt_tan hz hz2
    have hcos : 0 < Real.cos (π / N) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hz2⟩
    have hsin : 0 < Real.sin (π / N) := Real.sin_pos_of_pos_of_lt_pi hz (by linarith)
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at ht
    rw [Real.cot_eq_cos_div_sin, div_le_div_iff₀ hsin hpi]
    have e : π / N * Real.cos (π / N) * N = π * Real.cos (π / N) := by
      field_simp
    nlinarith [mul_lt_mul_of_pos_right ht hNr]
  have hA : (5 / 2 : ℝ) ≤ N / π := by
    rw [le_div_iff₀ hpi]
    nlinarith
  have hB : π / N ≤ 2 / 5 := by
    rw [div_le_iff₀ hNr]
    nlinarith
  have hAL : (N / π) * ((6931 : ℝ) / 10000) ≤ (N / π) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hL.le (by positivity)
  nlinarith

/-! ## Symmetry -/

lemma junc_cot_pi_sub (z : ℝ) : Real.cot (π - z) = -Real.cot z := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

lemma junc_clausen2_two_pi_sub (y : ℝ) : clausen2 (2 * π - y) = -clausen2 y := by
  rw [show 2 * π - y = -y + 2 * π by ring, Cell.clausen2_add_two_pi, Cell.clausen2_neg]

lemma junc_kbarR_N_sub (N : ℕ) [NeZero N] (w : ℝ) : kbarR N (N - w) = -kbarR N w := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold kbarR
  have e1 : 2 * π * ((N : ℝ) - w) / N = 2 * π - 2 * π * w / N := by
    field_simp
  have e2 : 2 * π * ((N : ℝ) - w + 1) / N = 2 * π - 2 * π * (w - 1) / N := by
    field_simp
    ring
  have e3 : 2 * π * ((N : ℝ) - w - 1) / N = 2 * π - 2 * π * (w + 1) / N := by
    field_simp
    ring
  rw [e1, e2, e3, junc_clausen2_two_pi_sub, junc_clausen2_two_pi_sub, junc_clausen2_two_pi_sub]
  ring

lemma junc_kbarR_zero (N : ℕ) : kbarR N 0 = 0 := by
  unfold kbarR
  rw [show 2 * π * ((0 : ℝ) - 1) / N = -(2 * π * (0 + 1) / N) by ring, Cell.clausen2_neg,
    mul_zero, zero_div, Cell.clausen2_zero]
  ring

theorem kap_neg {N : ℕ} [NeZero N] (u : ZMod N) : kap N (-u) = -kap N u := by
  by_cases hu : u = 0
  · subst hu
    simp [kap, Real.cot_eq_cos_div_sin]
  · have : NeZero u := ⟨hu⟩
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    unfold kap
    rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub (ZMod.val_lt u).le]
    rw [show π * ((N : ℝ) - (u.val : ℝ)) / N = π - π * (u.val : ℝ) / N by
      field_simp]
    exact junc_cot_pi_sub _

theorem kbar_neg {N : ℕ} [NeZero N] (u : ZMod N) : kbar N (-u) = -kbar N u := by
  by_cases hu : u = 0
  · subst hu
    simp [kbar, junc_kbarR_zero]
  · have : NeZero u := ⟨hu⟩
    unfold kbar
    rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub (ZMod.val_lt u).le]
    exact junc_kbarR_N_sub N _

theorem ejun_neg {N : ℕ} [NeZero N] (u : ZMod N) : ejun N (-u) = -ejun N u := by
  unfold ejun
  rw [kap_neg, kbar_neg]
  ring

/-! ## Monotonicity and sign -/

/-- `cot` is strictly decreasing on `(0, π)`. -/
lemma junc_cot_lt {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < π) :
    Real.cot q < Real.cot p := by
  have hsp : 0 < Real.sin p := Real.sin_pos_of_pos_of_lt_pi hp (by linarith)
  have hsq : 0 < Real.sin q := Real.sin_pos_of_pos_of_lt_pi (by linarith) hq
  have hsqp : 0 < Real.sin (q - p) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, div_lt_div_iff₀ hsq hsp]
  rw [Real.sin_sub] at hsqp
  linarith

theorem kap_strictAnti {N : ℕ} [NeZero N] (v : ℕ) (hv : 1 ≤ v) (hvN : v + 2 ≤ N) :
    kap N ((v + 1 : ℕ) : ZMod N) < kap N (v : ZMod N) := by
  have hpi := Real.pi_pos
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hvN' : (v : ℝ) + 2 ≤ N := by exact_mod_cast hvN
  unfold kap
  rw [ZMod.val_cast_of_lt (by omega : v + 1 < N), ZMod.val_cast_of_lt (by omega : v < N)]
  push_cast
  apply junc_cot_lt
  · exact div_pos (mul_pos hpi (by linarith)) hNr
  · exact div_lt_div_of_pos_right (by nlinarith) hNr
  · rw [div_lt_iff₀ hNr]
    nlinarith

theorem ejun_nonpos {N : ℕ} [NeZero N] (v : ℕ) (hv : 1 ≤ v) (hvN : 2 * v ≤ N) :
    ejun N (v : ZMod N) ≤ 0 := by
  have h := junc_cot_le_kbarR (N := N) (m := (v : ℝ)) (by omega) (by exact_mod_cast hv)
    (by exact_mod_cast hvN)
  unfold ejun kap kbar
  rw [ZMod.val_cast_of_lt (by omega : v < N)]
  linarith

/-! ## The margin -/

/-- `∑_{m=2}^{K+1} (3m-2)/(6m(m²-1)) = 7/24 - 1/(3(K+2)) - 1/(12(K+1)) - 1/(12(K+2))`. -/
lemma junc_sum_closed (K : ℕ) :
    ∑ m ∈ Finset.Ico 2 (K + 2), (3 * (m : ℝ) - 2) / (6 * m * ((m : ℝ) ^ 2 - 1)) =
      7 / 24 - 1 / (3 * ((K : ℝ) + 2)) - 1 / (12 * ((K : ℝ) + 1)) - 1 / (12 * ((K : ℝ) + 2)) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [show K + 1 + 2 = (K + 2) + 1 by ring, Finset.sum_Ico_succ_top (by omega : 2 ≤ K + 2), ih]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h1 : (K : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (K : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (K : ℝ) + 1 + 2 ≠ 0 := by positivity
    have h4 : (K : ℝ) + 1 + 1 ≠ 0 := by positivity
    have h5 : ((K : ℝ) + 2) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < ((K : ℝ) + 2) ^ 2 - 1).ne'
    push_cast
    field_simp
    ring

lemma junc_sum_le (M : ℕ) :
    ∑ m ∈ Finset.Ico 2 M, (3 * (m : ℝ) - 2) / (6 * m * ((m : ℝ) ^ 2 - 1)) ≤ 7 / 24 := by
  rcases Nat.lt_or_ge M 2 with hM | hM
  · rw [Finset.Ico_eq_empty_of_le hM.le]
    norm_num
  · obtain ⟨K, rfl⟩ : ∃ K, M = K + 2 := ⟨M - 2, by omega⟩
    rw [junc_sum_closed]
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h1 : 0 ≤ 1 / (3 * ((K : ℝ) + 2)) := by positivity
    have h2 : 0 ≤ 1 / (12 * ((K : ℝ) + 1)) := by positivity
    have h3 : 0 ≤ 1 / (12 * ((K : ℝ) + 2)) := by positivity
    linarith

theorem junction_margin {N : ℕ} [NeZero N] (hN : 8 ≤ N) :
    2 * scSum N (ejun N) + fwSum N (ejun N) < -ejun N 1 := by
  have hpi := Real.pi_pos
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h1 : -ejun N 1 = kbarR N 1 - Real.cot (π / N) := by
    have : Fact (1 < N) := ⟨by omega⟩
    simp only [ejun, kap, kbar, ZMod.val_one, Nat.cast_one, mul_one]
    ring
  rw [h1]
  refine lt_of_le_of_lt ?_ (kbarR_one_sub_cot hN)
  have hterm : ∀ m ∈ Finset.Ico 2 (N / 2),
      2 * (((m : ℝ) - 1) * -ejun N (m : ZMod N)) + (m : ℝ) * -ejun N (m : ZMod N) ≤
        (N / π) * ((3 * (m : ℝ) - 2) / (6 * m * ((m : ℝ) ^ 2 - 1))) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmN : 2 * (m + 1) ≤ N := by omega
    have hb := kbarR_sub_cot_le hm.1 hmN
    have he : -ejun N (m : ZMod N) = kbarR N m - Real.cot (π * (m : ℝ) / N) := by
      simp only [ejun, kap, kbar, ZMod.val_cast_of_lt (by omega : m < N)]
      ring
    rw [he]
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hc : 0 ≤ 3 * (m : ℝ) - 2 := by linarith
    calc 2 * (((m : ℝ) - 1) * (kbarR N m - Real.cot (π * m / N))) +
          m * (kbarR N m - Real.cot (π * m / N))
        = (3 * (m : ℝ) - 2) * (kbarR N m - Real.cot (π * m / N)) := by ring
      _ ≤ (3 * (m : ℝ) - 2) * ((N / π) / (6 * m * ((m : ℝ) ^ 2 - 1))) :=
          mul_le_mul_of_nonneg_left hb hc
      _ = (N / π) * ((3 * (m : ℝ) - 2) / (6 * m * ((m : ℝ) ^ 2 - 1))) := by ring
  unfold scSum fwSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc _ ≤ ∑ m ∈ Finset.Ico 2 (N / 2),
        (N / π) * ((3 * (m : ℝ) - 2) / (6 * m * ((m : ℝ) ^ 2 - 1))) := Finset.sum_le_sum hterm
    _ = (N / π) * ∑ m ∈ Finset.Ico 2 (N / 2), (3 * (m : ℝ) - 2) / (6 * m * ((m : ℝ) ^ 2 - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (N / π) * (7 / 24) := mul_le_mul_of_nonneg_left (junc_sum_le _) (by positivity)

end OQP27.ClassB
