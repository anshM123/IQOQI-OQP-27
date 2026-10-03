import OQP27.ClassicalDefs
import OQP27.RigidityClassical

/-!
# The cotangent representation of the classical clock function (module L7)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Lemma `lem:cot` (cotangent representation) and the
proof of Theorem B in its Section 3.

Setting: `d ≥ 1`, `N = 4d`, `κ(u) = cot(π u/N)` on `ℤ_N` (`OQP27.ClassB.kap`), and for `a ∈ ℤ_4^d` the set
`S_a = {x_k : 0 ≤ k < d}`, `x_k = k - d a_k ∈ ℤ_N` (`OQP27.ClassB.Sa`, built from `OQP27.Rig.siteIdx`).
`⟨X, Y⟩ = ∑_{x ∈ X} ∑_{y ∈ Y} κ(x - y)` is the pairing `OQP27.ClassB.pairK`.

What is proved (no hypotheses remain; everything follows from the definitions):

* `card_Sa`, `card_Sa_sub`: `|S_a| = |S_a - d| = d` (`x_k ≡ k mod d`, so `k ↦ x_k` is injective);
* `disjoint_Sa`: `S_a ∩ (S_a - d) = ∅`;
* `clockFa_eq_pairK` (Lemma `lem:cot`): the classical clock function `F(a)` (`OQP27.Rig.clockFa`,
  paper eq. (Fa)) satisfies `F(a) = ⟨S_a, S_a - d⟩/2 - d/2`;
* `FDKZ_eq_pairK`: `F_DKZ = ⟨[0, d), [-d, 0)⟩/2 - d/2` (the case `a = 0`, where `S_0 = [0, d)`);
* `isOneStep_of_Sa_eq`: if `S_a` is an interval `r + [0, d)` of `ℤ_N`, then `a` is one-step
  (`a_k = c + [k ≥ r₀]`, `OQP27.Rig.IsOneStep`).

Proof (as in the paper). For `j < k`, `m = k - j` and `s = a_k - a_j`, the difference `x_k - x_j` is
represented by the integer `m - d s`, and `Re[h_m i^s] = 1/cos(ψ_m - sπ/2)`, `ψ_m = πm/(2d)`. The identity
`cot(θ + π/4) - cot(θ - π/4) = 2/cos(2θ)` with `θ = π(m - d s)/N` gives
`2 Re[h_m i^s] = κ(x_k - x_j + d) - κ(x_k - x_j - d)` (there is no pole because `m ≢ 0 mod d`). As `κ` is
odd, summing over `j < k` gives `2 F(a) = ∑_{j ≠ k} κ(x_k - x_j + d)`, while
`⟨S_a, S_a - d⟩ = ∑_{j, k} κ(x_k - x_j + d)` has the diagonal contribution `d κ(d) = d cot(π/4) = d`.
For `a = 0` the double sum `∑_{j<k} sec ψ_{k-j}` is `∑_{m=1}^{d-1} (d - m) sec ψ_m = F_DKZ`. Finally, if
`S_a = r + [0, d)`, reducing `x_k = r + i_k` modulo `d` and then modulo `4d` determines `a_k` up to the step
at `r₀ = r mod d`.
-/

namespace OQP27.ClassB

open Finset OQP27.Rig

/-- `S_a = {k - d a_k : 0 ≤ k < d} ⊆ ℤ_{4d}`. -/
def Sa {d : ℕ} (a : Fin d → ZMod 4) : Finset (ZMod (4 * d)) :=
  Finset.univ.image fun k : Fin d => siteIdx d k (a k)

/-! ## Trigonometric identities -/

section Trig

open Real

lemma cotr_cot_neg (x : ℝ) : cot (-x) = -cot x := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_neg, sin_neg, div_neg]

lemma cotr_cot_add_int_mul_pi (x : ℝ) (q : ℤ) : cot (x + q * π) = cot x := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_add_int_mul_pi, cos_add_int_mul_pi]
  exact mul_div_mul_left _ _ (zpow_ne_zero q (by norm_num))

/-- `sin(π t/N) ≠ 0` when `N ∤ t`. -/
lemma cotr_sin_ne_zero {N : ℕ} (hN : 0 < N) {t : ℤ} (ht : ¬ (N : ℤ) ∣ t) :
    sin (π * (t : ℝ) / (N : ℝ)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 h
  apply ht
  refine ⟨n, ?_⟩
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hN'] at hn
  have h1 : π * (t : ℝ) = π * ((N : ℝ) * n) := by linear_combination -hn
  have h2 : (t : ℝ) = (N : ℝ) * n := mul_left_cancel₀ pi_ne_zero h1
  exact_mod_cast h2

/-- `cot(θ + π/4) - cot(θ - π/4) = 2/cos(2θ)` away from the poles. -/
lemma cotr_cot_sub (θ : ℝ) (hp : sin (θ + π / 4) ≠ 0) (hq : sin (θ - π / 4) ≠ 0) :
    cot (θ + π / 4) - cot (θ - π / 4) = 2 / cos (2 * θ) := by
  have key : sin (θ + π / 4) * sin (θ - π / 4) = -cos (2 * θ) / 2 := by
    rw [sin_add, sin_sub, cos_pi_div_four, sin_pi_div_four, cos_two_mul]
    have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
    have hsc := sin_sq_add_cos_sq θ
    linear_combination ((sin θ ^ 2 - cos θ ^ 2) / 4) * h2 + (1 / 2) * hsc
  have hnum : cos (θ + π / 4) * sin (θ - π / 4) - sin (θ + π / 4) * cos (θ - π / 4) = -1 := by
    have h := sin_sub (θ - π / 4) (θ + π / 4)
    rw [show θ - π / 4 - (θ + π / 4) = -(π / 2) by ring, sin_neg, sin_pi_div_two] at h
    linear_combination -h
  have hc : cos (2 * θ) ≠ 0 := by
    intro h
    apply mul_ne_zero hp hq
    rw [key, h]; ring
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, div_sub_div _ _ hp hq, hnum, key]
  field_simp

/-- `Re[h_m i^s] = 1/cos(ψ_m - sπ/2)` for `s = 0, 1, 2, 3` (the values `sec ψ_m, csc ψ_m, -sec ψ_m,
-csc ψ_m`). -/
lemma cotr_hm_re (d m s : ℕ) (hs : s < 4) :
    (hm d m * Complex.I ^ s).re = 1 / cos (π * m / (2 * d) - s * π / 2) := by
  have hdef : hm d m = ((1 / cos (π * m / (2 * d)) : ℝ) : ℂ)
      - Complex.I * ((1 / sin (π * m / (2 * d)) : ℝ) : ℂ) := rfl
  have e : ∀ (A B : ℝ) (z : ℂ), (((A : ℂ) - Complex.I * (B : ℂ)) * z).re = A * z.re + B * z.im := by
    intro A B z
    simp [Complex.mul_re]
  rw [hdef, e]
  generalize π * (m : ℝ) / (2 * d) = ψ
  interval_cases s
  · simp
  · simp [cos_sub_pi_div_two]
  · rw [show ψ - ((2 : ℕ) : ℝ) * π / 2 = ψ - π by push_cast; ring, cos_sub_pi]
    have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
    rw [h2]
    simp
  · rw [show ψ - ((3 : ℕ) : ℝ) * π / 2 = (ψ - π) - π / 2 by push_cast; ring, cos_sub_pi_div_two,
      sin_sub_pi]
    have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    rw [h3]
    simp

/-- `κ` evaluated through any integer representative: `κ(t mod N) = cot(π t/N)` (`cot` has period `π`). -/
lemma cotr_kap_intCast {N : ℕ} [NeZero N] (t : ℤ) :
    kap N (t : ZMod N) = cot (π * (t : ℝ) / N) := by
  unfold kap
  have hdvd : (N : ℤ) ∣ (((t : ZMod N).val : ℕ) : ℤ) - t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp
  obtain ⟨q, hq⟩ := hdvd
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hv : (((t : ZMod N).val : ℕ) : ℝ) = (t : ℝ) + N * q := by
    have : (((t : ZMod N).val : ℕ) : ℤ) = t + N * q := by linarith
    exact_mod_cast this
  rw [hv, show π * ((t : ℝ) + N * q) / N = π * t / N + q * π by field_simp,
    cotr_cot_add_int_mul_pi]

/-- `κ(d) = cot(π/4) = 1` for `N = 4d`. -/
lemma cotr_kap_natCast_self {d : ℕ} [NeZero d] : kap (4 * d) (d : ZMod (4 * d)) = 1 := by
  have h := cotr_kap_intCast (N := 4 * d) (d : ℤ)
  simp only [Int.cast_natCast] at h
  rw [h]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [show π * (d : ℝ) / ((4 * d : ℕ) : ℝ) = π / 4 by push_cast; field_simp]
  rw [cot_eq_cos_div_sin, cos_pi_div_four, sin_pi_div_four]
  exact div_self (by positivity)

/-- No pole: `4d ∤ m - d s ± d` when `0 < m < d`. -/
lemma cotr_not_dvd {d m : ℕ} (hm1 : 1 ≤ m) (hmd : m < d) (s e : ℤ) :
    ¬ ((4 * d : ℕ) : ℤ) ∣ (m : ℤ) - d * s + e * d := by
  intro hdvd
  have h1 : (d : ℤ) ∣ (m : ℤ) - d * s + e * d := dvd_trans ⟨4, by push_cast; ring⟩ hdvd
  have h3 : (d : ℤ) ∣ (d : ℤ) * s - e * d := ⟨s - e, by ring⟩
  have h2 : (d : ℤ) ∣ (m : ℤ) := by
    have h4 := dvd_add h1 h3
    rwa [show (m : ℤ) - d * s + e * d + (d * s - e * d) = m by ring] at h4
  have := Int.le_of_dvd (by omega) h2
  omega

/-- The pair identity on integer representatives:
`cot(π(m - ds + d)/N) - cot(π(m - ds - d)/N) = 2 Re[h_m i^s]`, `N = 4d`, `0 < m < d`, `s < 4`. -/
lemma cotr_trig (d m s : ℕ) (hd : 0 < d) (hm1 : 1 ≤ m) (hmd : m < d) (hs : s < 4) :
    cot (π * (((m : ℤ) - d * s + d : ℤ) : ℝ) / ((4 * d : ℕ) : ℝ))
      - cot (π * (((m : ℤ) - d * s - d : ℤ) : ℝ) / ((4 * d : ℕ) : ℝ))
      = 2 * (hm d m * Complex.I ^ s).re := by
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have hN : 0 < 4 * d := by omega
  have hp0 : sin (π * (((m : ℤ) - d * s + d : ℤ) : ℝ) / ((4 * d : ℕ) : ℝ)) ≠ 0 := by
    apply cotr_sin_ne_zero hN
    have := cotr_not_dvd hm1 hmd s 1
    rwa [one_mul] at this
  have hq0 : sin (π * (((m : ℤ) - d * s - d : ℤ) : ℝ) / ((4 * d : ℕ) : ℝ)) ≠ 0 := by
    apply cotr_sin_ne_zero hN
    have := cotr_not_dvd hm1 hmd s (-1)
    rwa [neg_one_mul, ← sub_eq_add_neg] at this
  have h1 : π * (((m : ℤ) - d * s + d : ℤ) : ℝ) / ((4 * d : ℕ) : ℝ)
      = π * ((m : ℝ) - d * s) / (4 * d) + π / 4 := by
    push_cast; field_simp
  have h2 : π * (((m : ℤ) - d * s - d : ℤ) : ℝ) / ((4 * d : ℕ) : ℝ)
      = π * ((m : ℝ) - d * s) / (4 * d) - π / 4 := by
    push_cast; field_simp
  have h3 : 2 * (π * ((m : ℝ) - d * s) / (4 * d)) = π * m / (2 * d) - s * π / 2 := by
    field_simp; ring
  rw [h1] at hp0 ⊢
  rw [h2] at hq0 ⊢
  rw [cotr_cot_sub _ hp0 hq0, h3, cotr_hm_re d m s hs]
  ring

end Trig

/-! ## Reduction modulo `d`: cardinality and disjointness -/

lemma cotr_cast_siteIdx {d : ℕ} (k : Fin d) (u : ZMod 4) :
    ZMod.castHom (dvd_mul_left d 4) (ZMod d) (siteIdx d k u) = ((k : ℕ) : ZMod d) := by
  simp [siteIdx]

lemma cotr_cast_d {d : ℕ} : ZMod.castHom (dvd_mul_left d 4) (ZMod d) (d : ZMod (4 * d)) = 0 := by
  simp

lemma cotr_fin_eq_of_cast {d : ℕ} {j k : Fin d} (h : ((j : ℕ) : ZMod d) = ((k : ℕ) : ZMod d)) :
    j = k := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] at h
  exact Fin.ext h

/-- `k ↦ x_k = k - d a_k` is injective (`x_k ≡ k mod d`). -/
lemma cotr_x_inj {d : ℕ} (a : Fin d → ZMod 4) :
    Function.Injective fun k : Fin d => siteIdx d k (a k) := by
  intro j k h
  have h1 := congrArg (ZMod.castHom (dvd_mul_left d 4) (ZMod d)) h
  simp only [cotr_cast_siteIdx] at h1
  exact cotr_fin_eq_of_cast h1

theorem card_Sa {d : ℕ} [NeZero d] (a : Fin d → ZMod 4) : (Sa a).card = d := by
  rw [Sa, Finset.card_image_of_injective _ (cotr_x_inj a), Finset.card_univ, Fintype.card_fin]

theorem card_Sa_sub {d : ℕ} [NeZero d] (a : Fin d → ZMod 4) :
    ((Sa a).image (· - (d : ZMod (4 * d)))).card = d := by
  rw [Finset.card_image_of_injective _ sub_left_injective, card_Sa]

theorem disjoint_Sa {d : ℕ} [NeZero d] (a : Fin d → ZMod 4) :
    Disjoint (Sa a) ((Sa a).image (· - (d : ZMod (4 * d)))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Sa, Finset.mem_image, Finset.mem_univ, true_and] at hx hx'
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨y, ⟨j, rfl⟩, hj⟩ := hx'
  have hjk : j = k := by
    have h1 := congrArg (ZMod.castHom (dvd_mul_left d 4) (ZMod d)) hj
    rw [map_sub, cotr_cast_siteIdx, cotr_cast_siteIdx, cotr_cast_d, sub_zero] at h1
    exact cotr_fin_eq_of_cast h1
  subst hjk
  have h0 : ((d : ℕ) : ZMod (4 * d)) = 0 := by linear_combination -hj
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hd := NeZero.pos d
  have := Nat.le_of_dvd hd h0
  omega

/-! ## The cotangent representation -/

/-- `⟨S_a, S_a - d⟩ = ∑_{k, j} κ(x_k - x_j + d)`. -/
lemma cotr_pairK_Sa {d : ℕ} [NeZero d] (a : Fin d → ZMod 4) :
    pairK (kap (4 * d)) (Sa a) ((Sa a).image (· - (d : ZMod (4 * d))))
      = ∑ k : Fin d, ∑ j : Fin d, kap (4 * d) (siteIdx d k (a k) - siteIdx d j (a j) + d) := by
  have hinj := cotr_x_inj a
  unfold pairK Sa
  rw [Finset.image_image, Finset.sum_image hinj.injOn]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_image (sub_left_injective.comp hinj).injOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [Function.comp_apply]
  ring

/-- A double sum split into the pairs `j < k` (both orders) and the diagonal. -/
lemma cotr_sum_split {d : ℕ} (G : Fin d → Fin d → ℝ) :
    ∑ k, ∑ j, G k j = (∑ j, ∑ k, if j < k then G k j + G j k else 0) + ∑ k, G k k := by
  have h1 : ∀ k j, G k j = (if j < k then G k j else 0) + (if k < j then G k j else 0)
      + (if j = k then G k j else 0) := by
    intro k j
    rcases lt_trichotomy j k with h | h | h
    · rw [if_pos h, if_neg (lt_asymm h), if_neg (ne_of_lt h)]; ring
    · subst h; rw [if_neg (lt_irrefl _), if_pos rfl]; ring
    · rw [if_neg (lt_asymm h), if_pos h, if_neg (ne_of_gt h)]; ring
  have e1 : (∑ k, ∑ j, if j < k then G k j else 0) = ∑ j, ∑ k, if j < k then G k j else 0 :=
    Finset.sum_comm
  have e3 : (∑ k, ∑ j, if j = k then G k j else 0) = ∑ k, G k k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  calc ∑ k, ∑ j, G k j
      = ∑ k, ∑ j, ((if j < k then G k j else 0) + (if k < j then G k j else 0)
          + (if j = k then G k j else 0)) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => h1 k j
    _ = (∑ k, ∑ j, if j < k then G k j else 0) + (∑ k, ∑ j, if k < j then G k j else 0)
          + ∑ k, ∑ j, if j = k then G k j else 0 := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ j, ∑ k, if j < k then G k j + G j k else 0) + ∑ k, G k k := by
        rw [e1, e3, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> ring

/-- `d (u.val - v.val) = d (u - v).val` in `ℤ_{4d}` for `u, v ∈ ℤ_4`. -/
lemma cotr_d_mul_val_sub {d : ℕ} (u v : ZMod 4) :
    (d : ZMod (4 * d)) * (((u.val : ℕ) : ZMod (4 * d)) - ((v.val : ℕ) : ZMod (4 * d)))
      = (d : ZMod (4 * d)) * (((u - v).val : ℕ) : ZMod (4 * d)) := by
  have h4 : ∀ u v : ZMod 4, u.val + 4 * (if u.val < v.val then 1 else 0) = (u - v).val + v.val := by
    decide
  obtain ⟨c, hc⟩ : ∃ c : ℕ, u.val + 4 * c = (u - v).val + v.val := ⟨_, h4 u v⟩
  have hc' := congrArg (Nat.cast : ℕ → ZMod (4 * d)) hc
  push_cast at hc'
  have hN : (4 : ZMod (4 * d)) * d = 0 := by exact_mod_cast ZMod.natCast_self (4 * d)
  linear_combination (d : ZMod (4 * d)) * hc' - (c : ZMod (4 * d)) * hN

/-- `x_k - x_j` is represented by the integer `(k - j) - d s`, `s = (a_k - a_j).val`. -/
lemma cotr_siteIdx_sub {d : ℕ} (a : Fin d → ZMod 4) (j k : Fin d) (hjk : (j : ℕ) ≤ k) :
    siteIdx d k (a k) - siteIdx d j (a j)
      = (((((k : ℕ) - j : ℕ) : ℤ) - d * ((a k - a j).val : ℤ) : ℤ) : ZMod (4 * d)) := by
  have h := cotr_d_mul_val_sub (d := d) (a k) (a j)
  unfold siteIdx
  push_cast [Nat.cast_sub hjk]
  linear_combination -h

/-- For `j < k`: `κ(x_k - x_j + d) + κ(x_j - x_k + d) = 2 Re[h_{k-j} i^{a_k - a_j}]`. -/
lemma cotr_pair_term {d : ℕ} [NeZero d] (a : Fin d → ZMod 4) (j k : Fin d) (hjk : j < k) :
    kap (4 * d) (siteIdx d k (a k) - siteIdx d j (a j) + d)
      + kap (4 * d) (siteIdx d j (a j) - siteIdx d k (a k) + d)
      = 2 * (hm d ((k : ℕ) - j) * Complex.I ^ (a k - a j).val).re := by
  have hjk' : (j : ℕ) < k := hjk
  have hkd := k.isLt
  have hdiff := cotr_siteIdx_sub a j k hjk'.le
  have e1 : siteIdx d k (a k) - siteIdx d j (a j) + d
      = (((((k : ℕ) - j : ℕ) : ℤ) - d * ((a k - a j).val : ℤ) + d : ℤ) : ZMod (4 * d)) := by
    rw [hdiff]; push_cast; ring
  have e2 : siteIdx d j (a j) - siteIdx d k (a k) + d
      = ((-((((k : ℕ) - j : ℕ) : ℤ) - d * ((a k - a j).val : ℤ) - d) : ℤ) : ZMod (4 * d)) := by
    rw [show siteIdx d j (a j) - siteIdx d k (a k) = -(siteIdx d k (a k) - siteIdx d j (a j)) by ring,
      hdiff]
    push_cast; ring
  rw [e1, e2, cotr_kap_intCast, cotr_kap_intCast, Int.cast_neg, mul_neg, neg_div, cotr_cot_neg,
    ← sub_eq_add_neg]
  exact cotr_trig d ((k : ℕ) - j) (a k - a j).val (NeZero.pos d) (by omega) (by omega)
    (ZMod.val_lt _)

/-- **Lemma `lem:cot`** (cotangent representation): `F(a) = ⟨S_a, S_a - d⟩/2 - d/2`. -/
theorem clockFa_eq_pairK {d : ℕ} [NeZero d] (a : Fin d → ZMod 4) :
    clockFa a = pairK (kap (4 * d)) (Sa a) ((Sa a).image (· - (d : ZMod (4 * d)))) / 2 - (d : ℝ) / 2 := by
  rw [cotr_pairK_Sa, cotr_sum_split]
  have hdiag : ∑ k : Fin d, kap (4 * d) (siteIdx d k (a k) - siteIdx d k (a k) + d) = d := by
    simp [cotr_kap_natCast_self]
  have hpair : (∑ j : Fin d, ∑ k : Fin d, if j < k then
      kap (4 * d) (siteIdx d k (a k) - siteIdx d j (a j) + d)
        + kap (4 * d) (siteIdx d j (a j) - siteIdx d k (a k) + d) else 0) = 2 * clockFa a := by
    unfold clockFa
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · exact cotr_pair_term a j k h
    · ring
  rw [hdiag, hpair]
  ring

/-! ## The DKZ value -/

/-- `∑_{0 ≤ j < k < d} f(k - j) = ∑_{m=1}^{d-1} (d - m) f(m)`. -/
lemma cotr_pair_count (d : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ range d, ∑ k ∈ range d, (if j < k then f (k - j) else 0)
      = ∑ m ∈ Ico 1 d, ((d : ℝ) - m) * f m := by
  have h1 : ∀ j ∈ range d, ∑ k ∈ range d, (if j < k then f (k - j) else 0)
      = ∑ m ∈ Ico 1 d, (if j + m < d then f m else 0) := by
    intro j _
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    apply Finset.sum_nbij' (fun k => k - j) (fun m => m + j)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hk ⊢
      omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hm ⊢
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Ico] at hm
      omega
    · intro k _
      rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hf : ((range d).filter fun j => j + m < d) = range (d - m) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, card_range]
  rw [Finset.mem_Ico] at hm
  rw [Nat.cast_sub hm.2.le]

lemma cotr_fin_double_sum (d : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ j : Fin d, ∑ k : Fin d, g j k = ∑ j ∈ range d, ∑ k ∈ range d, g j k := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ k : Fin d, g j k) d]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Fin.sum_univ_eq_sum_range (g j) d

open Real in
/-- `F(0) = F_DKZ`. -/
lemma cotr_clockFa_zero (d : ℕ) [NeZero d] : clockFa (0 : Fin d → ZMod 4) = FDKZ d := by
  unfold clockFa FDKZ
  have h0 : ∀ j k : Fin d,
      (if j < k then (hm d ((k : ℕ) - j)
        * Complex.I ^ ((0 : Fin d → ZMod 4) k - (0 : Fin d → ZMod 4) j).val).re else 0)
      = (fun (j k : ℕ) => if j < k then 1 / cos (π * ((k - j : ℕ) : ℝ) / (2 * d)) else 0) j k := by
    intro j k
    simp only [Pi.zero_apply, sub_self, ZMod.val_zero, Fin.lt_def]
    split_ifs
    · rw [cotr_hm_re _ _ 0 (by norm_num)]
      simp
    · rfl
  have hc := cotr_pair_count d (fun m => 1 / cos (π * (m : ℝ) / (2 * d)))
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h0 j k]
  exact (cotr_fin_double_sum d
    (fun (j k : ℕ) => if j < k then 1 / cos (π * ((k - j : ℕ) : ℝ) / (2 * d)) else 0)).trans hc

/-- `S_0 = [0, d)`. -/
lemma cotr_Sa_zero (d : ℕ) : Sa (0 : Fin d → ZMod 4) = ico 0 d := by
  ext x
  simp only [Sa, ico, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range, siteIdx,
    Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero, zero_add]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- `[0, d) - d = [-d, 0)`. -/
lemma cotr_ico_image_sub (d : ℕ) :
    (ico (0 : ZMod (4 * d)) d).image (· - (d : ZMod (4 * d))) = ico (-(d : ZMod (4 * d))) d := by
  unfold ico
  rw [Finset.image_image]
  refine Finset.image_congr fun i _ => ?_
  simp only [Function.comp_apply, zero_add]
  ring

/-- `F_DKZ = ⟨[0, d), [-d, 0)⟩/2 - d/2`. -/
theorem FDKZ_eq_pairK (d : ℕ) [NeZero d] :
    FDKZ d = pairK (kap (4 * d)) (ico 0 d) (ico (-(d : ZMod (4 * d))) d) / 2 - (d : ℝ) / 2 := by
  rw [← cotr_clockFa_zero d, clockFa_eq_pairK, cotr_Sa_zero, cotr_ico_image_sub]

/-! ## Intervals come from one-step configurations -/

lemma cotr_zmod4_of_dvd {d : ℕ} (hd : 0 < d) (n : ℕ) (h : ((d * n : ℕ) : ZMod (4 * d)) = 0) :
    ((n : ℕ) : ZMod 4) = 0 := by
  rw [ZMod.natCast_eq_zero_iff] at h ⊢
  rw [mul_comm 4 d] at h
  exact Nat.dvd_of_mul_dvd_mul_left hd h

/-- If `S_a` is an interval `r + [0, d)` of `ℤ_{4d}`, then `a` is one-step: with `r mod 4d = q d + r₀`,
`0 ≤ r₀ < d`, one has `a_k = -(q + 1) + [k ≥ r₀]`. -/
theorem isOneStep_of_Sa_eq {d : ℕ} [NeZero d] (a : Fin d → ZMod 4) (r : ZMod (4 * d))
    (h : Sa a = ico r d) : IsOneStep a := by
  have hd : 0 < d := NeZero.pos d
  obtain ⟨q, hq⟩ : ∃ q, q = r.val / d := ⟨_, rfl⟩
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = r.val % d := ⟨_, rfl⟩
  have hRqr : r.val = q * d + r₀ := by rw [hq, hr₀]; exact (Nat.div_add_mod' r.val d).symm
  have hr₀d : r₀ < d := by rw [hr₀]; exact Nat.mod_lt _ hd
  have hrcast : r = ((q * d + r₀ : ℕ) : ZMod (4 * d)) := by
    rw [← hRqr, ZMod.natCast_zmod_val]
  refine ⟨-((q : ZMod 4) + 1), r₀, hr₀d, fun k => ?_⟩
  have hk : siteIdx d k (a k) ∈ ico r d := by
    rw [← h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  obtain ⟨i, hi, hxi⟩ : ∃ i, i < d ∧ r + (i : ZMod (4 * d)) = siteIdx d k (a k) := by
    simpa [ico] using hk
  -- reduction modulo `d`: `k ≡ r₀ + i`
  have hmodd : (r₀ + i) % d = (k : ℕ) := by
    have h1 := congrArg (ZMod.castHom (dvd_mul_left d 4) (ZMod d)) hxi
    rw [cotr_cast_siteIdx, map_add, hrcast, map_natCast, map_natCast] at h1
    have h2 : ((r₀ + i : ℕ) : ZMod d) = ((k : ℕ) : ZMod d) := by
      rw [← h1]
      push_cast
      simp
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt k.isLt] at h2
    exact h2
  have hcase : (r₀ + i < d ∧ (k : ℕ) = r₀ + i) ∨ (d ≤ r₀ + i ∧ (k : ℕ) + d = r₀ + i) := by
    by_cases hlt : r₀ + i < d
    · left
      exact ⟨hlt, by rw [← hmodd, Nat.mod_eq_of_lt hlt]⟩
    · right
      have hle : d ≤ r₀ + i := not_lt.1 hlt
      refine ⟨hle, ?_⟩
      rw [← hmodd, Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
      omega
  have hA : (((a k).val : ℕ) : ZMod 4) = a k := ZMod.natCast_zmod_val (a k)
  rw [hrcast] at hxi
  unfold siteIdx at hxi
  push_cast at hxi
  -- reduction modulo `4d`: `d (a_k + q + [k < r₀]) ≡ 0`
  by_cases hrk : r₀ ≤ (k : ℕ)
  · have hki : (k : ℕ) = r₀ + i := by
      rcases hcase with hc | hc
      · exact hc.2
      · omega
    have hkc : ((k : ℕ) : ZMod (4 * d)) = (r₀ : ZMod (4 * d)) + i := by
      rw [hki]; push_cast; ring
    have key : ((d * ((a k).val + q) : ℕ) : ZMod (4 * d)) = 0 := by
      push_cast
      linear_combination hxi + hkc
    have h4 := cotr_zmod4_of_dvd hd _ key
    push_cast at h4
    rw [hA] at h4
    rw [if_pos hrk]
    linear_combination h4
  · have hki : (k : ℕ) + d = r₀ + i := by
      rcases hcase with hc | hc
      · omega
      · exact hc.2
    have hkc : ((k : ℕ) : ZMod (4 * d)) + d = (r₀ : ZMod (4 * d)) + i := by
      have := congrArg (Nat.cast : ℕ → ZMod (4 * d)) hki
      push_cast at this
      exact this
    have key : ((d * ((a k).val + q + 1) : ℕ) : ZMod (4 * d)) = 0 := by
      push_cast
      linear_combination hxi + hkc
    have h4 := cotr_zmod4_of_dvd hd _ key
    push_cast at h4
    rw [hA] at h4
    rw [if_neg hrk]
    linear_combination h4

end OQP27.ClassB
