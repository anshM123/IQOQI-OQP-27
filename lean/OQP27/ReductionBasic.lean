import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.ZMod.Basic

/-!
# OQP 27B, module L2 (reduction), part 1: roots of unity and the scalar identities

Paper: `publish/CGLMP/paper-classical-all-d/main.tex` (cited below as "the paper").

Notation of the paper, Section 2: `w = e^{2πi/d}`, `z = e^{2πi/(4d)}` (so `z^4 = w`, `z^d = i`),
`ψ_m = π m / (2d)`, `h_m = sec ψ_m - i csc ψ_m`, and the Fourier coefficients `c_n = -1/(1 - w^{-n})`
of the residue function `m(t)` (paper eq. (mfourier)).

Main results (all PROVED, no hypotheses):
* `OQP27.Red.val_eq_fourier`: paper eq. (mfourier), `m(t) = (d-1)/2 + ∑_{n=1}^{d-1} c_n w^{n t}`.
* `OQP27.Red.hd_mul_zd_pow`: `h_n z^n = -4 c_n` (the identity `4 c_n z^{-n} = -h_n` of the paper's appendix).
* `OQP27.Red.cd_reflect`: `c_{d-n} = conj c_n`.
* `OQP27.Red.secd_reflect`: `sec ψ_{d-m} = csc ψ_m`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate

noncomputable section

/-- `w = exp(2πi/d)`. -/
def wd (d : ℕ) : ℂ := exp (2 * Real.pi * I / d)

/-- `z = exp(2πi/(4d))`. -/
def zd (d : ℕ) : ℂ := exp (2 * Real.pi * I / (4 * d))

/-- `ψ_m = π m / (2d)`. -/
def psi (d m : ℕ) : ℝ := Real.pi * m / (2 * d)

/-- `sec ψ_m`. -/
def secd (d m : ℕ) : ℝ := 1 / Real.cos (psi d m)

/-- `csc ψ_m`. -/
def cscd (d m : ℕ) : ℝ := 1 / Real.sin (psi d m)

/-- `h_m = sec ψ_m - i csc ψ_m`. -/
def hd (d m : ℕ) : ℂ := (secd d m : ℂ) - I * (cscd d m : ℂ)

/-- `c_n = -1/(1 - w^{-n})`, the Fourier coefficients of the residue function. -/
def cd (d n : ℕ) : ℂ := -1 / (1 - (wd d ^ n)⁻¹)

variable {d : ℕ}

/-! ### Roots of unity -/

lemma wd_prim (hd : d ≠ 0) : IsPrimitiveRoot (wd d) d := Complex.isPrimitiveRoot_exp d hd

lemma wd_pow_d (hd : d ≠ 0) : wd d ^ d = 1 := (wd_prim hd).pow_eq_one

lemma wd_ne_zero : wd d ≠ 0 := Complex.exp_ne_zero _

lemma zd_ne_zero : zd d ≠ 0 := Complex.exp_ne_zero _

lemma zd_pow_four (hd : d ≠ 0) : zd d ^ 4 = wd d := by
  rw [zd, wd, ← Complex.exp_nat_mul]
  congr 1
  have : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd
  field_simp
  push_cast
  ring

lemma zd_pow_d (hd : d ≠ 0) : zd d ^ d = I := by
  rw [zd, ← Complex.exp_nat_mul]
  have : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have e : (d : ℂ) * (2 * Real.pi * I / (4 * d)) = Real.pi / 2 * I := by
    field_simp
    ring
  rw [e, Complex.exp_pi_div_two_mul_I]

lemma zd_pow_eq (hd : d ≠ 0) (n : ℕ) : zd d ^ n = exp ((psi d n : ℂ) * I) := by
  rw [zd, ← Complex.exp_nat_mul, psi]
  congr 1
  have : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd
  push_cast
  field_simp
  ring

lemma wd_pow_eq (hd : d ≠ 0) (n : ℕ) : wd d ^ n = zd d ^ (4 * n) := by
  rw [pow_mul, zd_pow_four hd]

/-- Conjugation of `exp (x i)` for real `x`. -/
lemma conj_exp_ofReal_mul_I (x : ℝ) : conj (exp ((x : ℂ) * I)) = (exp ((x : ℂ) * I))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal]

lemma wd_eq_exp : wd d = exp (((2 * Real.pi / d : ℝ) : ℂ) * I) := by
  rw [wd]
  congr 1
  push_cast
  ring

lemma zd_eq_exp : zd d = exp (((2 * Real.pi / (4 * d) : ℝ) : ℂ) * I) := by
  rw [zd]
  congr 1
  push_cast
  ring

lemma conj_wd : conj (wd d) = (wd d)⁻¹ := by
  rw [wd_eq_exp, conj_exp_ofReal_mul_I]

lemma conj_zd : conj (zd d) = (zd d)⁻¹ := by
  rw [zd_eq_exp, conj_exp_ofReal_mul_I]

lemma star_zd_mul : star (zd d) * zd d = 1 := by
  rw [Complex.star_def, conj_zd, inv_mul_cancel₀ zd_ne_zero]

lemma star_wd_mul : star (wd d) * wd d = 1 := by
  rw [Complex.star_def, conj_wd, inv_mul_cancel₀ wd_ne_zero]

lemma conj_wd_pow (n : ℕ) : conj (wd d ^ n) = (wd d ^ n)⁻¹ := by
  rw [map_pow, conj_wd, inv_pow]

lemma conj_zd_pow (n : ℕ) : conj (zd d ^ n) = (zd d ^ n)⁻¹ := by
  rw [map_pow, conj_zd, inv_pow]

/-- Powers of `w` only depend on the exponent modulo `d`. -/
lemma wd_pow_mod (hd : d ≠ 0) (k : ℕ) : wd d ^ (k % d) = wd d ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k d, pow_add, pow_mul, wd_pow_d hd, one_pow, mul_one]

lemma wd_pow_ne_one (hd : d ≠ 0) {n : ℕ} (h0 : n ≠ 0) (hn : n < d) : wd d ^ n ≠ 1 :=
  (wd_prim hd).pow_ne_one_of_pos_of_lt h0 hn

/-- The character `t ↦ w^{n t}` of `ℤ/d`, written with `ZMod.val`. -/
lemma wd_pow_val_add [NeZero d] (n : ℕ) (a b : ZMod d) :
    wd d ^ (n * (a + b).val) = wd d ^ (n * a.val) * wd d ^ (n * b.val) := by
  have hd : d ≠ 0 := NeZero.ne d
  rw [← pow_add, ← mul_add, ZMod.val_add, mul_comm n, mul_comm n, pow_mul, pow_mul,
    wd_pow_mod hd]

lemma wd_pow_val_neg [NeZero d] (n : ℕ) (a : ZMod d) :
    wd d ^ (n * (-a).val) = (wd d ^ (n * a.val))⁻¹ := by
  have hd : d ≠ 0 := NeZero.ne d
  have h := wd_pow_val_add n a (-a)
  rw [add_neg_cancel, ZMod.val_zero, mul_zero, pow_zero] at h
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)

lemma wd_pow_val_sub [NeZero d] (n : ℕ) (a b : ZMod d) :
    wd d ^ (n * (a - b).val) = wd d ^ (n * a.val) * (wd d ^ (n * b.val))⁻¹ := by
  rw [sub_eq_add_neg, wd_pow_val_add, wd_pow_val_neg]

lemma wd_pow_val_neg_one [NeZero d] (n : ℕ) :
    wd d ^ (n * (-1 : ZMod d).val) = (wd d ^ n)⁻¹ := by
  rw [wd_pow_val_neg]
  rcases Nat.lt_or_ge d 2 with h | h
  · -- `d = 1`: every power of `w` is `1`
    have hd1 : d = 1 := by have := NeZero.ne d; omega
    subst hd1
    have hw : wd 1 = 1 := by simpa using wd_pow_d (d := 1) one_ne_zero
    simp [hw]
  · have : Fact (1 < d) := ⟨by omega⟩
    rw [ZMod.val_one, mul_one]

/-! ### Fourier expansion of the residue function (paper eq. (mfourier)) -/

lemma sum_range_cast_mul_two (n : ℕ) : (∑ s ∈ range n, (s : ℂ)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- `(1 - q) ∑_{s<n} s q^s = ∑_{s<n} q^s - n q^n + q^n - 1`. -/
lemma one_sub_mul_sum_mul_pow (q : ℂ) (n : ℕ) :
    (1 - q) * ∑ s ∈ range n, (s : ℂ) * q ^ s
      = ∑ s ∈ range n, q ^ s - n * q ^ n + q ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    push_cast
    ring

/-- `∑_{s<d} s w^{-ns} = d c_n` for `1 ≤ n ≤ d - 1`. -/
lemma sum_mul_pow_inv (hd : d ≠ 0) {n : ℕ} (h0 : n ≠ 0) (hn : n < d) :
    ∑ s ∈ range d, (s : ℂ) * ((wd d ^ n)⁻¹) ^ s = d * cd d n := by
  set q : ℂ := (wd d ^ n)⁻¹ with hq
  have hq1 : q ≠ 1 := by
    rw [hq]
    intro h
    exact wd_pow_ne_one hd h0 hn (inv_eq_one.1 h)
  have hqd : q ^ d = 1 := by
    rw [hq, inv_pow, ← pow_mul, mul_comm, pow_mul, wd_pow_d hd, one_pow, inv_one]
  have hgeom : ∑ s ∈ range d, q ^ s = 0 := by
    rw [geom_sum_eq hq1, hqd, sub_self, zero_div]
  have key := one_sub_mul_sum_mul_pow q d
  rw [hgeom, hqd] at key
  have h1q : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [cd, ← hq]
  field_simp
  linear_combination key

/-- Orthogonality of the characters of `ℤ/d`, in the form used below. -/
lemma sum_pow_ratio (hd : d ≠ 0) {s t : ℕ} (hs : s < d) (ht : t < d) :
    ∑ n ∈ range d, (wd d ^ t * (wd d ^ s)⁻¹) ^ n = if s = t then (d : ℂ) else 0 := by
  split_ifs with hst
  · subst hst
    rw [mul_inv_cancel₀ (pow_ne_zero _ wd_ne_zero)]
    simp
  · have hr : wd d ^ t * (wd d ^ s)⁻¹ ≠ 1 := by
      intro h
      rw [mul_inv_eq_one₀ (pow_ne_zero _ wd_ne_zero)] at h
      exact hst ((wd_prim hd).pow_inj ht hs h).symm
    have hrd : (wd d ^ t * (wd d ^ s)⁻¹) ^ d = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm t, mul_comm s, pow_mul, pow_mul,
        wd_pow_d hd, one_pow, one_pow, inv_one, mul_one]
    rw [geom_sum_eq hr, hrd, sub_self, zero_div]

lemma sum_range_eq_add_Ico {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ range n, f k = f 0 + ∑ k ∈ Ico 1 n, f k := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]

/-- **Paper eq. (mfourier).** For `t ∈ ℤ/d`, `m(t) = (d-1)/2 + ∑_{n=1}^{d-1} c_n w^{n t}`. -/
theorem val_eq_fourier [NeZero d] (t : ZMod d) :
    (t.val : ℂ) = ((d : ℂ) - 1) / 2 + ∑ n ∈ Ico 1 d, cd d n * wd d ^ (n * t.val) := by
  have hd : d ≠ 0 := NeZero.ne d
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have ht : t.val < d := ZMod.val_lt t
  -- the full inversion formula with `ĉ_n = (1/d) ∑_s s w^{-ns}`
  have inv : ∑ n ∈ range d, ((1 / (d : ℂ)) * ∑ s ∈ range d, (s : ℂ) * ((wd d ^ n)⁻¹) ^ s)
      * wd d ^ (n * t.val) = t.val := by
    have e1 : ∀ n s : ℕ, ((wd d ^ n)⁻¹) ^ s * wd d ^ (n * t.val)
        = (wd d ^ t.val * (wd d ^ s)⁻¹) ^ n := by
      intro n s
      rw [inv_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm n s,
        mul_comm t.val n]
      ring
    calc ∑ n ∈ range d, ((1 / (d : ℂ)) * ∑ s ∈ range d, (s : ℂ) * ((wd d ^ n)⁻¹) ^ s)
          * wd d ^ (n * t.val)
        = (1 / (d : ℂ)) * ∑ s ∈ range d, (s : ℂ) *
            ∑ n ∈ range d, (wd d ^ t.val * (wd d ^ s)⁻¹) ^ n := by
          rw [mul_sum]
          simp_rw [mul_sum, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun s _ => sum_congr rfl fun n _ => ?_
          rw [← e1]
          ring
      _ = (1 / (d : ℂ)) * ∑ s ∈ range d, (s : ℂ) * (if s = t.val then (d : ℂ) else 0) := by
          congr 1
          refine sum_congr rfl fun s hs => ?_
          rw [sum_pow_ratio hd (mem_range.1 hs) ht]
      _ = t.val := by
          simp_rw [mul_ite, mul_zero]
          rw [sum_ite_eq' (range d) t.val, if_pos (mem_range.2 ht)]
          field_simp
  rw [← inv, sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero hd)]
  congr 1
  · -- the constant term
    simp only [pow_zero, inv_one, one_pow, mul_one, zero_mul]
    have h2 : ∑ s ∈ range d, (s : ℂ) = d * (d - 1) / 2 := by
      rw [eq_div_iff two_ne_zero]
      exact sum_range_cast_mul_two d
    rw [h2]
    field_simp
  · refine sum_congr rfl fun n hn => ?_
    rw [mem_Ico] at hn
    rw [sum_mul_pow_inv hd (by omega) hn.2]
    field_simp

/-! ### Trigonometric identities -/

lemma psi_pos {m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) : 0 < psi d m := by
  unfold psi
  have : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)
  have : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  positivity

lemma psi_lt_pi_div_two {m : ℕ} (hm : m < d) : psi d m < Real.pi / 2 := by
  unfold psi
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  have : (m : ℝ) < d := Nat.cast_lt.2 hm
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  have := Real.pi_pos
  nlinarith

lemma cos_psi_pos {m : ℕ} (hm : m < d) : 0 < Real.cos (psi d m) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 ≤ psi d m := by unfold psi; positivity
    linarith [Real.pi_pos]
  · exact psi_lt_pi_div_two hm

lemma sin_psi_pos {m : ℕ} (hm0 : m ≠ 0) (hm : m < d) : 0 < Real.sin (psi d m) := by
  apply Real.sin_pos_of_pos_of_lt_pi (psi_pos (by omega) hm0)
  linarith [psi_lt_pi_div_two hm, Real.pi_pos]

lemma secd_pos {m : ℕ} (hm : m < d) : 0 < secd d m := by
  unfold secd
  exact one_div_pos.2 (cos_psi_pos hm)

lemma cscd_pos {m : ℕ} (hm0 : m ≠ 0) (hm : m < d) : 0 < cscd d m := by
  unfold cscd
  exact one_div_pos.2 (sin_psi_pos hm0 hm)

lemma psi_reflect (hd : d ≠ 0) {m : ℕ} (hm : m ≤ d) :
    psi d (d - m) = Real.pi / 2 - psi d m := by
  unfold psi
  have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  rw [Nat.cast_sub hm]
  field_simp

/-- `sec ψ_{d-m} = csc ψ_m`. -/
theorem secd_reflect (hd : d ≠ 0) {m : ℕ} (hm : m ≤ d) : secd d (d - m) = cscd d m := by
  rw [secd, cscd, psi_reflect hd hm, Real.cos_pi_div_two_sub]

/-- `csc ψ_{d-m} = sec ψ_m`. -/
theorem cscd_reflect (hd : d ≠ 0) {m : ℕ} (hm : m ≤ d) : cscd d (d - m) = secd d m := by
  rw [secd, cscd, psi_reflect hd hm, Real.sin_pi_div_two_sub]

lemma alg_hz (C S : ℂ) (hC : C ≠ 0) (hS : S ≠ 0) (hpy : C ^ 2 + S ^ 2 = 1)
    (hne : 1 - (C - S * I) ^ 4 ≠ 0) :
    (1 / C - I * (1 / S)) * (C + S * I) = -4 * (-1 / (1 - (C - S * I) ^ 4)) := by
  have hne' : 1 - (C - I * S) ^ 4 ≠ 0 := by rwa [mul_comm I S]
  field_simp
  linear_combination (S * (C + I * S) * (1 - (C - I * S) ^ 4) - 4 * C * S
      - I * (C - I * S) ^ 2 * ((C + I * S) * (C - I * S) + 1) * S ^ 2) * Complex.I_sq
    + (I * (C - I * S) ^ 2 * ((C + I * S) * (C - I * S) + 1)) * hpy

/-- **The identity `4 c_n z^{-n} = -h_n`** of the paper's appendix, in the form `h_n z^n = -4 c_n`
(`1 ≤ n ≤ d - 1`). -/
theorem hd_mul_zd_pow (hd0 : d ≠ 0) {n : ℕ} (h0 : n ≠ 0) (hn : n < d) :
    hd d n * zd d ^ n = -4 * cd d n := by
  set x : ℝ := psi d n with hx
  have hC : Real.cos x ≠ 0 := (cos_psi_pos hn).ne'
  have hS : Real.sin x ≠ 0 := (sin_psi_pos h0 hn).ne'
  have hCc : Complex.cos x ≠ 0 := by rw [← Complex.ofReal_cos]; exact_mod_cast hC
  have hSc : Complex.sin x ≠ 0 := by rw [← Complex.ofReal_sin]; exact_mod_cast hS
  have hu : zd d ^ n = Complex.cos x + Complex.sin x * I := by
    rw [zd_pow_eq hd0, ← hx, Complex.exp_mul_I]
  have hw : wd d ^ n = (Complex.cos x + Complex.sin x * I) ^ 4 := by
    rw [wd_pow_eq hd0, mul_comm, pow_mul, hu]
  have hpy : Complex.cos x ^ 2 + Complex.sin x ^ 2 = 1 := Complex.cos_sq_add_sin_sq x
  have hinv : (Complex.cos x + Complex.sin x * I)⁻¹ = Complex.cos x - Complex.sin x * I := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination hpy - Complex.sin x ^ 2 * Complex.I_sq
  have hw1 : (wd d ^ n)⁻¹ = (Complex.cos x - Complex.sin x * I) ^ 4 := by
    rw [hw, ← inv_pow, hinv]
  have hne : (1 : ℂ) - (Complex.cos x - Complex.sin x * I) ^ 4 ≠ 0 := by
    rw [← hw1, sub_ne_zero]
    intro h
    exact wd_pow_ne_one hd0 h0 hn (inv_eq_one.1 h.symm)
  rw [hd, cd, hu, hw1, secd, cscd, ← hx]
  push_cast
  exact alg_hz _ _ hCc hSc hpy hne

/-- `c_{d-n} = conj c_n` (`n ≤ d`). -/
theorem cd_reflect (hd : d ≠ 0) {n : ℕ} (hn : n ≤ d) : cd d (d - n) = conj (cd d n) := by
  have h1 : (wd d ^ (d - n))⁻¹ = wd d ^ n := by
    have : wd d ^ (d - n) * wd d ^ n = 1 := by rw [← pow_add, Nat.sub_add_cancel hn, wd_pow_d hd]
    exact inv_eq_of_mul_eq_one_right this
  rw [cd, cd, h1, map_div₀, map_neg, map_one, map_sub, map_one, map_inv₀, conj_wd_pow, inv_inv]

end

end OQP27.Red
