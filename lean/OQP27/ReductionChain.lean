import OQP27.ReductionBasic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Field

/-!
# OQP 27B, module L2 (reduction), part 2: the chain form of the CGLMP expression

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 2.1 (Lemma 2.1, eq. (S)) and
Section 2.2 (eqs. (mfourier), (Strace)).

* `OQP27.Red.cglmp`: the CGLMP expression, paper eq. (cglmp), of a behaviour `p x y a b`
  (settings `x, y : Fin 2`, where `0` is setting 1 and `1` is setting 2; outcomes in `ℤ/d`).
* `OQP27.Red.cglmp_eq_chain` (**Lemma 2.1**): `I_d = 4 - 2 S / (d - 1)` for every normalised behaviour,
  with `S` the chain sum of paper eq. (S).
* `OQP27.Red.IsPVM`, `OQP27.Red.probME`: projective measurements and the maximally entangled
  probabilities `p(a,b|x,y) = Tr(A_{x,a}^T B_{y,b}) / D`.
* `OQP27.Red.chainR`: the chain unitaries `R_1 = U_2, R_2 = (U'_2)^T, R_3 = U_1, R_4 = (U'_1)^T` of paper
  eq. (chainR) (indexed by `ℤ/4`, `R_{s+1} = chainR s`).
* `OQP27.Red.chainS_trace` (**paper eq. (Strace)**): `S = 2(d-1) + ∑_{n=1}^{d-1} c_n Λ_n(R)`.

Everything is PROVED; there are no hypotheses.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

/-! ### Behaviours and the CGLMP expression -/

/-- A behaviour `p x y a b`: settings `x y : Fin 2` (`0` is setting 1, `1` is setting 2), outcomes in
`ℤ/d`. -/
abbrev Behaviour (d : ℕ) := Fin 2 → Fin 2 → ZMod d → ZMod d → ℝ

variable {d : ℕ} [NeZero d]

/-- `P(A_x = B_y + k)`. -/
def pAB (p : Behaviour d) (x y : Fin 2) (k : ZMod d) : ℝ :=
  ∑ a, ∑ b, if a = b + k then p x y a b else 0

/-- `P(B_y = A_x + k)`. -/
def pBA (p : Behaviour d) (x y : Fin 2) (k : ZMod d) : ℝ :=
  ∑ a, ∑ b, if b = a + k then p x y a b else 0

/-- **The CGLMP expression**, paper eq. (cglmp):
`I_d = ∑_{k=0}^{⌊d/2⌋-1} (1 - 2k/(d-1)) ([P(A_1 = B_1 + k) + P(B_1 = A_2 + k + 1) + P(A_2 = B_2 + k)
+ P(B_2 = A_1 + k)] - [P(A_1 = B_1 - k - 1) + P(B_1 = A_2 - k) + P(A_2 = B_2 - k - 1)
+ P(B_2 = A_1 - k - 1)])`. -/
def cglmp (p : Behaviour d) : ℝ :=
  ∑ k ∈ range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
    ((pAB p 0 0 k + pBA p 1 0 ((k : ZMod d) + 1) + pAB p 1 1 k + pBA p 0 1 k)
      - (pAB p 0 0 (-(k : ZMod d) - 1) + pBA p 1 0 (-(k : ZMod d)) + pAB p 1 1 (-(k : ZMod d) - 1)
          + pBA p 0 1 (-(k : ZMod d) - 1)))

/-- `E m(A_x - B_y + e)`, `m(t) ∈ {0, …, d-1}` the residue. -/
def emAB (p : Behaviour d) (x y : Fin 2) (e : ZMod d) : ℝ :=
  ∑ a, ∑ b, ((a - b + e).val : ℝ) * p x y a b

/-- `E m(B_y - A_x + e)`. -/
def emBA (p : Behaviour d) (x y : Fin 2) (e : ZMod d) : ℝ :=
  ∑ a, ∑ b, ((b - a + e).val : ℝ) * p x y a b

/-- **The chain sum** of paper eq. (S): with `X_1 = A_2, Y_1 = B_2, X_2 = A_1, Y_2 = B_1`,
`S = E m(X_1 - Y_1) + E m(Y_1 - X_2) + E m(X_2 - Y_2) + E m(Y_2 - X_1 - 1)`. -/
def chainS (p : Behaviour d) : ℝ :=
  emAB p 1 1 0 + emBA p 0 1 0 + emAB p 0 0 0 + emBA p 1 0 (-1)

/-- A behaviour is normalised if every `p(·,·|x,y)` sums to `1`. -/
def IsNormalised (p : Behaviour d) : Prop := ∀ x y, ∑ a, ∑ b, p x y a b = 1

/-! ### Lemma 2.1 -/

/-- Sum over `ℤ/d` as a sum over `range d`. -/
lemma sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (φ : ZMod d → M) :
    ∑ t : ZMod d, φ t = ∑ j ∈ range d, φ (j : ZMod d) := by
  refine Finset.sum_nbij' (fun t => t.val) (fun j => (j : ZMod d)) ?_ ?_ ?_ ?_ ?_
  · intro t _
    exact mem_range.2 (ZMod.val_lt t)
  · intro j _
    exact mem_univ _
  · intro t _
    exact ZMod.natCast_zmod_val t
  · intro j hj
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hj)]
  · intro t _
    rw [ZMod.natCast_zmod_val]

/-- Folding a sum over `range d` at its middle. -/
lemma sum_range_fold (φ : ℕ → ℝ) (d : ℕ) :
    ∑ j ∈ range d, φ j = ∑ k ∈ range (d / 2), (φ k + φ (d - 1 - k))
      + (if d % 2 = 1 then φ (d / 2) else 0) := by
  set h := d / 2 with hh
  rcases Nat.even_or_odd d with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hrh : r = h := by omega
    subst hrh
    have hmod : d % 2 = 0 := by omega
    rw [if_neg (by omega), add_zero, sum_add_distrib, hr, sum_range_add]
    congr 1
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have := mem_range.1 hk
    congr 1
    omega
  · have hrh : r = h := by omega
    subst hrh
    rw [if_pos (by omega), sum_add_distrib, hr]
    rw [show 2 * h + 1 = h + (h + 1) by ring, sum_range_add, sum_range_succ', add_zero]
    have e1 : ∑ k ∈ range h, φ (h + (k + 1)) = ∑ k ∈ range h, φ (h + (h + 1) - 1 - k) := by
      rw [← sum_range_reflect (fun k => φ (h + (k + 1))) h]
      refine sum_congr rfl fun k hk => ?_
      have := mem_range.1 hk
      congr 1
      omega
    rw [e1]
    ring

/-- The difference distribution `q(t) = P(D(A_x, B_y) = t)`. -/
def diffDist (p : Behaviour d) (x y : Fin 2) (D : ZMod d → ZMod d → ZMod d) (t : ZMod d) : ℝ :=
  ∑ a, ∑ b, if D a b = t then p x y a b else 0

lemma sum_diffDist (p : Behaviour d) (x y : Fin 2) (D : ZMod d → ZMod d → ZMod d) :
    ∑ t, diffDist p x y D t = ∑ a, ∑ b, p x y a b := by
  unfold diffDist
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_ite_eq]
  simp

lemma sum_val_mul_diffDist (p : Behaviour d) (x y : Fin 2) (D : ZMod d → ZMod d → ZMod d) :
    ∑ t, (t.val : ℝ) * diffDist p x y D t = ∑ a, ∑ b, ((D a b).val : ℝ) * p x y a b := by
  unfold diffDist
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  simp_rw [mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp

/-- The key folding identity behind Lemma 2.1: for a function `g` on `ℤ/d` (`d ≥ 2`),
`∑_{k<⌊d/2⌋} (1 - 2k/(d-1)) (g(k) - g(-k-1)) = ∑_t (1 - 2 m(t)/(d-1)) g(t)`. -/
lemma fold_identity (hd : 2 ≤ d) (g : ZMod d → ℝ) :
    ∑ k ∈ range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) * (g k - g (-(k : ZMod d) - 1))
      = ∑ t : ZMod d, (1 - 2 * (t.val : ℝ) / ((d : ℝ) - 1)) * g t := by
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [sum_zmod_eq_sum_range]
  have hval : ∀ j ∈ range d, ((j : ZMod d).val : ℝ) = j := by
    intro j hj
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hj)]
  have hR : ∑ j ∈ range d, (1 - 2 * (((j : ZMod d).val : ℕ) : ℝ) / ((d : ℝ) - 1)) * g (j : ZMod d)
      = ∑ j ∈ range d, (1 - 2 * (j : ℝ) / ((d : ℝ) - 1)) * g (j : ZMod d) :=
    sum_congr rfl fun j hj => by rw [hval j hj]
  rw [hR, sum_range_fold (fun j => (1 - 2 * (j : ℝ) / ((d : ℝ) - 1)) * g (j : ZMod d)) d]
  have hmid : (if d % 2 = 1 then (1 - 2 * ((d / 2 : ℕ) : ℝ) / ((d : ℝ) - 1)) * g ((d / 2 : ℕ) : ZMod d)
      else 0) = 0 := by
    split_ifs with h
    · have : ((d / 2 : ℕ) : ℝ) * 2 = (d : ℝ) - 1 := by
        have h2 : (d / 2) * 2 + 1 = d := by omega
        have h3 : (((d / 2) * 2 + 1 : ℕ) : ℝ) = d := by rw [h2]
        push_cast at h3
        linarith
      rw [show 2 * ((d / 2 : ℕ) : ℝ) / ((d : ℝ) - 1) = 1 by rw [div_eq_one_iff_eq hd1]; linarith]
      ring
    · rfl
  rw [hmid, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < d / 2 := mem_range.1 hk
  have hkd : k + 1 ≤ d := by omega
  have hcast : ((d - 1 - k : ℕ) : ℝ) = (d : ℝ) - 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hz : ((d - 1 - k : ℕ) : ZMod d) = -(k : ZMod d) - 1 := by
    have e : ((d - 1 - k + k + 1 : ℕ) : ZMod d) = 0 := by
      rw [show d - 1 - k + k + 1 = d by omega, ZMod.natCast_self]
    push_cast at e
    linear_combination e
  rw [hcast, hz]
  field_simp
  ring

/-- `P(A_x = B_y + k)` is the difference distribution of `A_x - B_y`. -/
lemma pAB_eq (p : Behaviour d) (x y : Fin 2) (k : ZMod d) :
    pAB p x y k = diffDist p x y (fun a b => a - b) k := by
  unfold pAB diffDist
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  congr 1
  apply propext
  constructor <;> intro h
  · rw [h]; ring
  · rw [← h]; ring

/-- `P(B_y = A_x + k)` is the difference distribution of `B_y - A_x + e` at `k + e`. -/
lemma pBA_eq (p : Behaviour d) (x y : Fin 2) (e k : ZMod d) :
    pBA p x y k = diffDist p x y (fun a b => b - a + e) (k + e) := by
  unfold pBA diffDist
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  congr 1
  apply propext
  constructor <;> intro h
  · rw [h]; ring
  · linear_combination h

lemma pair_identity (hd : 2 ≤ d) (p : Behaviour d) (x y : Fin 2) (D : ZMod d → ZMod d → ZMod d)
    (hp : ∑ a, ∑ b, p x y a b = 1) :
    ∑ k ∈ range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
        (diffDist p x y D k - diffDist p x y D (-(k : ZMod d) - 1))
      = 1 - 2 / ((d : ℝ) - 1) * ∑ a, ∑ b, ((D a b).val : ℝ) * p x y a b := by
  rw [fold_identity hd, ← sum_val_mul_diffDist]
  simp_rw [sub_mul, one_mul]
  rw [sum_sub_distrib, sum_diffDist, hp, mul_sum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  ring

/-- **Lemma 2.1 of the paper.** For every normalised behaviour, `I_d = 4 - 2 S/(d-1)`. -/
theorem cglmp_eq_chain (hd : 2 ≤ d) (p : Behaviour d) (hp : IsNormalised p) :
    cglmp p = 4 - 2 / ((d : ℝ) - 1) * chainS p := by
  have e1 := pair_identity hd p 0 0 (fun a b => a - b) (hp 0 0)
  have e2 := pair_identity hd p 1 0 (fun a b => b - a + (-1)) (hp 1 0)
  have e3 := pair_identity hd p 1 1 (fun a b => a - b) (hp 1 1)
  have e4 := pair_identity hd p 0 1 (fun a b => b - a + 0) (hp 0 1)
  have h2 : ∀ k : ℕ, pBA p 1 0 ((k : ZMod d) + 1) = diffDist p 1 0 (fun a b => b - a + (-1)) k := by
    intro k
    rw [pBA_eq p 1 0 (-1)]
    congr 1
    ring
  have h2' : ∀ k : ℕ, pBA p 1 0 (-(k : ZMod d)) =
      diffDist p 1 0 (fun a b => b - a + (-1)) (-(k : ZMod d) - 1) := by
    intro k
    rw [pBA_eq p 1 0 (-1)]
    congr 1
    ring
  have h4 : ∀ k : ZMod d, pBA p 0 1 k = diffDist p 0 1 (fun a b => b - a + 0) k := by
    intro k
    rw [pBA_eq p 0 1 0, add_zero]
  unfold cglmp chainS emAB emBA
  simp_rw [pAB_eq, h2, h2', h4]
  have : ∀ k : ℕ, (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
      ((diffDist p 0 0 (fun a b => a - b) k + diffDist p 1 0 (fun a b => b - a + (-1)) k
        + diffDist p 1 1 (fun a b => a - b) k + diffDist p 0 1 (fun a b => b - a + 0) k)
      - (diffDist p 0 0 (fun a b => a - b) (-(k : ZMod d) - 1)
        + diffDist p 1 0 (fun a b => b - a + (-1)) (-(k : ZMod d) - 1)
        + diffDist p 1 1 (fun a b => a - b) (-(k : ZMod d) - 1)
        + diffDist p 0 1 (fun a b => b - a + 0) (-(k : ZMod d) - 1)))
      = (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
          (diffDist p 0 0 (fun a b => a - b) k - diffDist p 0 0 (fun a b => a - b) (-(k : ZMod d) - 1))
        + (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
          (diffDist p 1 0 (fun a b => b - a + (-1)) k
            - diffDist p 1 0 (fun a b => b - a + (-1)) (-(k : ZMod d) - 1))
        + (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
          (diffDist p 1 1 (fun a b => a - b) k - diffDist p 1 1 (fun a b => a - b) (-(k : ZMod d) - 1))
        + (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
          (diffDist p 0 1 (fun a b => b - a + 0) k
            - diffDist p 0 1 (fun a b => b - a + 0) (-(k : ZMod d) - 1)) := by
    intro k; ring
  rw [sum_congr rfl fun k _ => this k]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, e1, e2, e3, e4]
  simp only [add_zero]
  ring

/-! ### Fourier form of the chain sum -/

/-- `T_n(x,y) = ∑_{a,b} w^{n a} conj(w^{n b}) p(a,b|x,y) = E w^{n (A_x - B_y)}`. -/
def charSum (p : Behaviour d) (x y : Fin 2) (n : ℕ) : ℂ :=
  ∑ a, ∑ b, (wd d ^ (n * a.val) * conj (wd d ^ (n * b.val))) * (p x y a b : ℂ)

lemma wd_pow_val_diff (n : ℕ) (a b e : ZMod d) :
    wd d ^ (n * (a - b + e).val)
      = (wd d ^ (n * a.val) * conj (wd d ^ (n * b.val))) * wd d ^ (n * e.val) := by
  rw [wd_pow_val_add, wd_pow_val_sub, conj_wd_pow]

lemma fourier_sum (p : Behaviour d) (x y : Fin 2) (D : ZMod d → ZMod d → ZMod d)
    (hp : ∑ a, ∑ b, p x y a b = 1) :
    ∑ a, ∑ b, ((D a b).val : ℂ) * (p x y a b : ℂ) = ((d : ℂ) - 1) / 2
      + ∑ n ∈ Ico 1 d, cd d n * ∑ a, ∑ b, wd d ^ (n * (D a b).val) * (p x y a b : ℂ) := by
  have hp' : ∑ a, ∑ b, (p x y a b : ℂ) = 1 := by exact_mod_cast hp
  calc ∑ a, ∑ b, ((D a b).val : ℂ) * (p x y a b : ℂ)
      = ∑ a, ∑ b, (((d : ℂ) - 1) / 2 * (p x y a b : ℂ)
          + ∑ n ∈ Ico 1 d, cd d n * (wd d ^ (n * (D a b).val) * (p x y a b : ℂ))) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        rw [val_eq_fourier (D a b), add_mul, sum_mul]
        congr 1
        refine sum_congr rfl fun n _ => ?_
        ring
    _ = ((d : ℂ) - 1) / 2 * ∑ a, ∑ b, (p x y a b : ℂ)
          + ∑ n ∈ Ico 1 d, cd d n * ∑ a, ∑ b, wd d ^ (n * (D a b).val) * (p x y a b : ℂ) := by
        simp only [sum_add_distrib, mul_sum]
        congr 1
        calc ∑ a, ∑ b, ∑ n ∈ Ico 1 d, cd d n * (wd d ^ (n * (D a b).val) * (p x y a b : ℂ))
            = ∑ a, ∑ n ∈ Ico 1 d, ∑ b, cd d n * (wd d ^ (n * (D a b).val) * (p x y a b : ℂ)) :=
              sum_congr rfl fun a _ => sum_comm
          _ = _ := sum_comm
    _ = _ := by rw [hp', mul_one]

lemma charSum_shift_AB (p : Behaviour d) (x y : Fin 2) (e : ZMod d) (n : ℕ) :
    ∑ a, ∑ b, wd d ^ (n * (a - b + e).val) * (p x y a b : ℂ)
      = wd d ^ (n * e.val) * charSum p x y n := by
  unfold charSum
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [wd_pow_val_diff]
  ring

lemma charSum_shift_BA (p : Behaviour d) (x y : Fin 2) (e : ZMod d) (n : ℕ) :
    ∑ a, ∑ b, wd d ^ (n * (b - a + e).val) * (p x y a b : ℂ)
      = wd d ^ (n * e.val) * conj (charSum p x y n) := by
  unfold charSum
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [wd_pow_val_diff, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

lemma emAB_fourier (p : Behaviour d) (x y : Fin 2) (e : ZMod d) (hp : ∑ a, ∑ b, p x y a b = 1) :
    (emAB p x y e : ℂ) = ((d : ℂ) - 1) / 2
      + ∑ n ∈ Ico 1 d, cd d n * wd d ^ (n * e.val) * charSum p x y n := by
  unfold emAB
  push_cast
  rw [fourier_sum p x y (fun a b => a - b + e) hp]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [charSum_shift_AB, mul_assoc]

lemma emBA_fourier (p : Behaviour d) (x y : Fin 2) (e : ZMod d) (hp : ∑ a, ∑ b, p x y a b = 1) :
    (emBA p x y e : ℂ) = ((d : ℂ) - 1) / 2
      + ∑ n ∈ Ico 1 d, cd d n * wd d ^ (n * e.val) * conj (charSum p x y n) := by
  unfold emBA
  push_cast
  rw [fourier_sum p x y (fun a b => b - a + e) hp]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [charSum_shift_BA, mul_assoc]

/-- The chain sum in Fourier form (first half of paper eq. (Strace)). -/
theorem chainS_fourier (p : Behaviour d) (hp : IsNormalised p) :
    (chainS p : ℂ) = 2 * ((d : ℂ) - 1) + ∑ n ∈ Ico 1 d, cd d n *
      (charSum p 1 1 n + conj (charSum p 0 1 n) + charSum p 0 0 n
        + (wd d ^ n)⁻¹ * conj (charSum p 1 0 n)) := by
  unfold chainS
  push_cast
  rw [emAB_fourier p 1 1 0 (hp 1 1), emBA_fourier p 0 1 0 (hp 0 1), emAB_fourier p 0 0 0 (hp 0 0),
    emBA_fourier p 1 0 (-1) (hp 1 0)]
  simp only [ZMod.val_zero, mul_zero, pow_zero, mul_one, wd_pow_val_neg_one]
  rw [show ∀ a b c e : ℂ, ((d : ℂ) - 1) / 2 + a + (((d : ℂ) - 1) / 2 + b) + (((d : ℂ) - 1) / 2 + c)
      + (((d : ℂ) - 1) / 2 + e) = 2 * ((d : ℂ) - 1) + (a + b + c + e) by intros; ring]
  congr 1
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  ring

/-! ### Projective measurements and the maximally entangled state -/

section Quantum

open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A projection: Hermitian and idempotent. -/
def IsProj (P : Matrix ι ι ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- A projective measurement (PVM) with outcomes in `ℤ/d`: projections summing to `1`. -/
def IsPVM (P : ZMod d → Matrix ι ι ℂ) : Prop := (∀ a, IsProj (P a)) ∧ ∑ a, P a = 1

/-- The outcomes of a PVM are mutually orthogonal. -/
lemma IsPVM.mul_eq_zero {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) {a b : ZMod d} (hab : a ≠ b) :
    P a * P b = 0 := by
  have hH : ∀ c, (P c)ᴴ = P c := fun c => (hP.1 c).1
  have hI : ∀ c, P c * P c = P c := fun c => (hP.1 c).2
  have key : ∀ b c, c ≠ b → P c * P b = 0 := by
    intro b
    have e1 : ∀ c, (P c * P b)ᴴ * (P c * P b) = P b * P c * P b := by
      intro c
      rw [conjTranspose_mul, hH, hH, mul_assoc, ← mul_assoc (P c) (P c), hI, ← mul_assoc]
    have e2 : ∑ c, P b * P c * P b = P b := by
      rw [← sum_mul, ← mul_sum, hP.2, mul_one, hI]
    have hsum : ∑ c ∈ univ.erase b, P b * P c * P b = 0 := by
      have h3 : P b * P b * P b = P b := by rw [hI, hI]
      rw [← sum_erase_add _ _ (mem_univ b), h3] at e2
      exact add_eq_right.1 e2
    have htr : ∑ c ∈ univ.erase b, trace ((P c * P b)ᴴ * (P c * P b)) = 0 := by
      rw [← trace_sum]
      simp_rw [e1]
      rw [hsum, trace_zero]
    have hnn : ∀ c ∈ univ.erase b, 0 ≤ trace ((P c * P b)ᴴ * (P c * P b)) :=
      fun c _ => (posSemidef_conjTranspose_mul_self _).trace_nonneg
    intro c hc
    have := (sum_eq_zero_iff_of_nonneg hnn).1 htr c (mem_erase.2 ⟨hc, mem_univ c⟩)
    exact trace_conjTranspose_mul_self_eq_zero_iff.1 this
  exact key b a hab

/-- Products of PVM-diagonal matrices. -/
lemma IsPVM.sum_mul_sum {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) (f g : ZMod d → ℂ) :
    (∑ a, f a • P a) * (∑ b, g b • P b) = ∑ a, (f a * g a) • P a := by
  rw [Finset.sum_mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single a]
  · rw [smul_mul_smul_comm, (hP.1 a).2]
  · intro b _ hba
    rw [smul_mul_smul_comm, hP.mul_eq_zero (Ne.symm hba), smul_zero]
  · intro h
    exact absurd (mem_univ a) h

lemma IsPVM.sum_smul_conjTranspose {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) (f : ZMod d → ℂ) :
    (∑ a, f a • P a)ᴴ = ∑ a, conj (f a) • P a := by
  rw [conjTranspose_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [conjTranspose_smul, (hP.1 a).1.eq]
  rfl

/-- The unitary `U = ∑_a w^a P_a` of a PVM. -/
def pvmU (P : ZMod d → Matrix ι ι ℂ) : Matrix ι ι ℂ := ∑ a, (wd d ^ a.val) • P a

lemma pvmU_pow {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) (n : ℕ) :
    pvmU P ^ n = ∑ a, (wd d ^ (n * a.val)) • P a := by
  induction n with
  | zero => simp [hP.2]
  | succ n ih =>
    rw [pow_succ, ih, pvmU, hP.sum_mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [← pow_add]
    congr 2
    ring

lemma pvmU_pow_conjTranspose {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) (n : ℕ) :
    (pvmU P ^ n)ᴴ = ∑ a, conj (wd d ^ (n * a.val)) • P a := by
  rw [pvmU_pow hP, hP.sum_smul_conjTranspose]

lemma pvmU_unitary {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) : (pvmU P)ᴴ * pvmU P = 1 := by
  have h := pvmU_pow_conjTranspose hP 1
  rw [pow_one] at h
  rw [h, pvmU, hP.sum_mul_sum, ← hP.2]
  refine sum_congr rfl fun a _ => ?_
  rw [one_mul, conj_wd_pow, inv_mul_cancel₀ (pow_ne_zero _ wd_ne_zero), one_smul]

lemma pvmU_pow_d {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) : pvmU P ^ d = 1 := by
  rw [pvmU_pow hP, ← hP.2]
  refine sum_congr rfl fun a _ => ?_
  rw [pow_mul, wd_pow_d (NeZero.ne d), one_pow, one_smul]

/-- **Maximally entangled probabilities** `p(a,b|x,y) = Tr(A_{x,a}^T B_{y,b}) / D`. -/
def probME (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) : Behaviour d :=
  fun x y a b => (trace ((A x a)ᵀ * B y b)).re / Fintype.card ι

omit [DecidableEq ι] in
/-- `Tr(Pᵀ Q)` is real for Hermitian `P, Q`. -/
lemma conj_trace_transpose_mul {P Q : Matrix ι ι ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    conj (trace (Pᵀ * Q)) = trace (Pᵀ * Q) := by
  rw [← Complex.star_def, ← trace_conjTranspose, conjTranspose_mul, hQ.eq,
    conjTranspose_transpose_eq_transpose_conjTranspose, hP.eq, trace_mul_comm]

lemma probME_cast (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) (hA : ∀ x, IsPVM (A x))
    (hB : ∀ y, IsPVM (B y)) (x y : Fin 2) (a b : ZMod d) :
    (probME A B x y a b : ℂ) = trace ((A x a)ᵀ * B y b) / Fintype.card ι := by
  unfold probME
  push_cast
  congr 1
  exact Complex.conj_eq_iff_re.1 (conj_trace_transpose_mul ((hA x).1 a).1 ((hB y).1 b).1)

lemma probME_normalised [Nonempty ι] (A B : Fin 2 → ZMod d → Matrix ι ι ℂ)
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) : IsNormalised (probME A B) := by
  intro x y
  have hD : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e : ∑ a, ∑ b, trace ((A x a)ᵀ * B y b) = Fintype.card ι := by
    calc ∑ a, ∑ b, trace ((A x a)ᵀ * B y b) = ∑ a, trace ((A x a)ᵀ * ∑ b, B y b) := by
          simp_rw [mul_sum, trace_sum]
      _ = trace ((∑ a, A x a)ᵀ) := by
          rw [(hB y).2, transpose_sum, trace_sum]
          simp
      _ = Fintype.card ι := by rw [(hA x).2, transpose_one, trace_one]
  have h : ((∑ a, ∑ b, probME A B x y a b : ℝ) : ℂ) = 1 := by
    push_cast
    simp_rw [probME_cast A B hA hB]
    simp_rw [← sum_div]
    rw [e, div_self hD]
  exact_mod_cast h

/-- `T_n(x,y) = Tr((U_x^n)ᵀ (U'_y{}^n)ᴴ) / D` for the maximally entangled probabilities. -/
lemma charSum_probME (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) (hA : ∀ x, IsPVM (A x))
    (hB : ∀ y, IsPVM (B y)) (x y : Fin 2) (n : ℕ) :
    charSum (probME A B) x y n
      = trace ((pvmU (A x) ^ n)ᵀ * (pvmU (B y) ^ n)ᴴ) / Fintype.card ι := by
  unfold charSum
  simp_rw [probME_cast A B hA hB]
  rw [pvmU_pow (hA x), pvmU_pow_conjTranspose (hB y), transpose_sum, Finset.sum_mul_sum, trace_sum,
    sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [trace_sum, sum_div]
  refine sum_congr rfl fun b _ => ?_
  rw [transpose_smul, smul_mul_smul_comm, trace_smul, smul_eq_mul]
  ring

/-! ### Chain unitaries, links, and paper eq. (Strace) -/

/-- A function on `ℤ/4` given by its four values. -/
def vec4 {M : Type*} (a b c e : M) : ZMod 4 → M :=
  fun s => if s = 0 then a else if s = 1 then b else if s = 2 then c else e

section vec4
variable {M : Type*} (a b c e : M)
@[simp] lemma vec4_zero : vec4 a b c e 0 = a := if_pos rfl
@[simp] lemma vec4_one : vec4 a b c e 1 = b := by
  unfold vec4; rw [if_neg (by decide), if_pos rfl]
@[simp] lemma vec4_two : vec4 a b c e 2 = c := by
  unfold vec4; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
@[simp] lemma vec4_three : vec4 a b c e 3 = e := by
  unfold vec4; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
end vec4

/-- The normalised trace `τ = Tr / D`. -/
def ntr (X : Matrix ι ι ℂ) : ℂ := trace X / Fintype.card ι

/-- The phase attached to the fourth link: `w^{-n}` at `s = 3`, `1` otherwise. -/
def twist (d : ℕ) (s : ZMod 4) (n : ℕ) : ℂ := if s = 3 then (wd d ^ n)⁻¹ else 1

/-- `Λ_n(R) = ∑_{i=0}^{3} τ(L^{(i)}_n)` (paper eq. (Strace)) for a chain `R_{s+1} = R s`, `s ∈ ℤ/4`:
the links are `L^{(s)}_n = R_{s+1}^n R_{s+2}^{-n}` for `s = 0, 1, 2` and `L^{(3)}_n = w^{-n} R_4^n R_1^{-n}`
(for unitary `R`, `R^{-n} = (R^n)ᴴ`). -/
def Lam (d : ℕ) (R : ZMod 4 → Matrix ι ι ℂ) (n : ℕ) : ℂ :=
  ∑ s : ZMod 4, twist d s n * ntr (R s ^ n * (R (s + 1) ^ n)ᴴ)

/-- **The chain unitaries**, paper eq. (chainR): `R_1 = U_2`, `R_2 = (U'_2)^T`, `R_3 = U_1`,
`R_4 = (U'_1)^T`, stored as `chainR A B s = R_{s+1}` (`s ∈ ℤ/4`). Here `U_x = ∑_a w^a A_{x,a}` and
`U'_y = ∑_b w^b B_{y,b}`. -/
def chainR (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) : ZMod 4 → Matrix ι ι ℂ :=
  vec4 (pvmU (A 1)) (pvmU (B 1))ᵀ (pvmU (A 0)) (pvmU (B 0))ᵀ

omit [DecidableEq ι] in
lemma trace_mul_transpose_conjTranspose (X Y : Matrix ι ι ℂ) :
    trace (X * (Yᵀ)ᴴ) = trace (Xᵀ * Yᴴ) := by
  rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← trace_transpose, transpose_mul,
    transpose_transpose, trace_mul_comm]

omit [DecidableEq ι] in
lemma conj_ntr (X : Matrix ι ι ℂ) : conj (ntr X) = ntr Xᴴ := by
  rw [ntr, ntr, map_div₀, Complex.conj_natCast, trace_conjTranspose, Complex.star_def]

lemma sum_zmod4 {M : Type*} [AddCommMonoid M] (f : ZMod 4 → M) :
    ∑ s, f s = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

/-- **Paper eq. (Strace).** For a projective strategy on the maximally entangled state,
`S = 2(d-1) + ∑_{n=1}^{d-1} c_n Λ_n(R)` with `R` the chain unitaries. -/
theorem chainS_trace [Nonempty ι] (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) (hA : ∀ x, IsPVM (A x))
    (hB : ∀ y, IsPVM (B y)) :
    (chainS (probME A B) : ℂ) = 2 * ((d : ℂ) - 1) + ∑ n ∈ Ico 1 d, cd d n * Lam d (chainR A B) n := by
  rw [chainS_fourier _ (probME_normalised A B hA hB)]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  congr 1
  rw [Lam, sum_zmod4]
  simp only [charSum_probME A B hA hB, twist, chainR]
  have h01 : (0 : ZMod 4) + 1 = 1 := rfl
  have h11 : (1 : ZMod 4) + 1 = 2 := rfl
  have h21 : (2 : ZMod 4) + 1 = 3 := rfl
  have h31 : (3 : ZMod 4) + 1 = 0 := rfl
  have n0 : (0 : ZMod 4) ≠ 3 := by decide
  have n1 : (1 : ZMod 4) ≠ 3 := by decide
  have n2 : (2 : ZMod 4) ≠ 3 := by decide
  rw [h01, h11, h21, h31]
  simp only [n0, n1, n2, if_false, if_true, vec4_zero, vec4_one, vec4_two, vec4_three, one_mul,
    ← transpose_pow, ntr]
  rw [trace_mul_transpose_conjTranspose, trace_mul_transpose_conjTranspose]
  have c1 : conj (trace ((pvmU (A 0) ^ n)ᵀ * (pvmU (B 1) ^ n)ᴴ) / (Fintype.card ι : ℂ))
      = trace ((pvmU (B 1) ^ n)ᵀ * (pvmU (A 0) ^ n)ᴴ) / Fintype.card ι := by
    rw [map_div₀, Complex.conj_natCast, ← Complex.star_def, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, trace_mul_transpose_conjTranspose]
  have c2 : conj (trace ((pvmU (A 1) ^ n)ᵀ * (pvmU (B 0) ^ n)ᴴ) / (Fintype.card ι : ℂ))
      = trace ((pvmU (B 0) ^ n)ᵀ * (pvmU (A 1) ^ n)ᴴ) / Fintype.card ι := by
    rw [map_div₀, Complex.conj_natCast, ← Complex.star_def, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, trace_mul_transpose_conjTranspose]
  rw [c1, c2]

end Quantum

end

end OQP27.Red
