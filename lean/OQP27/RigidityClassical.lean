import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

/-!
# OQP 27B rigidity, Step 5 (first half): commuting configurations are classical (module L6)

Paper proofs: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, section 6.1-6.2, and
`publish/CGLMP/paper-classical-all-d/main.tex`, Theorem B (proof in its Section 3) and eq. (Fa).

Setting (`RIGIDITY_ALLD.md` 1.3). `d ≥ 1`, `N = 4d`. A 27B configuration on `ℂ^M` (here `ℂ^ι` for a
finite index type `ι`, `M = |ι|`) is a family of projections `Q : ℤ_N → M_M(ℂ)` such that at every site `k ∈ {0, …, d-1}` the four projections
`Q_{k - d a}` (`a ∈ ℤ_4`) form a PVM (`OQP27.Rig.IsConfig`). Its reduced family is
`V_k = E_k^* = ∑_a (-i)^a Q_{k - d a}` (eq. (1.0), `OQP27.Rig.redV`), and
`F(V) = ∑_{j<k} Re[h_{k-j} tr(V_j V_k^*)]`, `h_m = sec ψ_m - i csc ψ_m`, `ψ_m = πm/(2d)`,
`tr = Tr/M`, `M = |ι|` (`OQP27.Rig.clockF`).

What is proved (the only hypothesis is the classical rearrangement theorem):

* `OQP27.Rig.clockF_eq_sum`: if all `Q_x` commute, then with the joint spectral projections
  `Π_a = ∏_k Q_{k - d a_k}` (`a ∈ ℤ_4^d`), `F(V) = ∑_a tr(Π_a) F(a)`, where
  `F(a) = ∑_{j<k} Re[h_{k-j} i^{a_k - a_j}]` is the classical clock function (paper eq. (Fa)).
* `OQP27.Rig.commuting_optimal_relations` (Theorem B, equality case, and the relations used by
  Corollary C): if all `Q_x` commute and `F(V) = F_DKZ`, then, assuming the classical statement
  `OQP27.Rig.Hyp_ClassicalTheoremB d`, every `Π_a` with `a` not one-step vanishes, and the reduced
  family satisfies, for `1 ≤ n ≤ d` and every site `k`, `(Y - 1)(Y - i) = 0` with
  `Y = V_{k-n} V_k^*` (`k ≥ n`) resp. `Y = i V_{k-n+d} V_k^*` (`k < n`)
  (`RIGIDITY.md` Lemma 7.2(b), the two-eigenvalue relations `(T_n)` in the reduced variables).
  The `V_k` commute pairwise, so the cyclic adjacent commutation of Lemma 7.2(a) also holds.

Hypothesis remaining (precise statement in `OQP27.Rig.Hyp_ClassicalTheoremB`): Theorem B of
`paper-classical-all-d` for `M = 1`, i.e. `F(a) ≤ F_DKZ` for every `a ∈ ℤ_4^d`, with equality only
for one-step `a` (`a_k = c + [k ≥ r]`). It is proved by hand in that paper (Theorem A, the
discrete rearrangement inequality, plus the cotangent representation, Lemma `lem:cot`); it is
not formalised.
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset

namespace OQP27.Rig

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- A projection (shared convention of the OQP27 formalisation). -/
def IsProj (P : Matrix ι ι ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- The index `k - d a ∈ ℤ_N`, `N = 4d`, of the label `a ∈ ℤ_4` at the site `k`. -/
def siteIdx (d : ℕ) (k : Fin d) (a : ZMod 4) : ZMod (4 * d) :=
  ((k : ℕ) : ZMod (4 * d)) - (d : ZMod (4 * d)) * ((a.val : ℕ) : ZMod (4 * d))

/-- A 27B configuration on `ℂ^M` (`RIGIDITY_ALLD.md` 1.3): projections `Q_x`, `x ∈ ℤ_{4d}`, such that
for each site `k` the four projections `Q_{k - d a}`, `a ∈ ℤ_4`, form a PVM. -/
structure IsConfig (Q : ZMod (4 * d) → Matrix ι ι ℂ) : Prop where
  proj : ∀ x, IsProj (Q x)
  pvm_sum : ∀ k : Fin d, ∑ a : ZMod 4, Q (siteIdx d k a) = 1
  pvm_orth : ∀ k : Fin d, ∀ a b : ZMod 4, a ≠ b → Q (siteIdx d k a) * Q (siteIdx d k b) = 0

/-- The reduced family of a configuration, `V_k = E_k^* = ∑_a (-i)^a Q_{k - d a}` (eq. (1.0)). -/
noncomputable def redV (Q : ZMod (4 * d) → Matrix ι ι ℂ) (k : Fin d) :
    Matrix ι ι ℂ :=
  ∑ a : ZMod 4, ((-I) ^ a.val) • Q (siteIdx d k a)

/-- `h_m = sec ψ_m - i csc ψ_m`, `ψ_m = π m/(2d)`. -/
noncomputable def hm (d m : ℕ) : ℂ :=
  ((1 / Real.cos (Real.pi * m / (2 * d)) : ℝ) : ℂ) - I * ((1 / Real.sin (Real.pi * m / (2 * d)) : ℝ) : ℂ)

/-- `F(V) = ∑_{0 ≤ j < k ≤ d-1} Re[h_{k-j} tr(V_j V_k^*)]`, `tr = Tr/M` (paper eq. (F)). -/
noncomputable def clockF (V : Fin d → Matrix ι ι ℂ) : ℝ :=
  ∑ j : Fin d, ∑ k : Fin d,
    if j < k then (hm d ((k : ℕ) - j) * ((V j * star (V k)).trace / Fintype.card ι)).re else 0

/-- The classical clock function `F(a) = ∑_{j<k} Re[h_{k-j} i^{a_k - a_j}]` (paper eq. (Fa)). -/
noncomputable def clockFa (a : Fin d → ZMod 4) : ℝ :=
  ∑ j : Fin d, ∑ k : Fin d, if j < k then (hm d ((k : ℕ) - j) * I ^ (a k - a j).val).re else 0

/-- `F_DKZ = ∑_{m=1}^{d-1} (d - m) sec ψ_m` (paper eq. (FDKZ)). -/
noncomputable def FDKZ (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 d, ((d : ℝ) - m) * (1 / Real.cos (Real.pi * m / (2 * d)))

/-- One-step configurations: `a_k = c + [k ≥ r]` for some `c ∈ ℤ_4` and `0 ≤ r ≤ d - 1`. -/
def IsOneStep (a : Fin d → ZMod 4) : Prop :=
  ∃ c : ZMod 4, ∃ r : ℕ, r < d ∧ ∀ k : Fin d, a k = c + if r ≤ (k : ℕ) then 1 else 0

/-- **Hypothesis: Theorem B of `paper-classical-all-d` for `M = 1`** (the commutative sector on one
joint eigenvector). For every `a ∈ ℤ_4^d`, `F(a) ≤ F_DKZ`, and equality holds only if `a` is
one-step. Paper proof: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 3 ("Proof of
Theorem B from Theorem A", using Lemma `lem:cot`) and Section 4 (Theorem A, the discrete
rearrangement inequality). Not formalised. -/
def Hyp_ClassicalTheoremB (d : ℕ) : Prop :=
  ∀ a : Fin d → ZMod 4, clockFa a ≤ FDKZ d ∧ (clockFa a = FDKZ d → IsOneStep a)

/-! ## Elementary facts -/

lemma I_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

lemma negI_eq : -I = I ^ 3 := by rw [pow_succ, I_sq]; ring

lemma val_sub_aux : ∀ s t : ZMod 4, (3 * s.val + t.val) % 4 = (t - s).val := by decide

lemma I_pow_val_mul (s t : ZMod 4) : (-I) ^ s.val * I ^ t.val = I ^ (t - s).val := by
  rw [negI_eq, ← pow_mul, ← pow_add, I_pow_mod, val_sub_aux]

lemma star_negI_pow (s : ZMod 4) : star ((-I) ^ s.val) = I ^ s.val := by
  rw [star_pow, Complex.star_def, map_neg, Complex.conj_I, neg_neg]

/-- `Tr P = ∑ |P_ij|²` for a Hermitian idempotent `P`. -/
lemma trace_proj (P : Matrix ι ι ℂ) (hP : IsProj P) :
    P.trace = ((∑ i, ∑ j, ‖P j i‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : P.trace = (Pᴴ * P).trace := by rw [hP.1.eq, hP.2]
  rw [h1]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma proj_eq_zero_of_trace (P : Matrix ι ι ℂ) (hP : IsProj P) (h : P.trace = 0) :
    P = 0 := by
  rw [trace_proj P hP] at h
  have h' : (∑ i, ∑ j, ‖P j i‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  ext j i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => sq_nonneg ‖P j i‖))).1 h' i (Finset.mem_univ _)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖P j i‖)).1 hi j
    (Finset.mem_univ _)
  simpa using hj

lemma trace_proj_re_nonneg (P : Matrix ι ι ℂ) (hP : IsProj P) :
    0 ≤ P.trace.re ∧ P.trace.im = 0 := by
  rw [trace_proj P hP]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-! ## Joint spectral projections of a commuting configuration -/

section Joint

variable [NeZero d] (Q : ZMod (4 * d) → Matrix ι ι ℂ)

/-- The star subalgebra generated by the `Q_x`. -/
noncomputable def cAlg : StarSubalgebra ℂ (Matrix ι ι ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range Q)

lemma cAlg_mul_comm [hH : Fact (∀ x, (Q x).IsHermitian)] [hc : Fact (∀ x y, Q x * Q y = Q y * Q x)]
    (a b : cAlg Q) : a * b = b * a := by
  have h := StarAlgebra.isMulCommutative_adjoin ℂ (s := Set.range Q)
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact hc.out x y)
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [star_eq_conjTranspose, (hH.out y).eq]; exact hc.out x y)
  exact h.is_comm.comm a b

/-- For a commuting family of Hermitian matrices the generated star algebra is commutative. -/
@[reducible] noncomputable def cAlgCommRing [Fact (∀ x, (Q x).IsHermitian)]
    [Fact (∀ x y, Q x * Q y = Q y * Q x)] : CommRing (cAlg Q) :=
  { (inferInstance : Ring (cAlg Q)) with mul_comm := cAlg_mul_comm Q }

attribute [local instance] cAlgCommRing

/-- `Q_x` as an element of the generated algebra. -/
noncomputable def qq (x : ZMod (4 * d)) : cAlg Q := ⟨Q x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩

@[simp] lemma coe_qq (x : ZMod (4 * d)) : ((qq Q x : cAlg Q) : Matrix ι ι ℂ) = Q x := rfl

variable {Q}

lemma qq_mul_self (hQ : IsConfig Q) (x : ZMod (4 * d)) : qq Q x * qq Q x = qq Q x :=
  Subtype.ext (hQ.proj x).2

lemma star_qq (hQ : IsConfig Q) (x : ZMod (4 * d)) : star (qq Q x) = qq Q x :=
  Subtype.ext (by
    show star (Q x) = Q x
    rw [star_eq_conjTranspose, (hQ.proj x).1.eq])

lemma sum_qq (hQ : IsConfig Q) (k : Fin d) : ∑ a : ZMod 4, qq Q (siteIdx d k a) = 1 :=
  Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hQ.pvm_sum k)

lemma qq_orth (hQ : IsConfig Q) (k : Fin d) {a b : ZMod 4} (hab : a ≠ b) :
    qq Q (siteIdx d k a) * qq Q (siteIdx d k b) = 0 :=
  Subtype.ext (hQ.pvm_orth k a b hab)

lemma qq_mul_qq (hQ : IsConfig Q) (k : Fin d) (a b : ZMod 4) :
    qq Q (siteIdx d k a) * qq Q (siteIdx d k b) = if b = a then qq Q (siteIdx d k a) else 0 := by
  split_ifs with h
  · rw [h, qq_mul_self hQ]
  · exact qq_orth hQ k (Ne.symm h)

variable [Fact (∀ x, (Q x).IsHermitian)] [Fact (∀ x y, Q x * Q y = Q y * Q x)]

variable (Q) in
/-- The joint spectral projection `Π_a = ∏_k Q_{k - d a_k}` of a configuration `a ∈ ℤ_4^d`. -/
noncomputable def jp (a : Fin d → ZMod 4) : cAlg Q := ∏ k : Fin d, qq Q (siteIdx d k (a k))

lemma jp_mul_self (hQ : IsConfig Q) (a : Fin d → ZMod 4) : jp Q a * jp Q a = jp Q a := by
  rw [jp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => qq_mul_self hQ _

lemma jp_mul_jp (hQ : IsConfig Q) (a b : Fin d → ZMod 4) :
    jp Q a * jp Q b = if a = b then jp Q a else 0 := by
  split_ifs with h
  · rw [h, jp_mul_self hQ]
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    rw [jp, jp, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (qq_orth hQ k hk)

lemma sum_jp (hQ : IsConfig Q) : ∑ a : Fin d → ZMod 4, jp Q a = 1 := by
  simp only [jp]
  rw [← Fintype.prod_sum (fun (k : Fin d) (s : ZMod 4) => qq Q (siteIdx d k s))]
  exact Finset.prod_eq_one fun k _ => sum_qq hQ k

lemma qq_mul_jp (hQ : IsConfig Q) (k : Fin d) (s : ZMod 4) (a : Fin d → ZMod 4) :
    qq Q (siteIdx d k s) * jp Q a = if a k = s then jp Q a else 0 := by
  rw [jp, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), ← mul_assoc,
    qq_mul_qq hQ]
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

lemma qq_eq_sum (hQ : IsConfig Q) (k : Fin d) (s : ZMod 4) :
    qq Q (siteIdx d k s) = ∑ a : Fin d → ZMod 4, if a k = s then jp Q a else 0 := by
  rw [← mul_one (qq Q (siteIdx d k s)), ← sum_jp hQ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => qq_mul_jp hQ k s a

lemma star_jp (hQ : IsConfig Q) (a : Fin d → ZMod 4) : star (jp Q a) = jp Q a := by
  rw [jp, star_prod]
  exact Finset.prod_congr rfl fun k _ => star_qq hQ _

lemma jp_isProj (hQ : IsConfig Q) (a : Fin d → ZMod 4) :
    IsProj ((jp Q a : cAlg Q) : Matrix ι ι ℂ) := by
  constructor
  · show _ = _
    rw [← star_eq_conjTranspose]
    exact congrArg Subtype.val (star_jp hQ a)
  · exact congrArg Subtype.val (jp_mul_self hQ a)

/-- Product of two combinations of the orthogonal projections `Π_a`. -/
lemma comb_mul_comb (hQ : IsConfig Q) (α β : (Fin d → ZMod 4) → ℂ) :
    (∑ a, α a • jp Q a) * (∑ b, β b • jp Q b) = ∑ a, (α a * β a) • jp Q a := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  simp_rw [smul_mul_smul, jp_mul_jp hQ, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma one_eq_comb (hQ : IsConfig Q) : (1 : cAlg Q) = ∑ a, (1 : ℂ) • jp Q a := by
  simp [sum_jp hQ]

/-- The reduced family inside the generated algebra. -/
noncomputable def vv (Q : ZMod (4 * d) → Matrix ι ι ℂ) (k : Fin d) : cAlg Q :=
  ∑ s : ZMod 4, ((-I) ^ s.val) • qq Q (siteIdx d k s)

lemma coe_vv (k : Fin d) : ((vv Q k : cAlg Q) : Matrix ι ι ℂ) = redV Q k := by
  rw [vv, AddSubmonoidClass.coe_finsetSum]
  rfl

lemma vv_eq (hQ : IsConfig Q) (k : Fin d) :
    vv Q k = ∑ a : Fin d → ZMod 4, ((-I) ^ (a k).val) • jp Q a := by
  rw [vv]
  simp_rw [qq_eq_sum hQ, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp

lemma star_vv (hQ : IsConfig Q) (k : Fin d) :
    star (vv Q k) = ∑ a : Fin d → ZMod 4, (I ^ (a k).val) • jp Q a := by
  rw [vv_eq hQ, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_smul, star_jp hQ, star_negI_pow]

lemma vv_mul_star_vv (hQ : IsConfig Q) (j k : Fin d) :
    vv Q j * star (vv Q k) = ∑ a : Fin d → ZMod 4, (I ^ (a k - a j).val) • jp Q a := by
  rw [vv_eq hQ, star_vv hQ, comb_mul_comb hQ]
  simp_rw [I_pow_val_mul]

lemma trace_comb (α : (Fin d → ZMod 4) → ℂ) :
    (((∑ a, α a • jp Q a : cAlg Q)) : Matrix ι ι ℂ).trace
      = ∑ a, α a * ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace := by
  rw [AddSubmonoidClass.coe_finsetSum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : ((α a • jp Q a : cAlg Q) : Matrix ι ι ℂ)
      = α a • ((jp Q a : cAlg Q) : Matrix ι ι ℂ) := rfl
  rw [e, Matrix.trace_smul, smul_eq_mul]

end Joint

/-! ## Theorem B for commuting configurations, and the relations of the equality case -/

section Main

variable [NeZero d] {Q : ZMod (4 * d) → Matrix ι ι ℂ}

attribute [local instance] cAlgCommRing

/-- `tr(Π_a) = Tr(Π_a)/M`, `M = |ι|` (a real number). -/
noncomputable def jtr (Q : ZMod (4 * d) → Matrix ι ι ℂ)
    [Fact (∀ x, (Q x).IsHermitian)] [Fact (∀ x y, Q x * Q y = Q y * Q x)]
    (a : Fin d → ZMod 4) : ℝ :=
  ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace.re / Fintype.card ι

variable [Fact (∀ x, (Q x).IsHermitian)] [Fact (∀ x y, Q x * Q y = Q y * Q x)]

lemma redV_mul_star (j k : Fin d) :
    redV Q j * star (redV Q k)
      = ((vv Q j * star (vv Q k) : cAlg Q) : Matrix ι ι ℂ) := by
  rw [← coe_vv, ← coe_vv]
  rfl

lemma trace_jp_real (hQ : IsConfig Q) (a : Fin d → ZMod 4) :
    ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace
      = ((((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [(trace_proj_re_nonneg _ (jp_isProj hQ a)).2]

/-- **Theorem B, the identity**: for a commuting configuration,
`F(V) = ∑_a tr(Π_a) F(a)`. -/
theorem clockF_eq_sum (hQ : IsConfig Q) :
    clockF (redV Q) = ∑ a : Fin d → ZMod 4, jtr Q a * clockFa a := by
  have hjk : ∀ j k : Fin d, (hm d ((k : ℕ) - j) * ((redV Q j * star (redV Q k)).trace / Fintype.card ι)).re
      = ∑ a : Fin d → ZMod 4, jtr Q a * (hm d ((k : ℕ) - j) * I ^ (a k - a j).val).re := by
    intro j k
    rw [redV_mul_star, vv_mul_star_vv hQ, trace_comb, Finset.sum_div, Finset.mul_sum,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [trace_jp_real hQ a, jtr]
    set t := ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace.re
    have e : hm d ((k : ℕ) - j) * (I ^ (a k - a j).val * (t : ℂ) / (Fintype.card ι : ℂ))
        = ((t / Fintype.card ι : ℝ) : ℂ) * (hm d ((k : ℕ) - j) * I ^ (a k - a j).val) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
  unfold clockF clockFa
  calc ∑ j : Fin d, ∑ k : Fin d,
        (if j < k then (hm d ((k : ℕ) - j) * ((redV Q j * star (redV Q k)).trace / Fintype.card ι)).re else 0)
      = ∑ j : Fin d, ∑ k : Fin d, ∑ a : Fin d → ZMod 4,
          (if j < k then jtr Q a * (hm d ((k : ℕ) - j) * I ^ (a k - a j).val).re else 0) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        split_ifs
        · exact hjk j k
        · simp
    _ = ∑ a : Fin d → ZMod 4, ∑ j : Fin d, ∑ k : Fin d,
          (if j < k then jtr Q a * (hm d ((k : ℕ) - j) * I ^ (a k - a j).val).re else 0) := by
        calc _ = ∑ j : Fin d, ∑ a : Fin d → ZMod 4, ∑ k : Fin d,
              (if j < k then jtr Q a * (hm d ((k : ℕ) - j) * I ^ (a k - a j).val).re else 0) :=
              Finset.sum_congr rfl fun j _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
    _ = ∑ a : Fin d → ZMod 4, jtr Q a * ∑ j : Fin d, ∑ k : Fin d,
          (if j < k then (hm d ((k : ℕ) - j) * I ^ (a k - a j).val).re else 0) := by
        simp_rw [Finset.mul_sum, mul_ite, mul_zero]

lemma jtr_nonneg (hQ : IsConfig Q) (a : Fin d → ZMod 4) : 0 ≤ jtr Q a :=
  div_nonneg (trace_proj_re_nonneg _ (jp_isProj hQ a)).1 (Nat.cast_nonneg (Fintype.card ι))

lemma sum_jtr (hQ : IsConfig Q) (hM : 0 < Fintype.card ι) : ∑ a : Fin d → ZMod 4, jtr Q a = 1 := by
  have h1 : ∑ a : Fin d → ZMod 4, ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace = Fintype.card ι := by
    rw [← Matrix.trace_sum, ← AddSubmonoidClass.coe_finsetSum, sum_jp hQ]
    simp
  have h2 : ∑ a : Fin d → ZMod 4, ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace.re = Fintype.card ι := by
    rw [← Complex.re_sum, h1]
    simp
  unfold jtr
  rw [← Finset.sum_div, h2]
  exact div_self (Nat.cast_ne_zero.2 hM.ne' : (Fintype.card ι : ℝ) ≠ 0)

/-- **Theorem B (inequality) for commuting configurations**, given the classical statement. -/
theorem clockF_le (hB : Hyp_ClassicalTheoremB d) (hQ : IsConfig Q) (hM : 0 < Fintype.card ι) :
    clockF (redV Q) ≤ FDKZ d := by
  rw [clockF_eq_sum hQ]
  calc ∑ a : Fin d → ZMod 4, jtr Q a * clockFa a ≤ ∑ a : Fin d → ZMod 4, jtr Q a * FDKZ d :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hB a).1 (jtr_nonneg hQ a)
    _ = FDKZ d := by rw [← Finset.sum_mul, sum_jtr hQ hM, one_mul]

/-- **Theorem B (equality case)**: if `F(V) = F_DKZ`, every joint spectral projection `Π_a` with `a`
not one-step vanishes. -/
theorem jp_eq_zero (hB : Hyp_ClassicalTheoremB d) (hQ : IsConfig Q) (hM : 0 < Fintype.card ι)
    (hF : clockF (redV Q) = FDKZ d) (a : Fin d → ZMod 4) (ha : ¬ IsOneStep a) : jp Q a = 0 := by
  have key : ∑ b : Fin d → ZMod 4, jtr Q b * (FDKZ d - clockFa b) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_jtr hQ hM, one_mul, ← clockF_eq_sum hQ, hF,
      sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
    mul_nonneg (jtr_nonneg hQ b) (sub_nonneg.2 (hB b).1))).1 key a (Finset.mem_univ a)
  have hlt : clockFa a < FDKZ d := lt_of_le_of_ne (hB a).1 (fun h => ha ((hB a).2 h))
  have hz : jtr Q a = 0 := by
    rcases mul_eq_zero.1 hterm with h | h
    · exact h
    · linarith
  have hre : ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace.re = 0 := by
    unfold jtr at hz
    rcases div_eq_zero_iff.1 hz with h | h
    · exact h
    · exact absurd h (Nat.cast_ne_zero.2 hM.ne')
  have htr : ((jp Q a : cAlg Q) : Matrix ι ι ℂ).trace = 0 := by
    rw [trace_jp_real hQ a, hre, Complex.ofReal_zero]
  exact Subtype.ext (proj_eq_zero_of_trace _ (jp_isProj hQ a) htr)

end Main

/-! ## The relations of Lemma 7.2 for an optimal commuting configuration -/

/-- The unitary `Y_{n,k}` of `RIGIDITY.md` Lemma 7.2(b): `V_{k-n} V_k^*` if `n ≤ k`, and
`i V_{k-n+d} V_k^*` if `k < n` (the `k`-th diagonal block of `z^n R_1^n R_2^{-n}` for the
covariant strategy of the reduced family `V`). -/
noncomputable def relY (V : Fin d → Matrix ι ι ℂ) (n : ℕ) (k : Fin d) :
    Matrix ι ι ℂ :=
  if h : n ≤ (k : ℕ) then V ⟨k - n, by have := k.isLt; omega⟩ * star (V k)
  else I • (V ⟨k + d - n, by have := k.isLt; omega⟩ * star (V k))

lemma one_add_val_aux : ∀ t : ZMod 4, (1 + t.val) % 4 = (1 + t).val := by decide

lemma I_mul_I_pow (t : ZMod 4) : I * I ^ t.val = I ^ (1 + t).val := by
  rw [← pow_succ', I_pow_mod (t.val + 1), add_comm t.val 1, one_add_val_aux]

lemma one_step_diff {a : Fin d → ZMod 4} (ha : IsOneStep a) {j k : Fin d} (hjk : (j : ℕ) ≤ k) :
    a k - a j = 0 ∨ a k - a j = 1 := by
  obtain ⟨c, r, -, hc⟩ := ha
  rw [hc j, hc k]
  by_cases h1 : r ≤ (j : ℕ)
  · have h2 : r ≤ (k : ℕ) := le_trans h1 hjk
    simp [h1, h2]
  · by_cases h2 : r ≤ (k : ℕ)
    · simp [h1, h2]
    · simp [h1, h2]

lemma one_step_diff' {a : Fin d → ZMod 4} (ha : IsOneStep a) {j k : Fin d} (hjk : (k : ℕ) ≤ j) :
    1 + (a k - a j) = 0 ∨ 1 + (a k - a j) = 1 := by
  obtain ⟨c, r, -, hc⟩ := ha
  rw [hc j, hc k]
  by_cases h1 : r ≤ (k : ℕ)
  · have h2 : r ≤ (j : ℕ) := le_trans h1 hjk
    simp [h1, h2]
  · by_cases h2 : r ≤ (j : ℕ)
    · left; simp [h1, h2]
    · simp [h1, h2]

lemma two_valued_coeff {e : ZMod 4} (he : e = 0 ∨ e = 1) :
    (I ^ e.val - 1) * (I ^ e.val - I) = 0 := by
  rcases he with h | h <;> subst h
  · have h0 : (0 : ZMod 4).val = 0 := rfl
    rw [h0, pow_zero, sub_self, zero_mul]
  · have h1 : (1 : ZMod 4).val = 1 := rfl
    rw [h1, pow_one, sub_self, mul_zero]

/-- **The equality case in the commutative sector** (`RIGIDITY_ALLD.md` 6.1-6.2): if all `Q_x`
commute and `F(V) = F_DKZ`, then (given `Hyp_ClassicalTheoremB`) the reduced family commutes and
satisfies the two-eigenvalue relations `(Y_{n,k} - 1)(Y_{n,k} - i) = 0` for `1 ≤ n ≤ d` and every
site `k`. -/
theorem commuting_optimal_relations [NeZero d] {Q : ZMod (4 * d) → Matrix ι ι ℂ}
    (hB : Hyp_ClassicalTheoremB d) (hQ : IsConfig Q) (hcomm : ∀ x y, Q x * Q y = Q y * Q x)
    (hF : clockF (redV Q) = FDKZ d) :
    (∀ j k, redV Q j * redV Q k = redV Q k * redV Q j) ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ d → ∀ k : Fin d,
      (relY (redV Q) n k - 1) * (relY (redV Q) n k - I • 1) = 0 := by
  have : Fact (∀ x, (Q x).IsHermitian) := ⟨fun x => (hQ.proj x).1⟩
  have : Fact (∀ x y, Q x * Q y = Q y * Q x) := ⟨hcomm⟩
  let _ := cAlgCommRing Q
  refine ⟨fun j k => ?_, fun n hn1 hn2 k => ?_⟩
  · rw [← coe_vv, ← coe_vv]
    exact congrArg Subtype.val (mul_comm (vv Q j) (vv Q k))
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  have hM : 0 < Fintype.card ι := Fintype.card_pos
  -- the exponent of `Y_{n,k}` on the joint eigenspace `a`
  set e : (Fin d → ZMod 4) → ZMod 4 := fun a =>
    if h : n ≤ (k : ℕ) then a k - a ⟨k - n, by have := k.isLt; omega⟩
    else 1 + (a k - a ⟨k + d - n, by have := k.isLt; omega⟩) with he
  have hY : relY (redV Q) n k
      = ((∑ a : Fin d → ZMod 4, (I ^ (e a).val) • jp Q a : cAlg Q) : Matrix ι ι ℂ) := by
    unfold relY
    split_ifs with h
    · rw [redV_mul_star, vv_mul_star_vv hQ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [he, dif_pos h]
    · rw [redV_mul_star, vv_mul_star_vv hQ]
      have e1 : ∀ X : cAlg Q, I • (X : Matrix ι ι ℂ) = ((I • X : cAlg Q) : Matrix ι ι ℂ) :=
        fun X => rfl
      rw [e1, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [he, dif_neg h]
      rw [smul_smul, I_mul_I_pow]
  set X : cAlg Q := ∑ a : Fin d → ZMod 4, (I ^ (e a).val) • jp Q a with hX
  have h1 : X - 1 = ∑ a : Fin d → ZMod 4, (I ^ (e a).val - 1) • jp Q a := by
    rw [one_eq_comb hQ, hX, ← Finset.sum_sub_distrib]
    simp_rw [sub_smul]
  have h2 : X - I • 1 = ∑ a : Fin d → ZMod 4, (I ^ (e a).val - I) • jp Q a := by
    rw [one_eq_comb hQ, hX, Finset.smul_sum, ← Finset.sum_sub_distrib]
    simp_rw [smul_smul, mul_one, sub_smul]
  have h3 : (X - 1) * (X - I • 1) = 0 := by
    rw [h1, h2, comb_mul_comb hQ]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : IsOneStep a
    · have hc : (I ^ (e a).val - 1) * (I ^ (e a).val - I) = 0 := by
        apply two_valued_coeff
        simp only [he]
        split_ifs with h
        · exact one_step_diff ha (by show (k : ℕ) - n ≤ k; omega)
        · exact one_step_diff' ha (by show (k : ℕ) ≤ k + d - n; omega)
      rw [hc, zero_smul]
    · rw [jp_eq_zero hB hQ hM hF a ha, smul_zero]
  rw [hY]
  have := congrArg Subtype.val h3
  exact this

end OQP27.Rig
