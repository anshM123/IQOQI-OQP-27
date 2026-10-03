import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# OQP 27B, maximally entangled clause: the statement in the internal model of the proof

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

IQOQI Vienna Open Quantum Problem 27 ("The power of CGLMP inequalities"), part B, asks to show that the
Durt-Kaszlikowski-Zukowski (DKZ) measurements are necessarily the optimal measurements for the CGLMP
inequality on maximally entangled states.  This file states that clause for every number of outcomes `d`,
with concrete complex matrices, in the internal model used by the proof: projective measurements of any
rank on `Φ_D` for every local dimension `D`, the probabilities in the closed form `Tr(Aᵀ B)/D`, and the
CGLMP expression of Collins et al.  The formulation of Formal Conjectures issue #3444 (complete von
Neumann measurements on `Φ_d`, the Born rule, the CGLMP functional of the problem page) and its reduction
to this model are proved in the single-file version of this development
(`formal-conjectures-27/27.lean`, Parts 0 and 87).

## Objects
* `OQP27.IsProjection P`: `P` is Hermitian and idempotent (the shared convention `P.IsHermitian ∧ P * P = P`).
* `OQP27.PVM d D`: a `d`-outcome projective measurement on `ℂ^D` (Hermitian idempotents summing to `1`);
  `OQP27.PVM.mul_eq_zero`: distinct outcomes are orthogonal.
* `OQP27.Strategy d D`: Alice's and Bob's two measurements (index `0` = setting 1, index `1` = setting 2)
  on the maximally entangled state `Φ_D = D^{-1/2} ∑ |ii⟩`, with
  `p(a,b|x,y) = ⟨Φ_D| A_{x,a} ⊗ B_{y,b} |Φ_D⟩ = Tr(A_{x,a}ᵀ B_{y,b}) / D` (`OQP27.Strategy.prob`).
* `OQP27.Strategy.cglmp`: the CGLMP expression exactly as in eq. (1) of
  `publish/CGLMP/paper-classical-all-d/main.tex`, where `P(A_x = B_y + k)` is the probability that
  `A_x - B_y ≡ k (mod d)`.
* `OQP27.IME d = 4/(d(d-1)) ∑_{j=1}^{d-1} (d-j) sec(π j/(2d))`.
* `OQP27.dkzA`, `OQP27.dkzB`, `OQP27.dkz`: the DKZ measurements of Collins et al. (2002), eqs. (12)-(15),
  in the form of `main.tex`, Section 2.4: Alice measures in the basis
  `|k⟩_{A,x} = d^{-1/2} ∑_j e^{-2πi j (k + α_x)/d} |j⟩`, Bob in `|l⟩_{B,y} = d^{-1/2} ∑_j e^{2πi j (l - β_y)/d} |j⟩`,
  with `α = (0, 1/2)` and `β = (1/4, -1/4)`.
* `OQP27.OptimalityStatement d`, `OQP27.RigidityStatement d`, `OQP27.MaxEntClause d`.

## Proved here (no hypotheses)
* projective measurements: orthogonality of distinct outcomes;
* `p(a,b|x,y)` is real (`OQP27.Strategy.im_trace_eq_zero`), nonnegative (`OQP27.Strategy.prob_nonneg`) and
  sums to `1` for each pair of settings (`OQP27.Strategy.sum_prob`);
* `OQP27.IME_gt_two`: `I_ME(d) > 2` (the local bound) for every `d ≥ 2`;
* the DKZ matrices form projective measurements (`OQP27.dkz`), and they are the projectors onto the
  DKZ basis vectors (`OQP27.dkzA_eq_vecMulVec`, `OQP27.dkzB_eq_vecMulVec`);
* `OQP27.Strategy.cglmp_eq_sum_range`: the folding step of Lemma 2.1 of `main.tex` (the CGLMP weights
  `1 - 2k/(d-1)` on the residues `t = 0, …, d-1` of the four chain differences);
* `OQP27.dkz_isDKZTensorId`: the DKZ strategy has the form required by the rigidity statement (`K = 1`),
  so `RigidityStatement` is consistent with the attainment theorem below;
* `OQP27.Strategy.cglmp_of_isDKZTensorId` (converse of rigidity): every strategy on `Φ_D`, `D ≥ 1`, that is
  DKZ ⊗ 1 up to a local unitary `u ⊗ ū` attains `I_ME(d)`; hence `OQP27.rigidity_iff`: under
  `RigidityStatement d` the optimal strategies are exactly these;
* `OQP27.dkz_cglmp`: **the DKZ strategy attains `I_ME(d)` for every `d ≥ 2`** (a finite trigonometric
  identity, proved via `∑_{t<d} t x^t = d/(x - 1)` for roots of unity `x ≠ 1` and
  `z^m/(z^{4m} - 1) + z^{-m}/(z^{-4m} - 1) = -1/(2 cos(π m/(2d)))`, `z = e^{2πi/(4d)}`).

No hypotheses remain in this file.  The optimality and rigidity statements themselves are proved in
`OQP27/Skeleton.lean` from explicitly named hypotheses (paper results), see `OQP27/STATUS_L1.md`.

## References
* D. Collins, N. Gisin, N. Linden, S. Massar, S. Popescu, PRL 88, 040404 (2002).
* T. Durt, D. Kaszlikowski, M. Zukowski, PRA 64, 024101 (2001).
* `publish/CGLMP/paper-classical-all-d/main.tex` (A. Mishra, A. Senthilkumar), Sections 1-2.
* `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, Theorem R (rigidity statement).
-/

namespace OQP27

open Matrix Complex Finset
open scoped ComplexOrder Kronecker Real

/-! ## Projective measurements -/

section Measurements

variable {d D : ℕ}

/-- A projection on `ℂ^D`: a Hermitian idempotent matrix. -/
def IsProjection (P : Matrix (Fin D) (Fin D) ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- A `d`-outcome projective measurement (PVM) on `ℂ^D`: projections summing to the identity.
Some outcomes may have the zero projection. -/
structure PVM (d D : ℕ) where
  /-- the projection of outcome `a` -/
  proj : Fin d → Matrix (Fin D) (Fin D) ℂ
  isProj : ∀ a, IsProjection (proj a)
  sum_eq_one : ∑ a, proj a = 1

lemma IsProjection.transpose {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsProjection P) : IsProjection Pᵀ :=
  ⟨hP.1.transpose, by rw [← transpose_mul, hP.2]⟩

/-- For projections `P`, `Q`: `Tr((QP)ᴴ (QP)) = Tr(PQP)`. -/
lemma IsProjection.trace_conjTranspose_mul {P Q : Matrix (Fin D) (Fin D) ℂ} (hP : IsProjection P)
    (hQ : IsProjection Q) : ((Q * P)ᴴ * (Q * P)).trace = (P * Q * P).trace := by
  rw [conjTranspose_mul, hP.1.eq, hQ.1.eq]
  rw [show P * Q * (Q * P) = P * (Q * Q) * P by simp only [Matrix.mul_assoc], hQ.2]

/-- For projections `P`, `Q`, `Tr(PQP)` is a nonnegative real number. -/
lemma IsProjection.trace_mul_mul_nonneg {P Q : Matrix (Fin D) (Fin D) ℂ} (hP : IsProjection P)
    (hQ : IsProjection Q) : 0 ≤ (P * Q * P).trace := by
  rw [← hP.trace_conjTranspose_mul hQ]
  exact (posSemidef_conjTranspose_mul_self _).trace_nonneg

/-- Distinct outcomes of a projective measurement are orthogonal. -/
theorem PVM.mul_eq_zero (P : PVM d D) {a b : Fin d} (hab : a ≠ b) :
    P.proj a * P.proj b = 0 := by
  set f : Fin d → ℂ := fun c => (P.proj a * P.proj c * P.proj a).trace with hf
  have hsum : ∑ c, f c = (P.proj a).trace := by
    simp only [hf]
    rw [← trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, P.sum_eq_one, Matrix.mul_one,
      (P.isProj a).2]
  have hterm : f a = (P.proj a).trace := by
    simp only [hf, (P.isProj a).2]
  have hrest : ∑ c ∈ univ.erase a, f c = 0 := by
    have h := Finset.add_sum_erase univ f (mem_univ a)
    rw [hsum, hterm] at h
    exact add_eq_left.mp h
  have hb : f b = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun c _ => (P.isProj a).trace_mul_mul_nonneg (P.isProj c))).1 hrest b
      (by simp [Ne.symm hab])
  simp only [hf] at hb
  rw [← (P.isProj a).trace_conjTranspose_mul (P.isProj b),
    trace_conjTranspose_mul_self_eq_zero_iff] at hb
  have h := congrArg conjTranspose hb
  rwa [conjTranspose_mul, (P.isProj a).1.eq, (P.isProj b).1.eq, conjTranspose_zero] at h

end Measurements

/-! ## Strategies on the maximally entangled state and the CGLMP expression -/

section Strategies

variable {d D : ℕ}

/-- A projective strategy on the maximally entangled state of local dimension `D`: Alice's two and
Bob's two `d`-outcome measurements on `ℂ^D`.  Index `0` is setting 1 and index `1` is setting 2. -/
structure Strategy (d D : ℕ) where
  /-- Alice's measurements `A_1, A_2` -/
  A : Fin 2 → PVM d D
  /-- Bob's measurements `B_1, B_2` -/
  B : Fin 2 → PVM d D

/-- The max-ent statistics `p(a,b|x,y) = ⟨Φ_D| A_{x,a} ⊗ B_{y,b} |Φ_D⟩ = Tr(A_{x,a}ᵀ B_{y,b}) / D`
(transpose in the Schmidt basis of `Φ_D`). The trace is real, see `Strategy.im_trace_eq_zero`. -/
noncomputable def Strategy.prob (S : Strategy d D) (x y : Fin 2) (a b : Fin d) : ℝ :=
  (((S.A x).proj a)ᵀ * (S.B y).proj b).trace.re / D

/-- `Tr(A_{x,a}ᵀ B_{y,b})` is a nonnegative real number. -/
theorem Strategy.trace_nonneg (S : Strategy d D) (x y : Fin 2) (a b : Fin d) :
    0 ≤ (((S.A x).proj a)ᵀ * (S.B y).proj b).trace := by
  have hA := ((S.A x).isProj a).transpose
  have hB := (S.B y).isProj b
  have h := hB.trace_mul_mul_nonneg hA
  rwa [Matrix.trace_mul_cycle, hB.2, Matrix.trace_mul_comm] at h

theorem Strategy.im_trace_eq_zero (S : Strategy d D) (x y : Fin 2) (a b : Fin d) :
    (((S.A x).proj a)ᵀ * (S.B y).proj b).trace.im = 0 :=
  ((Complex.nonneg_iff.1 (S.trace_nonneg x y a b)).2).symm

theorem Strategy.prob_nonneg (S : Strategy d D) (x y : Fin 2) (a b : Fin d) :
    0 ≤ S.prob x y a b :=
  div_nonneg (Complex.nonneg_iff.1 (S.trace_nonneg x y a b)).1 (Nat.cast_nonneg D)

/-- The probability as a complex number: `p(a,b|x,y) = Tr(A_{x,a}ᵀ B_{y,b}) / D`. -/
theorem Strategy.prob_eq (S : Strategy d D) (x y : Fin 2) (a b : Fin d) :
    (S.prob x y a b : ℂ) = (((S.A x).proj a)ᵀ * (S.B y).proj b).trace / D := by
  have h : (((S.A x).proj a)ᵀ * (S.B y).proj b).trace =
      (((((S.A x).proj a)ᵀ * (S.B y).proj b).trace.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [S.im_trace_eq_zero])
  rw [h, Strategy.prob]
  push_cast
  rfl

/-- For each pair of settings the statistics form a probability distribution. -/
theorem Strategy.sum_prob (S : Strategy d D) (hD : 0 < D) (x y : Fin 2) :
    ∑ a, ∑ b, S.prob x y a b = 1 := by
  have h : ∑ a, ∑ b, (((S.A x).proj a)ᵀ * (S.B y).proj b).trace = (D : ℂ) := by
    have h1 : ∀ a, ∑ b, (((S.A x).proj a)ᵀ * (S.B y).proj b).trace = ((S.A x).proj a).trace := by
      intro a
      rw [← trace_sum, ← Matrix.mul_sum, (S.B y).sum_eq_one, Matrix.mul_one, trace_transpose]
    simp_rw [h1]
    rw [← trace_sum, (S.A x).sum_eq_one, trace_one, Fintype.card_fin]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [Strategy.prob, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hD']
  have := congrArg Complex.re h
  simpa [Complex.re_sum] using this

/-- `P(A_x = B_y + k)`: the probability that `A_x - B_y ≡ k (mod d)` for the settings `x`, `y`. -/
noncomputable def Strategy.probAB (S : Strategy d D) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) + (k : ZMod d) then S.prob x y a b else 0

/-- `P(B_y = A_x + k)`: the probability that `B_y - A_x ≡ k (mod d)` for the settings `x`, `y`. -/
noncomputable def Strategy.probBA (S : Strategy d D) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((b : ℕ) : ZMod d) = ((a : ℕ) : ZMod d) + (k : ZMod d) then S.prob x y a b else 0

/-- The CGLMP expression, eq. (1) of `publish/CGLMP/paper-classical-all-d/main.tex`
(Collins et al. 2002, eq. (4), in the reading under which their local bound and the value of their
measurements are derived):
`I_d = ∑_{k=0}^{⌊d/2⌋-1} (1 - 2k/(d-1)) ([P(A_1 = B_1 + k) + P(B_1 = A_2 + k + 1) + P(A_2 = B_2 + k)
+ P(B_2 = A_1 + k)] - [P(A_1 = B_1 - k - 1) + P(B_1 = A_2 - k) + P(A_2 = B_2 - k - 1) + P(B_2 = A_1 - k - 1)])`.
Settings: `A_1, B_1` have index `0`, `A_2, B_2` have index `1`. -/
noncomputable def Strategy.cglmp (S : Strategy d D) : ℝ :=
  ∑ k ∈ range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
    ((S.probAB 0 0 k + S.probBA 1 0 (k + 1) + S.probAB 1 1 k + S.probBA 0 1 k) -
      (S.probAB 0 0 (-(k : ℤ) - 1) + S.probBA 1 0 (-(k : ℤ)) + S.probAB 1 1 (-(k : ℤ) - 1) +
        S.probBA 0 1 (-(k : ℤ) - 1)))

end Strategies

/-! ## The DKZ value `I_ME(d)` -/

/-- `I_ME(d) = 4/(d(d-1)) ∑_{j=1}^{d-1} (d - j) sec(π j/(2d))`, the CGLMP value of the DKZ measurements on
the maximally entangled state. -/
noncomputable def IME (d : ℕ) : ℝ :=
  4 / ((d : ℝ) * ((d : ℝ) - 1)) * ∑ j ∈ Ico 1 d, ((d : ℝ) - j) / Real.cos (π * j / (2 * d))

lemma IME_aux_sum_Ico (d : ℕ) : ∑ j ∈ Ico 1 d, ((d : ℝ) - j) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [Finset.sum_Ico_succ_top (by omega)]
    have : ∑ j ∈ Ico 1 n, ((((n + 1 : ℕ) : ℝ)) - j) = ∑ j ∈ Ico 1 n, (((n : ℝ) - j) + 1) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast; ring
    rw [this, Finset.sum_add_distrib, ih]
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring

/-- The local (classical) bound of the CGLMP inequality is `2`; the DKZ value exceeds it for every
`d ≥ 2`. -/
theorem IME_gt_two {d : ℕ} (hd : 2 ≤ d) : 2 < IME d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < (d : ℝ) * ((d : ℝ) - 1) := by nlinarith
  have hlt : ∑ j ∈ Ico 1 d, ((d : ℝ) - j) < ∑ j ∈ Ico 1 d, ((d : ℝ) - j) / Real.cos (π * j / (2 * d)) := by
    apply Finset.sum_lt_sum_of_nonempty ⟨1, by simp; omega⟩
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hjd : (j : ℝ) < d := by exact_mod_cast hj.2
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hθ0 : 0 < π * j / (2 * d) := by positivity
    have hθ1 : π * j / (2 * d) < π / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos]
    have hc0 : 0 < Real.cos (π * j / (2 * d)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩
    have hc1 : Real.cos (π * j / (2 * d)) < 1 := by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) hθ0
    rw [lt_div_iff₀ hc0]
    have : 0 < (d : ℝ) - j := by linarith
    nlinarith
  rw [IME_aux_sum_Ico] at hlt
  unfold IME
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  calc (2 : ℝ) = 4 / ((d : ℝ) * ((d : ℝ) - 1)) * ((d : ℝ) * ((d : ℝ) - 1) / 2) := by
        field_simp
        ring
    _ < _ := mul_lt_mul_of_pos_left hlt (by positivity)


/-! ## The DKZ strategy -/

section DKZ

variable {d : ℕ}

/-- `z = e^{2πi/(4d)}`, a primitive `4d`-th root of unity (`z^4 = e^{2πi/d}`, `z^d = i`). -/
noncomputable def zz (d : ℕ) : ℂ := Complex.exp (2 * π * I / ((4 * d : ℕ) : ℂ))

lemma zz_isPrimitiveRoot (hd : 0 < d) : IsPrimitiveRoot (zz d) (4 * d) :=
  Complex.isPrimitiveRoot_exp (4 * d) (by omega)

lemma zz_ne_zero : zz d ≠ 0 := Complex.exp_ne_zero _

lemma star_zz : star (zz d) = (zz d)⁻¹ := by
  rw [zz, ← Complex.exp_neg]
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

lemma star_zz_zpow (n : ℤ) : star (zz d ^ n) = zz d ^ (-n) := by
  rw [star_zpow₀, star_zz, _root_.inv_zpow']

/-- Powers of `z` only depend on the exponent modulo `4d`. -/
lemma zz_zpow_eq_of_dvd (hd : 0 < d) {a b : ℤ} (h : (4 * d : ℤ) ∣ a - b) :
    zz d ^ a = zz d ^ b := by
  have := (zz_isPrimitiveRoot hd).zpow_eq_one_iff_dvd (a - b)
  rw [zpow_sub₀ zz_ne_zero, div_eq_one_iff_eq (zpow_ne_zero _ zz_ne_zero)] at this
  exact this.2 (by exact_mod_cast h)

/-- Orthogonality of the characters of `ℤ/d`: `∑_{k<d} (z^{4r})^k = 0` unless `d ∣ r`. -/
lemma sum_zz_pow_four_mul (hd : 0 < d) {r : ℤ} (hr : ¬ (d : ℤ) ∣ r) :
    ∑ k ∈ range d, (zz d ^ (4 * r)) ^ k = 0 := by
  have hprim := zz_isPrimitiveRoot hd
  have h1 : zz d ^ (4 * r) ≠ 1 := by
    rw [Ne, hprim.zpow_eq_one_iff_dvd]
    intro h
    apply hr
    have h' : (4 : ℤ) * d ∣ 4 * r := by exact_mod_cast h
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).1 h'
  have hpow : (zz d ^ (4 * r)) ^ d = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, hprim.zpow_eq_one_iff_dvd]
    exact ⟨r, by push_cast; ring⟩
  rw [geom_sum_eq h1, hpow, sub_self, zero_div]

/-- The rank-one projector `E_c = (d^{-1} z^{(j - j') c})_{j, j'}` onto the unit vector
`d^{-1/2} (z^{j c})_j`. -/
noncomputable def phaseProj (d : ℕ) (c : ℤ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j j' => (d : ℂ)⁻¹ * zz d ^ ((((j : ℕ) : ℤ) - (j' : ℕ)) * c)

lemma phaseProj_isProj (hd : 0 < d) (c : ℤ) : IsProjection (phaseProj d c) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  constructor
  · ext j j'
    simp only [conjTranspose_apply, phaseProj, of_apply, star_mul', star_inv₀, star_natCast,
      star_zz_zpow]
    congr 2
    ring
  · ext j j''
    simp only [mul_apply, phaseProj, of_apply]
    calc ∑ j' : Fin d, (d : ℂ)⁻¹ * zz d ^ ((((j : ℕ) : ℤ) - (j' : ℕ)) * c) *
          ((d : ℂ)⁻¹ * zz d ^ ((((j' : ℕ) : ℤ) - (j'' : ℕ)) * c))
        = ∑ _j' : Fin d, (d : ℂ)⁻¹ * ((d : ℂ)⁻¹ * zz d ^ ((((j : ℕ) : ℤ) - (j'' : ℕ)) * c)) := by
          refine sum_congr rfl fun j' _ => ?_
          rw [show (((j : ℕ) : ℤ) - (j'' : ℕ)) * c =
              (((j : ℕ) : ℤ) - (j' : ℕ)) * c + (((j' : ℕ) : ℤ) - (j'' : ℕ)) * c by ring,
            zpow_add₀ zz_ne_zero]
          ring
      _ = (d : ℂ)⁻¹ * zz d ^ ((((j : ℕ) : ℤ) - (j'' : ℕ)) * c) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

/-- The projectors `E_{4σa + c₀}` (`a = 0, …, d-1`, `σ = ±1`) form a projective measurement. -/
lemma sum_phaseProj (hd : 0 < d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (c₀ : ℤ) :
    ∑ a : Fin d, phaseProj d (4 * σ * (a : ℕ) + c₀) = 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  ext j j'
  rw [Matrix.sum_apply]
  simp only [phaseProj, of_apply]
  by_cases hjj : j = j'
  · subst hjj
    simp only [sub_self, zero_mul, zpow_zero, mul_one, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, one_apply_eq]
    field_simp
  · rw [one_apply_ne hjj]
    set r : ℤ := (((j : ℕ) : ℤ) - (j' : ℕ)) * σ with hr
    have hterm : ∀ a : Fin d,
        (d : ℂ)⁻¹ * zz d ^ ((((j : ℕ) : ℤ) - (j' : ℕ)) * (4 * σ * (a : ℕ) + c₀)) =
        (d : ℂ)⁻¹ * zz d ^ ((((j : ℕ) : ℤ) - (j' : ℕ)) * c₀) * (zz d ^ (4 * r)) ^ (a : ℕ) := by
      intro a
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_assoc ((d : ℂ)⁻¹), ← zpow_add₀ zz_ne_zero]
      congr 2
      rw [hr]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun a => (zz d ^ (4 * r)) ^ a) d]
    have hndvd : ¬ (d : ℤ) ∣ r := by
      intro hdvd
      have hj1 := j.isLt
      have hj2 := j'.isLt
      have habs : |r| < d := by
        rw [hr, abs_mul]
        rcases hσ with h | h <;> subst h <;> simp only [abs_one, abs_neg, mul_one] <;>
          · rw [abs_lt]; constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      rw [hr] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact hjj (Fin.ext (by omega))
      · rcases hσ with h' | h' <;> omega
    rw [sum_zz_pow_four_mul hd hndvd, mul_zero]

/-- `4 α_x` for Alice's DKZ phases `α = (0, 1/2)`. -/
def alpha4 : Fin 2 → ℤ := ![0, 2]

/-- `4 β_y` for Bob's DKZ phases `β = (1/4, -1/4)`. -/
def beta4 : Fin 2 → ℤ := ![1, -1]

/-- Alice's DKZ projector for setting `x` and outcome `k`: `|k⟩_{A,x}⟨k|`, where
`|k⟩_{A,x} = d^{-1/2} ∑_j e^{-2πi j (k + α_x)/d} |j⟩` (see `dkzA_eq_vecMulVec`); its entries are
`d^{-1} z^{-(j - j')(4k + 4α_x)}`. -/
noncomputable def dkzA (d : ℕ) (x : Fin 2) (k : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  phaseProj d (-(4 * (k : ℕ) + alpha4 x))

/-- Bob's DKZ projector for setting `y` and outcome `l`: `|l⟩_{B,y}⟨l|`, where
`|l⟩_{B,y} = d^{-1/2} ∑_j e^{2πi j (l - β_y)/d} |j⟩` (see `dkzB_eq_vecMulVec`); its entries are
`d^{-1} z^{(j - j')(4l - 4β_y)}`. -/
noncomputable def dkzB (d : ℕ) (y : Fin 2) (l : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  phaseProj d (4 * (l : ℕ) - beta4 y)

/-- Alice's DKZ measurement for setting `x`. -/
noncomputable def dkzPVMA (d : ℕ) [NeZero d] (x : Fin 2) : PVM d d where
  proj := dkzA d x
  isProj _ := phaseProj_isProj (NeZero.pos d) _
  sum_eq_one := by
    rw [← sum_phaseProj (NeZero.pos d) (-1) (Or.inr rfl) (-alpha4 x)]
    refine sum_congr rfl fun k _ => ?_
    simp only [dkzA]
    congr 1
    ring

/-- Bob's DKZ measurement for setting `y`. -/
noncomputable def dkzPVMB (d : ℕ) [NeZero d] (y : Fin 2) : PVM d d where
  proj := dkzB d y
  isProj _ := phaseProj_isProj (NeZero.pos d) _
  sum_eq_one := by
    rw [← sum_phaseProj (NeZero.pos d) 1 (Or.inl rfl) (-beta4 y)]
    refine sum_congr rfl fun l _ => ?_
    simp only [dkzB]
    congr 1
    try ring

/-- The DKZ strategy on `Φ_d` (the measurements of Collins et al. 2002, eqs. (12)-(15)). -/
noncomputable def dkz (d : ℕ) [NeZero d] : Strategy d d where
  A := dkzPVMA d
  B := dkzPVMB d

end DKZ

/-! ## The value of the DKZ strategy -/

section DKZValue

variable {d : ℕ}

/-! ### Elementary sums -/

lemma dkz_aux_geom_mul (x : ℂ) (n : ℕ) :
    (x - 1) * ∑ t ∈ range n, (t : ℂ) * x ^ t = ((n : ℂ) - 1) * x ^ n - ∑ t ∈ range n, x ^ t + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- `∑_{t<n} t x^t = n/(x - 1)` for an `n`-th root of unity `x ≠ 1`. -/
lemma dkz_sum_mul_pow_root {x : ℂ} {n : ℕ} (hx : x ^ n = 1) (hx1 : x ≠ 1) :
    ∑ t ∈ range n, (t : ℂ) * x ^ t = n / (x - 1) := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hg : ∑ t ∈ range n, x ^ t = 0 := by rw [geom_sum_eq hx1, hx, sub_self, zero_div]
  have h := dkz_aux_geom_mul x n
  rw [hx, hg] at h
  rw [eq_div_iff h1]
  linear_combination h

/-- Summing a function of `j' - j` over `0 ≤ j, j' < n`. -/
lemma dkz_sum_sum_sub {R : Type*} [CommRing R] (ψ : ℤ → R) (n : ℕ) :
    ∑ j ∈ range n, ∑ j' ∈ range n, ψ ((j' : ℤ) - j) + n * ψ 0 =
      ∑ m ∈ range n, ((n : R) - m) * (ψ m + ψ (-m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hB : ∑ j ∈ range (n + 1), ψ ((n : ℤ) - j) = ∑ m ∈ range (n + 1), ψ m := by
      rw [← sum_range_reflect (fun m : ℕ => ψ m) (n + 1)]
      refine sum_congr rfl fun j hj => ?_
      have := mem_range.1 hj
      congr 1
      omega
    have hC : ∑ j' ∈ range (n + 1), ψ ((j' : ℤ) - n) = ∑ m ∈ range (n + 1), ψ (-(m : ℤ)) := by
      rw [← sum_range_reflect (fun m : ℕ => ψ (-(m : ℤ))) (n + 1)]
      refine sum_congr rfl fun j hj => ?_
      have := mem_range.1 hj
      congr 1
      omega
    rw [sum_range_succ, sub_self] at hB hC
    have hL : ∑ j ∈ range (n + 1), ∑ j' ∈ range (n + 1), ψ ((j' : ℤ) - j) =
        ∑ j ∈ range n, ∑ j' ∈ range n, ψ ((j' : ℤ) - j) + ∑ j ∈ range n, ψ ((n : ℤ) - j) +
          ∑ j' ∈ range n, ψ ((j' : ℤ) - n) + ψ 0 := by
      simp only [sum_range_succ, sum_add_distrib, sub_self]
      ring
    have hR : ∑ m ∈ range (n + 1), (((n + 1 : ℕ) : R) - m) * (ψ m + ψ (-m)) =
        ∑ m ∈ range n, ((n : R) - m) * (ψ m + ψ (-m)) + ∑ m ∈ range (n + 1), ψ m +
          ∑ m ∈ range (n + 1), ψ (-(m : ℤ)) := by
      have e : ∀ m : ℕ, (((n + 1 : ℕ) : R) - m) * (ψ m + ψ (-m)) =
          ((n : R) - m) * (ψ m + ψ (-m)) + ψ m + ψ (-(m : ℤ)) := by
        intro m; push_cast; ring
      simp_rw [e, sum_add_distrib]
      rw [sum_range_succ (fun m : ℕ => ((n : R) - m) * (ψ m + ψ (-m))) n]
      simp
    rw [hL, hR]
    push_cast
    linear_combination ih + hB + hC

/-! ### The difference distribution of the DKZ strategy -/

/-- `q(c) = d^{-2} ∑_{j, j'} z^{(j' - j) c}`; the DKZ difference distributions are values of `q`. -/
noncomputable def dkzQ (d : ℕ) (c : ℤ) : ℂ :=
  (d : ℂ)⁻¹ ^ 2 * ∑ j : Fin d, ∑ j' : Fin d, zz d ^ ((((j' : ℕ) : ℤ) - (j : ℕ)) * c)

lemma dkzQ_neg (c : ℤ) : dkzQ d (-c) = dkzQ d c := by
  unfold dkzQ
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
  congr 1
  ring

lemma dkzQ_congr [NeZero d] {c c' : ℤ} (h : (4 * d : ℤ) ∣ c - c') : dkzQ d c = dkzQ d c' := by
  unfold dkzQ
  congr 1
  refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
  apply zz_zpow_eq_of_dvd (NeZero.pos d)
  rw [← mul_sub]
  exact Dvd.dvd.mul_left h _

lemma trace_transpose_phaseProj_mul (c c' : ℤ) :
    ((phaseProj d c)ᵀ * phaseProj d c').trace = dkzQ d (c + c') := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, transpose_apply, phaseProj, of_apply, dkzQ]
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j' _ => ?_
  rw [mul_add, zpow_add₀ zz_ne_zero]
  ring

lemma dkz_prob [NeZero d] (x y : Fin 2) (a b : Fin d) :
    ((dkz d).prob x y a b : ℂ) =
      (d : ℂ)⁻¹ * dkzQ d (-(4 * (((a : ℕ) : ℤ) - (b : ℕ)) + (alpha4 x + beta4 y))) := by
  rw [Strategy.prob_eq]
  simp only [dkz, dkzPVMA, dkzPVMB, dkzA, dkzB, trace_transpose_phaseProj_mul]
  rw [div_eq_inv_mul]
  congr 2
  ring

lemma dkz_zmod_eq_add_iff [NeZero d] (a b : ℕ) (t : ℤ) :
    ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) + (t : ZMod d) ↔ (d : ℤ) ∣ (a : ℤ) - b - t := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor <;> intro h <;> linear_combination h

lemma dkz_sum_fin_ite_eq [NeZero d] (c : ZMod d) :
    ∑ a : Fin d, (if ((a : ℕ) : ZMod d) = c then (1 : ℂ) else 0) = 1 := by
  have key : ∀ a : Fin d, ((a : ℕ) : ZMod d) = c ↔ a = ⟨c.val, ZMod.val_lt c⟩ := by
    intro a
    constructor
    · intro h
      ext
      simp only
      rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
    · intro h
      subst h
      simp
  simp_rw [key]
  simp

lemma dkz_probAB [NeZero d] (x y : Fin 2) (t : ℤ) :
    ((dkz d).probAB x y t : ℂ) = dkzQ d (-(4 * t + (alpha4 x + beta4 y))) := by
  set K := dkzQ d (-(4 * t + (alpha4 x + beta4 y)))
  have hterm : ∀ a b : Fin d,
      ((if ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) + (t : ZMod d) then (dkz d).prob x y a b
        else 0 : ℝ) : ℂ) =
      (if ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) + (t : ZMod d) then (1 : ℂ) else 0) *
        ((d : ℂ)⁻¹ * K) := by
    intro a b
    split_ifs with h
    · rw [one_mul, dkz_prob]
      congr 1
      apply dkzQ_congr
      obtain ⟨k, hk⟩ := (dkz_zmod_eq_add_iff (a : ℕ) (b : ℕ) t).1 h
      exact ⟨-k, by linear_combination (-4 : ℤ) * hk⟩
    · simp
  unfold Strategy.probAB
  push_cast
  simp_rw [hterm, ← sum_mul]
  rw [sum_comm]
  simp_rw [dkz_sum_fin_ite_eq]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

lemma dkz_probBA [NeZero d] (x y : Fin 2) (t : ℤ) :
    ((dkz d).probBA x y t : ℂ) = dkzQ d (4 * t - (alpha4 x + beta4 y)) := by
  set K := dkzQ d (4 * t - (alpha4 x + beta4 y))
  have hterm : ∀ a b : Fin d,
      ((if ((b : ℕ) : ZMod d) = ((a : ℕ) : ZMod d) + (t : ZMod d) then (dkz d).prob x y a b
        else 0 : ℝ) : ℂ) =
      (if ((b : ℕ) : ZMod d) = ((a : ℕ) : ZMod d) + (t : ZMod d) then (1 : ℂ) else 0) *
        ((d : ℂ)⁻¹ * K) := by
    intro a b
    split_ifs with h
    · rw [one_mul, dkz_prob]
      congr 1
      apply dkzQ_congr
      obtain ⟨k, hk⟩ := (dkz_zmod_eq_add_iff (b : ℕ) (a : ℕ) t).1 h
      exact ⟨k, by linear_combination (4 : ℤ) * hk⟩
    · simp
  unfold Strategy.probBA
  push_cast
  simp_rw [hterm, ← sum_mul, dkz_sum_fin_ite_eq]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp


/-- The four difference distributions entering `I_d` coincide for the DKZ strategy. -/
lemma dkz_pair_values [NeZero d] (t : ℤ) :
    ((dkz d).probAB 0 0 t : ℂ) = dkzQ d (4 * t + 1) ∧
    ((dkz d).probBA 1 0 (t + 1) : ℂ) = dkzQ d (4 * t + 1) ∧
    ((dkz d).probAB 1 1 t : ℂ) = dkzQ d (4 * t + 1) ∧
    ((dkz d).probBA 0 1 t : ℂ) = dkzQ d (4 * t + 1) := by
  have a0 : alpha4 0 = 0 := rfl
  have a1 : alpha4 1 = 2 := rfl
  have b0 : beta4 0 = 1 := rfl
  have b1 : beta4 1 = -1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : -(4 * t + (alpha4 0 + beta4 0)) = -(4 * t + 1) := by rw [a0, b0]; ring
    rw [dkz_probAB, e, dkzQ_neg]
  · have e : 4 * (t + 1) - (alpha4 1 + beta4 0) = 4 * t + 1 := by rw [a1, b0]; ring
    rw [dkz_probBA, e]
  · have e : -(4 * t + (alpha4 1 + beta4 1)) = -(4 * t + 1) := by rw [a1, b1]; ring
    rw [dkz_probAB, e, dkzQ_neg]
  · have e : 4 * t - (alpha4 0 + beta4 1) = 4 * t + 1 := by rw [a0, b1]; ring
    rw [dkz_probBA, e]

/-! ### Lemma 2.1 of the paper in the form used here -/

/-- Folding a sum over `range d` at its middle. -/
lemma cglmp_sum_range_fold (φ : ℕ → ℝ) (d : ℕ) :
    ∑ j ∈ range d, φ j = ∑ k ∈ range (d / 2), (φ k + φ (d - 1 - k))
      + (if d % 2 = 1 then φ (d / 2) else 0) := by
  set h := d / 2 with hh
  rcases Nat.even_or_odd d with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hrh : r = h := by omega
    subst hrh
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

/-- The weights `1 - 2k/(d-1)` of the CGLMP expression fold into `1 - 2t/(d-1)` on all residues `t`
(proof of Lemma 2.1 of `paper-classical-all-d/main.tex`). -/
lemma fold_cglmp_weights (hd : 2 ≤ d) (g : ℤ → ℝ)
    (hg : ∀ k k' : ℤ, (k : ZMod d) = k' → g k = g k') :
    ∑ k ∈ range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) * (g k - g (-(k : ℤ) - 1)) =
      ∑ t ∈ range d, (1 - 2 * (t : ℝ) / ((d : ℝ) - 1)) * g t := by
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [cglmp_sum_range_fold (fun t : ℕ => (1 - 2 * (t : ℝ) / ((d : ℝ) - 1)) * g (t : ℤ)) d]
  have hmid : (if d % 2 = 1 then (1 - 2 * ((d / 2 : ℕ) : ℝ) / ((d : ℝ) - 1)) *
      g ((d / 2 : ℕ) : ℤ) else 0) = 0 := by
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
  have hcast : ((d - 1 - k : ℕ) : ℝ) = (d : ℝ) - 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hz : g ((d - 1 - k : ℕ) : ℤ) = g (-(k : ℤ) - 1) := by
    apply hg
    have e : ((d - 1 - k + k + 1 : ℕ) : ZMod d) = 0 := by
      rw [show d - 1 - k + k + 1 = d by omega, ZMod.natCast_self]
    push_cast at e ⊢
    linear_combination e
  rw [hcast, hz]
  field_simp
  ring

/-- Lemma 2.1 of `paper-classical-all-d/main.tex` (first step): the CGLMP expression as a sum over
residues `t`, with the weights `1 - 2t/(d-1)` and the four difference distributions
`P(A_1 - B_1 ≡ t)`, `P(B_1 - A_2 - 1 ≡ t)`, `P(A_2 - B_2 ≡ t)`, `P(B_2 - A_1 ≡ t)`. -/
theorem Strategy.cglmp_eq_sum_range {D : ℕ} (S : Strategy d D) (hd : 2 ≤ d) :
    S.cglmp = ∑ t ∈ range d, (1 - 2 * (t : ℝ) / ((d : ℝ) - 1)) *
      (S.probAB 0 0 t + S.probBA 1 0 ((t : ℤ) + 1) + S.probAB 1 1 t + S.probBA 0 1 t) := by
  have p1 : ∀ x y, ∀ k k' : ℤ, (k : ZMod d) = k' → S.probAB x y k = S.probAB x y k' := by
    intro x y k k' h
    simp only [Strategy.probAB, h]
  have p2 : ∀ x y, ∀ k k' : ℤ, (k : ZMod d) = k' → S.probBA x y k = S.probBA x y k' := by
    intro x y k k' h
    simp only [Strategy.probBA, h]
  have p2' : ∀ k k' : ℤ, (k : ZMod d) = k' → S.probBA 1 0 (k + 1) = S.probBA 1 0 (k' + 1) := by
    intro k k' h
    apply p2
    push_cast
    rw [h]
  have e1 := fold_cglmp_weights hd (fun k => S.probAB 0 0 k) (p1 0 0)
  have e2 := fold_cglmp_weights hd (fun k => S.probBA 1 0 (k + 1)) p2'
  have e3 := fold_cglmp_weights hd (fun k => S.probAB 1 1 k) (p1 1 1)
  have e4 := fold_cglmp_weights hd (fun k => S.probBA 0 1 k) (p2 0 1)
  have h2 : ∀ k : ℕ, S.probBA 1 0 (-(k : ℤ) - 1 + 1) = S.probBA 1 0 (-(k : ℤ)) := by
    intro k
    congr 1
    ring
  simp only [h2] at e2
  unfold Strategy.cglmp
  calc ∑ k ∈ range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
        ((S.probAB 0 0 k + S.probBA 1 0 (k + 1) + S.probAB 1 1 k + S.probBA 0 1 k) -
          (S.probAB 0 0 (-(k : ℤ) - 1) + S.probBA 1 0 (-(k : ℤ)) + S.probAB 1 1 (-(k : ℤ) - 1) +
            S.probBA 0 1 (-(k : ℤ) - 1)))
      = ∑ k ∈ range (d / 2), ((1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
            (S.probAB 0 0 k - S.probAB 0 0 (-(k : ℤ) - 1)) +
          (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) * (S.probBA 1 0 (k + 1) - S.probBA 1 0 (-(k : ℤ))) +
          (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
            (S.probAB 1 1 k - S.probAB 1 1 (-(k : ℤ) - 1)) +
          (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
            (S.probBA 0 1 k - S.probBA 0 1 (-(k : ℤ) - 1))) := by
        refine sum_congr rfl fun k _ => ?_
        ring
    _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, e1, e2, e3, e4,
          ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun t _ => ?_
        ring

/-! ### Closed forms -/

lemma dkzQ_eq_range (c : ℤ) :
    dkzQ d c = (d : ℂ)⁻¹ ^ 2 * ∑ j ∈ range d, ∑ j' ∈ range d, zz d ^ (((j' : ℤ) - j) * c) := by
  unfold dkzQ
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∑ j' : Fin d, zz d ^ ((((j' : ℕ) : ℤ) - j) * c))]
  refine sum_congr rfl fun j _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun j' : ℕ => zz d ^ (((j' : ℤ) - j) * c)) d

lemma zz_zpow_four_mul_ne_one [NeZero d] {r : ℤ} (hr : ¬ (d : ℤ) ∣ r) : zz d ^ (4 * r) ≠ 1 := by
  rw [Ne, (zz_isPrimitiveRoot (NeZero.pos d)).zpow_eq_one_iff_dvd]
  intro h
  apply hr
  have h' : (4 : ℤ) * d ∣ 4 * r := by exact_mod_cast h
  exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).1 h'

lemma zz_zpow_four_mul_pow_d [NeZero d] (r : ℤ) : (zz d ^ (4 * r)) ^ d = 1 := by
  rw [← zpow_natCast, ← _root_.zpow_mul, (zz_isPrimitiveRoot (NeZero.pos d)).zpow_eq_one_iff_dvd]
  exact ⟨r, by push_cast; ring⟩

lemma zz_zpow_mul_four_add_one (r : ℤ) (t : ℕ) :
    zz d ^ (r * (4 * t + 1)) = zz d ^ r * (zz d ^ (4 * r)) ^ t := by
  rw [← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ zz_ne_zero]
  congr 1
  ring

lemma dkz_not_dvd_of_abs_lt [NeZero d] {r : ℤ} (h0 : r ≠ 0) (h1 : |r| < d) : ¬ (d : ℤ) ∣ r :=
  fun h => h0 (Int.eq_zero_of_abs_lt_dvd h h1)

/-- `∑_{t<d} z^{r(4t+1)} = 0` for `0 < |r| < d`. -/
lemma sum_zz_zpow_four_add_one [NeZero d] {r : ℤ} (hr : ¬ (d : ℤ) ∣ r) :
    ∑ t ∈ range d, zz d ^ (r * (4 * (t : ℤ) + 1)) = 0 := by
  simp_rw [zz_zpow_mul_four_add_one, ← mul_sum]
  rw [sum_zz_pow_four_mul (NeZero.pos d) hr, mul_zero]

/-- `∑_{t<d} t z^{r(4t+1)} = d z^r / (z^{4r} - 1)` for `0 < |r| < d`. -/
lemma sum_mul_zz_zpow_four_add_one [NeZero d] {r : ℤ} (hr : ¬ (d : ℤ) ∣ r) :
    ∑ t ∈ range d, (t : ℂ) * zz d ^ (r * (4 * (t : ℤ) + 1)) =
      zz d ^ r * ((d : ℂ) / (zz d ^ (4 * r) - 1)) := by
  simp_rw [zz_zpow_mul_four_add_one]
  rw [← dkz_sum_mul_pow_root (zz_zpow_four_mul_pow_d r) (zz_zpow_four_mul_ne_one hr),
    mul_sum]
  refine sum_congr rfl fun t _ => ?_
  ring

lemma dkz_pair_identity_alg (a D : ℂ) (ha : a ≠ 0) (h4 : a ^ 4 ≠ 1) (h2 : a ^ 2 + 1 ≠ 0) :
    a * (D / (a ^ 4 - 1)) + a⁻¹ * (D / (a⁻¹ ^ 4 - 1)) = -D / (a + a⁻¹) := by
  have h41 : a ^ 4 - 1 ≠ 0 := sub_ne_zero.2 h4
  have h3 : a ^ 2 - 1 ≠ 0 := by
    intro h
    apply h41
    have : a ^ 4 - 1 = (a ^ 2 - 1) * (a ^ 2 + 1) := by ring
    rw [this, h, zero_mul]
  have h5 : a⁻¹ ^ 4 - 1 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply h41
    have : (a ^ 4)⁻¹ = 1 := by linear_combination h
    rw [inv_eq_one] at this
    rw [this, sub_self]
  have h6 : a + a⁻¹ ≠ 0 := by
    intro h
    apply h2
    have : a ^ 2 + 1 = a * (a + a⁻¹) := by field_simp
    rw [this, h, mul_zero]
  field_simp
  ring

lemma zz_zpow_add_zpow_neg [NeZero d] (m : ℤ) :
    zz d ^ m + zz d ^ (-m) = 2 * ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [Complex.ofReal_cos, Complex.two_cos, zz, ← Complex.exp_int_mul, ← Complex.exp_int_mul]
  congr 1
  · congr 1
    push_cast
    field_simp
    ring
  · congr 1
    push_cast
    field_simp
    ring

lemma zz_pow_add_pow_neg_nat [NeZero d] (m : ℕ) :
    zz d ^ (m : ℤ) + zz d ^ (-(m : ℤ)) = 2 * ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ) := by
  have h := zz_zpow_add_zpow_neg (d := d) (m : ℤ)
  simp only [Int.cast_natCast] at h
  exact h

/-- For `1 ≤ m < d`: `ψ(m) + ψ(-m) = -d / (2 cos(π m/(2d)))`, `ψ(r) = ∑_{t<d} t z^{r(4t+1)}`. -/
lemma pair_sum_mul [NeZero d] {m : ℕ} (hm0 : 1 ≤ m) (hm : m < d) :
    ∑ t ∈ range d, (t : ℂ) * zz d ^ ((m : ℤ) * (4 * (t : ℤ) + 1)) +
      ∑ t ∈ range d, (t : ℂ) * zz d ^ (-(m : ℤ) * (4 * (t : ℤ) + 1)) =
      -(d : ℂ) / (2 * ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ)) := by
  have hnd : ¬ (d : ℤ) ∣ (m : ℤ) :=
    dkz_not_dvd_of_abs_lt (by omega) (by rw [abs_of_nonneg (by omega)]; exact_mod_cast hm)
  have hnd' : ¬ (d : ℤ) ∣ -(m : ℤ) := by rwa [Int.dvd_neg]
  rw [sum_mul_zz_zpow_four_add_one hnd, sum_mul_zz_zpow_four_add_one hnd',
    ← zz_pow_add_pow_neg_nat m]
  set a := zz d ^ (m : ℤ) with ha_def
  have ha : a ≠ 0 := zpow_ne_zero _ zz_ne_zero
  have e1 : zz d ^ (4 * (m : ℤ)) = a ^ 4 := by rw [ha_def, ← zpow_natCast, ← _root_.zpow_mul]; ring_nf
  have e2 : zz d ^ (-(m : ℤ)) = a⁻¹ := by rw [ha_def, _root_.zpow_neg]
  have e3 : zz d ^ (4 * -(m : ℤ)) = a⁻¹ ^ 4 := by
    rw [← e2, ← zpow_natCast, ← _root_.zpow_mul]; ring_nf
  have h4 : a ^ 4 ≠ 1 := by rw [← e1]; exact zz_zpow_four_mul_ne_one hnd
  have h2 : a ^ 2 + 1 ≠ 0 := by
    intro h
    apply h4
    have : a ^ 2 = -1 := by linear_combination h
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, this]
    norm_num
  rw [e1, e2, e3]
  exact dkz_pair_identity_alg a d ha h4 h2

/-- `∑_{t<d} q(4t+1) = 1`. -/
lemma sum_dkzQ [NeZero d] : ∑ t ∈ range d, dkzQ d (4 * (t : ℤ) + 1) = 1 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  set ψ : ℤ → ℂ := fun r => ∑ t ∈ range d, zz d ^ (r * (4 * (t : ℤ) + 1)) with hψdef
  have hswap : ∑ t ∈ range d, dkzQ d (4 * (t : ℤ) + 1) =
      (d : ℂ)⁻¹ ^ 2 * ∑ j ∈ range d, ∑ j' ∈ range d, ψ ((j' : ℤ) - j) := by
    simp_rw [dkzQ_eq_range]
    rw [← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
  have hψ := dkz_sum_sum_sub ψ d
  have h0 : ψ 0 = d := by simp [hψdef]
  have hR : ∑ m ∈ range d, ((d : ℂ) - m) * (ψ m + ψ (-m)) = (d : ℂ) * (2 * d) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (NeZero.pos d)]
    have hz : ∑ m ∈ Ico (0 + 1) d, ((d : ℂ) - m) * (ψ m + ψ (-m)) = 0 := by
      refine sum_eq_zero fun m hm => ?_
      have hm' := mem_Ico.1 hm
      have hnd : ¬ (d : ℤ) ∣ (m : ℤ) :=
        dkz_not_dvd_of_abs_lt (by omega) (by rw [abs_of_nonneg (by omega)]; exact_mod_cast hm'.2)
      have hnd' : ¬ (d : ℤ) ∣ -(m : ℤ) := by rwa [Int.dvd_neg]
      rw [hψdef]
      simp only
      rw [sum_zz_zpow_four_add_one hnd, sum_zz_zpow_four_add_one hnd', add_zero, mul_zero]
    rw [hz, add_zero]
    simp only [Nat.cast_zero, sub_zero, neg_zero]
    rw [h0]
    ring
  rw [hR, h0] at hψ
  rw [hswap]
  have : ∑ j ∈ range d, ∑ j' ∈ range d, ψ ((j' : ℤ) - j) = (d : ℂ) ^ 2 := by
    linear_combination hψ
  rw [this]
  field_simp

/-- `∑_{t<d} t q(4t+1) = (d-1)/2 - (1/d) ∑_{m=1}^{d-1} (d - m)/(2 cos(π m/(2d)))`. -/
lemma sum_mul_dkzQ [NeZero d] :
    ∑ t ∈ range d, (t : ℂ) * dkzQ d (4 * (t : ℤ) + 1) =
      ((d : ℂ) - 1) / 2 - (d : ℂ)⁻¹ * ∑ m ∈ Ico 1 d,
        ((d : ℂ) - m) / (2 * ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ)) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  set ψ : ℤ → ℂ := fun r => ∑ t ∈ range d, (t : ℂ) * zz d ^ (r * (4 * (t : ℤ) + 1)) with hψdef
  have hswap : ∑ t ∈ range d, (t : ℂ) * dkzQ d (4 * (t : ℤ) + 1) =
      (d : ℂ)⁻¹ ^ 2 * ∑ j ∈ range d, ∑ j' ∈ range d, ψ ((j' : ℤ) - j) := by
    have e : ∀ t ∈ range d, (t : ℂ) * dkzQ d (4 * (t : ℤ) + 1) = (d : ℂ)⁻¹ ^ 2 *
        ∑ j ∈ range d, ∑ j' ∈ range d, (t : ℂ) * zz d ^ (((j' : ℤ) - j) * (4 * (t : ℤ) + 1)) := by
      intro t _
      rw [dkzQ_eq_range, mul_left_comm, mul_sum]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]
    rw [sum_congr rfl e, ← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
  have hψ := dkz_sum_sum_sub ψ d
  have h0 : ψ 0 = (d : ℂ) * ((d : ℂ) - 1) / 2 := by
    have h1 : ψ 0 = ∑ t ∈ range d, (t : ℂ) := by
      simp only [hψdef, zero_mul, zpow_zero, mul_one]
    rw [h1]
    have h2 := Finset.sum_range_id_mul_two d
    have h3 : ((∑ i ∈ range d, i : ℕ) : ℂ) * 2 = ((d * (d - 1) : ℕ) : ℂ) := by exact_mod_cast h2
    rw [Nat.cast_mul, Nat.cast_sub (NeZero.pos d), Nat.cast_sum, Nat.cast_one] at h3
    linear_combination h3 / 2
  have hR : ∑ m ∈ range d, ((d : ℂ) - m) * (ψ m + ψ (-m)) = (d : ℂ) * (2 * ψ 0) +
      ∑ m ∈ Ico 1 d, ((d : ℂ) - m) * (ψ m + ψ (-m)) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (NeZero.pos d)]
    simp only [Nat.cast_zero, sub_zero, neg_zero, zero_add]
    ring
  have hpairs : ∑ m ∈ Ico 1 d, ((d : ℂ) - m) * (ψ m + ψ (-m)) = -(d : ℂ) * ∑ m ∈ Ico 1 d,
      ((d : ℂ) - m) / (2 * ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ)) := by
    rw [mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm' := mem_Ico.1 hm
    rw [hψdef]
    simp only
    rw [pair_sum_mul hm'.1 hm'.2]
    ring
  rw [hR, hpairs] at hψ
  rw [hswap]
  have hsum : ∑ j ∈ range d, ∑ j' ∈ range d, ψ ((j' : ℤ) - j) = (d : ℂ) * ψ 0 -
      (d : ℂ) * ∑ m ∈ Ico 1 d, ((d : ℂ) - m) / (2 * ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ)) := by
    linear_combination hψ
  rw [hsum, h0]
  field_simp

/-- **The DKZ strategy attains `I_ME(d)`** for every `d ≥ 2` (the value of the measurements of
Collins et al. (2002), eqs. (12)-(15); `paper-classical-all-d/main.tex`, Section 2.4). -/
theorem dkz_cglmp [NeZero d] (hd : 2 ≤ d) : (dkz d).cglmp = IME d := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((d : ℝ) : ℂ) - 1 = 0 := by exact_mod_cast h
    have h'' : (d : ℝ) - 1 = 0 := by exact_mod_cast h'
    linarith
  apply Complex.ofReal_injective
  rw [Strategy.cglmp_eq_sum_range _ hd]
  simp only [IME, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_add]
  have e : ∀ t ∈ range d, (1 - 2 * (t : ℂ) / ((d : ℂ) - 1)) *
      (((dkz d).probAB 0 0 t : ℂ) + ((dkz d).probBA 1 0 ((t : ℤ) + 1) : ℂ) +
        ((dkz d).probAB 1 1 t : ℂ) + ((dkz d).probBA 0 1 t : ℂ)) =
      4 * dkzQ d (4 * (t : ℤ) + 1) - 8 / ((d : ℂ) - 1) * ((t : ℂ) * dkzQ d (4 * (t : ℤ) + 1)) := by
    intro t _
    obtain ⟨h1, h2, h3, h4⟩ := dkz_pair_values (d := d) (t : ℤ)
    rw [h1, h2, h3, h4]
    ring
  rw [sum_congr rfl e, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_dkzQ, sum_mul_dkzQ]
  have hS : ∑ m ∈ Ico 1 d, ((d : ℂ) - m) / (2 * ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ)) =
      1 / 2 * ∑ m ∈ Ico 1 d, ((d : ℂ) - m) / ((Real.cos (π * m / (2 * d)) : ℝ) : ℂ) := by
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [hS]
  field_simp
  ring


/-! ### The DKZ projectors are the projectors onto the DKZ basis vectors -/

/-- Alice's DKZ basis vector `|k⟩_{A,x} = d^{-1/2} ∑_j e^{-2πi j (k + α_x)/d} |j⟩`, `α = (0, 1/2)`. -/
noncomputable def dkzVecA (d : ℕ) (x : Fin 2) (k : Fin d) : Fin d → ℂ := fun j =>
  ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
    Complex.exp (-(2 * π * I * ((j : ℕ) : ℂ) * (((k : ℕ) : ℂ) + (alpha4 x : ℂ) / 4) / d))

/-- Bob's DKZ basis vector `|l⟩_{B,y} = d^{-1/2} ∑_j e^{2πi j (l - β_y)/d} |j⟩`, `β = (1/4, -1/4)`. -/
noncomputable def dkzVecB (d : ℕ) (y : Fin 2) (l : Fin d) : Fin d → ℂ := fun j =>
  ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * π * I * ((j : ℕ) : ℂ) * (((l : ℕ) : ℂ) - (beta4 y : ℂ) / 4) / d)

lemma dkz_sqrt_inv_mul_self [NeZero d] :
    ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹ = (d : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  push_cast
  rfl

lemma dkz_star_sqrt_inv : star (((Real.sqrt d : ℝ) : ℂ)⁻¹) = ((Real.sqrt d : ℝ) : ℂ)⁻¹ := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

lemma zz_zpow_eq_exp (n : ℤ) : zz d ^ n = Complex.exp (n * (2 * π * I / ((4 * d : ℕ) : ℂ))) := by
  rw [zz, Complex.exp_int_mul]

/-- `A^DKZ_{x,k} = |k⟩_{A,x}⟨k|`. -/
theorem dkzA_eq_vecMulVec [NeZero d] (x : Fin 2) (k : Fin d) :
    dkzA d x k = vecMulVec (dkzVecA d x k) (star (dkzVecA d x k)) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  ext j j'
  simp only [dkzA, phaseProj, of_apply, vecMulVec_apply, Pi.star_apply, dkzVecA, star_mul',
    dkz_star_sqrt_inv]
  rw [show star (Complex.exp (-(2 * π * I * ((j' : ℕ) : ℂ) * (((k : ℕ) : ℂ) + (alpha4 x : ℂ) / 4) /
      d))) = Complex.exp (2 * π * I * ((j' : ℕ) : ℂ) * (((k : ℕ) : ℂ) + (alpha4 x : ℂ) / 4) / d) by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [map_div₀, Complex.conj_ofReal, map_intCast, map_ofNat]
    ring]
  rw [mul_mul_mul_comm, dkz_sqrt_inv_mul_self, ← Complex.exp_add, zz_zpow_eq_exp]
  congr 2
  push_cast
  field_simp
  ring

/-- `B^DKZ_{y,l} = |l⟩_{B,y}⟨l|`. -/
theorem dkzB_eq_vecMulVec [NeZero d] (y : Fin 2) (l : Fin d) :
    dkzB d y l = vecMulVec (dkzVecB d y l) (star (dkzVecB d y l)) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  ext j j'
  simp only [dkzB, phaseProj, of_apply, vecMulVec_apply, Pi.star_apply, dkzVecB, star_mul',
    dkz_star_sqrt_inv]
  rw [show star (Complex.exp (2 * π * I * ((j' : ℕ) : ℂ) * (((l : ℕ) : ℂ) - (beta4 y : ℂ) / 4) /
      d)) = Complex.exp (-(2 * π * I * ((j' : ℕ) : ℂ) * (((l : ℕ) : ℂ) - (beta4 y : ℂ) / 4) / d)) by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [map_div₀, Complex.conj_ofReal, map_intCast, map_ofNat]
    ring]
  rw [mul_mul_mul_comm, dkz_sqrt_inv_mul_self, ← Complex.exp_add, zz_zpow_eq_exp]
  congr 2
  push_cast
  field_simp
  ring

end DKZValue

/-! ## The statements -/

section Statements

variable {d D : ℕ}

/-- `S` is, up to a local unitary `u ⊗ ū`, the DKZ strategy tensored with the identity on `ℂ^K`
(`D = d K`): there is a unitary `u : ℂ^D → ℂ^d ⊗ ℂ^K` with `u A_{x,a} u† = A^DKZ_{x,a} ⊗ 1_K` and
`ū B_{y,b} ū† = B^DKZ_{y,b} ⊗ 1_K`, where `ū` is the entrywise complex conjugate of `u` in the Schmidt
basis of `Φ_D`.  Then `(u ⊗ ū) Φ_D = Φ_d ⊗ Φ_K`. -/
def Strategy.IsDKZTensorId (S : Strategy d D) : Prop :=
  ∃ K : ℕ, D = d * K ∧ ∃ u : Matrix (Fin d × Fin K) (Fin D) ℂ,
    u * uᴴ = 1 ∧ uᴴ * u = 1 ∧
    (∀ x a, u * (S.A x).proj a * uᴴ = dkzA d x a ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) ∧
    (∀ y b, u.map star * (S.B y).proj b * (u.map star)ᴴ =
      dkzB d y b ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ))

theorem Strategy.IsDKZTensorId.dvd {S : Strategy d D} (h : S.IsDKZTensorId) : d ∣ D := by
  obtain ⟨K, hK, -⟩ := h
  exact ⟨K, hK⟩

/-- OPTIMALITY (max-ent clause of OQP 27B, `d` outcomes): for every local dimension `D ≥ 1` and every
projective strategy on the maximally entangled state `Φ_D`, `I_d ≤ I_ME(d)`. -/
def OptimalityStatement (d : ℕ) : Prop :=
  ∀ D : ℕ, 0 < D → ∀ S : Strategy d D, S.cglmp ≤ IME d

/-- RIGIDITY: every projective strategy on `Φ_D` attaining `I_ME(d)` has `d ∣ D` and is the DKZ strategy
tensored with the identity, up to a local unitary `u ⊗ ū` (Theorem R of `Q_rig/RIGIDITY_ALLD.md`,
Theorem C of `publish/CGLMP/rigidity/RIGIDITY.md`). -/
def RigidityStatement (d : ℕ) : Prop :=
  ∀ D : ℕ, 0 < D → ∀ S : Strategy d D, S.cglmp = IME d → S.IsDKZTensorId

/-- The max-ent clause of OQP 27B for `d` outcomes: the DKZ measurements are optimal (`I_d ≤ I_ME(d)`,
attained by `dkz d`, see `dkz_cglmp`) and necessarily optimal (rigidity). -/
def MaxEntClause (d : ℕ) : Prop := OptimalityStatement d ∧ RigidityStatement d

end Statements


/-! ## Non-vacuity of the rigidity statement -/

section NonVacuity

variable {d : ℕ}

/-- The identification `ℂ^d ≅ ℂ^d ⊗ ℂ^1` as a matrix. -/
def dkzEmbedOne (d : ℕ) : Matrix (Fin d × Fin 1) (Fin d) ℂ :=
  (1 : Matrix (Fin d) (Fin d) ℂ).submatrix Prod.fst id

lemma dkzEmbedOne_apply (p : Fin d × Fin 1) (j : Fin d) :
    dkzEmbedOne d p j = if p.1 = j then 1 else 0 := by
  simp [dkzEmbedOne, one_apply]

lemma dkzEmbedOne_map_star : (dkzEmbedOne d).map star = dkzEmbedOne d := by
  ext p j
  simp only [map_apply, dkzEmbedOne_apply]
  split_ifs <;> simp

lemma dkzEmbedOne_mul_conjTranspose : dkzEmbedOne d * (dkzEmbedOne d)ᴴ = 1 := by
  ext ⟨i, a⟩ ⟨i', a'⟩
  have ha : a = a' := Subsingleton.elim a a'
  subst ha
  simp only [mul_apply, conjTranspose_apply, dkzEmbedOne_apply]
  rw [one_apply]
  by_cases h : i = i'
  · subst h
    simp
  · simp only [Prod.mk.injEq, h, false_and, if_false]
    refine sum_eq_zero fun j _ => ?_
    by_cases hj : i = j
    · subst hj
      simp [Ne.symm h]
    · simp [hj]

lemma dkzEmbedOne_conjTranspose_mul : (dkzEmbedOne d)ᴴ * dkzEmbedOne d = 1 := by
  ext j j'
  simp only [mul_apply, conjTranspose_apply, dkzEmbedOne_apply]
  rw [Fintype.sum_prod_type, one_apply]
  simp only [Fin.sum_univ_one]
  by_cases h : j = j'
  · subst h
    simp
  · simp only [h, if_false]
    refine sum_eq_zero fun i _ => ?_
    by_cases hi : i = j
    · subst hi
      simp [h]
    · simp [hi]

lemma dkzEmbedOne_conj (X : Matrix (Fin d) (Fin d) ℂ) :
    dkzEmbedOne d * X * (dkzEmbedOne d)ᴴ = X ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext ⟨i, a⟩ ⟨i', a'⟩
  have ha : a = a' := Subsingleton.elim a a'
  subst ha
  simp only [mul_apply, conjTranspose_apply, dkzEmbedOne_apply, kroneckerMap_apply, one_apply_eq,
    mul_one]
  rw [sum_eq_single i']
  · rw [sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- **Non-vacuity of the rigidity statement**: the DKZ strategy itself has the form required by
`RigidityStatement` (with `K = 1`), consistently with `dkz_cglmp`. -/
theorem dkz_isDKZTensorId (d : ℕ) [NeZero d] : (dkz d).IsDKZTensorId := by
  refine ⟨1, (mul_one d).symm, dkzEmbedOne d, dkzEmbedOne_mul_conjTranspose,
    dkzEmbedOne_conjTranspose_mul, fun x a => ?_, fun y b => ?_⟩
  · exact dkzEmbedOne_conj _
  · rw [dkzEmbedOne_map_star]
    exact dkzEmbedOne_conj _

end NonVacuity


/-! ## Converse of rigidity -/

section Converse

variable {d D : ℕ}

/-- The CGLMP value depends only on the statistics `p(a,b|x,y)`. -/
lemma Strategy.cglmp_congr {D' : ℕ} {S : Strategy d D} {S' : Strategy d D'}
    (h : ∀ x y a b, S.prob x y a b = S'.prob x y a b) : S.cglmp = S'.cglmp := by
  simp only [Strategy.cglmp, Strategy.probAB, Strategy.probBA, h]

/-- A strategy that is DKZ ⊗ 1 up to a local unitary `u ⊗ ū` has the DKZ statistics. -/
theorem Strategy.prob_eq_dkz_of_isDKZTensorId [NeZero d] {S : Strategy d D} (hD : 0 < D)
    (h : S.IsDKZTensorId) (x y : Fin 2) (a b : Fin d) : S.prob x y a b = (dkz d).prob x y a b := by
  obtain ⟨K, hK, u, hu1, hu2, hA, hB⟩ := h
  have hK0 : K ≠ 0 := by
    rintro rfl
    simp at hK
    omega
  set ub : Matrix (Fin d × Fin K) (Fin D) ℂ := u.map star with hub
  have e1 : uᴴᵀ = ub := rfl
  have e2 : ubᴴ = uᵀ := by
    ext i j
    simp [hub]
  have m1 : u.map (starRingEnd ℂ) = ub := by
    ext i j
    simp [hub]
  have m2 : uᴴ.map (starRingEnd ℂ) = uᵀ := by
    ext i j
    simp
  have hub1 : ub * uᵀ = 1 := by
    have h1 := congrArg (fun X => X.map (starRingEnd ℂ)) hu1
    simp only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] at h1
    rwa [m1, m2] at h1
  have hub2 : uᵀ * ub = 1 := by
    have h1 := congrArg (fun X => X.map (starRingEnd ℂ)) hu2
    simp only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] at h1
    rwa [m1, m2] at h1
  set X := dkzA d x a ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ) with hX
  set Y := dkzB d y b ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ) with hY
  have hA' : (S.A x).proj a = uᴴ * X * u := by
    rw [hX, ← hA x a]
    simp only [← Matrix.mul_assoc]
    rw [hu2, Matrix.one_mul, Matrix.mul_assoc, hu2, Matrix.mul_one]
  have hB' : (S.B y).proj b = uᵀ * Y * ub := by
    rw [hY, ← hB y b, e2]
    simp only [← Matrix.mul_assoc]
    rw [hub2, Matrix.one_mul, Matrix.mul_assoc, hub2, Matrix.mul_one]
  have htr : (((S.A x).proj a)ᵀ * (S.B y).proj b).trace = (Xᵀ * Y).trace := by
    rw [hA', hB', Matrix.transpose_mul, Matrix.transpose_mul, e1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ub uᵀ, hub1, Matrix.one_mul, Matrix.trace_mul_comm uᵀ]
    simp only [Matrix.mul_assoc]
    rw [hub1, Matrix.mul_one]
  have hXY : (Xᵀ * Y).trace = ((dkzA d x a)ᵀ * dkzB d y b).trace * K := by
    rw [hX, hY, ← kroneckerMap_transpose, transpose_one, ← mul_kronecker_mul, Matrix.mul_one,
      trace_kronecker, trace_one, Fintype.card_fin]
  unfold Strategy.prob
  rw [htr, hXY]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK0
  rw [show ((((dkzA d x a)ᵀ * dkzB d y b).trace * (K : ℂ)).re) =
      (((dkzA d x a)ᵀ * dkzB d y b).trace).re * K by simp [Complex.mul_re]]
  rw [hK]
  push_cast
  rw [mul_comm (d : ℝ) K, ← div_div, mul_div_cancel_right₀ _ hK']
  rfl

/-- **Converse of rigidity**: every strategy (`D ≥ 1`) that is DKZ ⊗ 1 up to a local unitary `u ⊗ ū`
attains `I_ME(d)`.  With `RigidityStatement d`, the optimal strategies are exactly these. -/
theorem Strategy.cglmp_of_isDKZTensorId [NeZero d] (hd : 2 ≤ d) {S : Strategy d D} (hD : 0 < D)
    (h : S.IsDKZTensorId) : S.cglmp = IME d := by
  rw [Strategy.cglmp_congr (S' := dkz d) (Strategy.prob_eq_dkz_of_isDKZTensorId hD h), dkz_cglmp hd]

/-- Under `RigidityStatement d`, a strategy on `Φ_D` (`D ≥ 1`) attains `I_ME(d)` if and only if it is
DKZ ⊗ 1 up to a local unitary `u ⊗ ū`. -/
theorem rigidity_iff [NeZero d] (hd : 2 ≤ d) (hrig : RigidityStatement d) {S : Strategy d D}
    (hD : 0 < D) : S.cglmp = IME d ↔ S.IsDKZTensorId :=
  ⟨hrig D hD S, Strategy.cglmp_of_isDKZTensorId hd hD⟩

end Converse

end OQP27
