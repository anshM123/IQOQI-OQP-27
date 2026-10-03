/- ## Part 87: the main results

The results announced in the module docstring, stated with the definitions of Part 0. The
statements for every $d \ge 2$ take the cone condition for $d \ge 21$ (`Hyp_ConeCertPos_large`,
established outside Lean by interval-arithmetic certificates) as an explicit hypothesis; all other
statements are unconditional. -/

namespace OpenQuantumProblem27

open Matrix
open scoped Kronecker

section Bridge

/- ### From the definitions of Part 0 to the internal model of the proof -/

variable {d D : ℕ}

/-- The internal model (part `Statement`) of projective measurements on $\Phi_D$. -/
noncomputable def toStrategy (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    Strategy d D where
  A x := ⟨A x, fun a => (hA x).1 a, (hA x).2⟩
  B y := ⟨B y, fun b => (hB y).1 b, (hB y).2⟩

/-- On $\Phi_D$, the Born-rule behaviour is the behaviour `Strategy.prob` of the internal model. -/
@[category API, AMS 15 81]
theorem quantumBehaviour_eq_prob (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    quantumBehaviour (densityMatrix (maxEntangledState D)) A B = (toStrategy A B hA hB).prob := by
  funext x y a b
  rw [quantumBehaviour, bornProb_maxEntangledState]
  rfl

@[category API, AMS 15 81]
theorem cglmpExpr_eq_cglmpOf (p : Behaviour d) : cglmpExpr p = cglmpOf p := rfl

@[category API, AMS 15 81]
theorem cglmpMaxEntValue_eq_IME (d : ℕ) : cglmpMaxEntValue d = IME d := rfl

@[category API, AMS 15 81]
theorem swapInputs_swapInputs (p : Behaviour d) : swapInputs (swapInputs p) = p := by
  funext x y a b
  simp [swapInputs]

/-- **The CGLMP functional of a projective strategy on $\Phi_D$** in terms of the CGLMP expression
of the internal model with the two inputs exchanged:
$F = \frac{d-1}{2} (4 - I_d)$. -/
@[category API, AMS 15 81]
theorem cglmpFunctional_quantumBehaviour (hd : 2 ≤ d) (hD : 0 < D)
    (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) =
      ((d : ℝ) - 1) * (4 - (toStrategy (fun x => A x.rev) (fun y => B y.rev) (fun x => hA x.rev)
        (fun y => hB y.rev)).cglmp) / 2 := by
  set S := toStrategy (fun x => A x.rev) (fun y => B y.rev) (fun x => hA x.rev) (fun y => hB y.rev)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsw : swapInputs (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) =
      S.prob := by
    rw [← quantumBehaviour_eq_prob]
    rfl
  have hI := cglmpExpr_eq_cglmpFunctional hd S.prob (S.sum_prob hD)
  have hG : cglmpFunctional (swapInputs S.prob) =
      cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) := by
    rw [← hsw, swapInputs_swapInputs]
  rw [cglmpExpr_eq_cglmpOf, cglmpOf_prob, hG] at hI
  rw [hI]
  field_simp
  ring

/-- The DKZ measurements of Part 0, with the two inputs exchanged, are the DKZ projectors of the
internal model. -/
@[category API, AMS 15 81]
theorem vonNeumannMeasurement_dkzUnitaryA [NeZero d] (x : Fin 2) (k : Fin d) :
    vonNeumannMeasurement (dkzUnitaryA d x.rev) k = dkzA d x k := by
  have hα : ((dkzAlpha x.rev : ℝ) : ℂ) = (alpha4 x : ℂ) / 4 := by
    fin_cases x
    · simp [dkzAlpha, alpha4]
    · simp [dkzAlpha, alpha4]
      norm_num
  rw [vonNeumannMeasurement_eq_vecMulVec, dkzA_eq_vecMulVec]
  congr 1
  · funext j
    rw [dkzUnitaryA_apply, hα]
    rfl
  · funext j
    simp only [Pi.star_apply]
    rw [dkzUnitaryA_apply, hα]
    rfl

@[category API, AMS 15 81]
theorem vonNeumannMeasurement_dkzUnitaryB [NeZero d] (y : Fin 2) (l : Fin d) :
    vonNeumannMeasurement (dkzUnitaryB d y.rev) l = dkzB d y l := by
  have hβ : ((dkzBeta y.rev : ℝ) : ℂ) = (beta4 y : ℂ) / 4 := by
    fin_cases y <;> simp [dkzBeta, beta4]
  rw [vonNeumannMeasurement_eq_vecMulVec, dkzB_eq_vecMulVec]
  congr 1
  · funext j
    rw [dkzUnitaryB_apply, hβ]
    rfl
  · funext j
    simp only [Pi.star_apply]
    rw [dkzUnitaryB_apply, hβ]
    rfl

@[category API, AMS 15 81]
theorem vonNeumannMeasurement_dkzUnitaryA' [NeZero d] (x : Fin 2) (k : Fin d) :
    vonNeumannMeasurement (dkzUnitaryA d x) k = dkzA d x.rev k := by
  rw [← vonNeumannMeasurement_dkzUnitaryA, Fin.rev_rev]

@[category API, AMS 15 81]
theorem vonNeumannMeasurement_dkzUnitaryB' [NeZero d] (y : Fin 2) (l : Fin d) :
    vonNeumannMeasurement (dkzUnitaryB d y) l = dkzB d y.rev l := by
  rw [← vonNeumannMeasurement_dkzUnitaryB, Fin.rev_rev]

@[category API, AMS 15 81]
lemma sum_vonNeumannMeasurement (U : Matrix (Fin d) (Fin d) ℂ) :
    ∑ a, vonNeumannMeasurement U a = U * Uᴴ := by
  unfold vonNeumannMeasurement
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_self_one, Matrix.mul_one]

/-- The DKZ bases are orthonormal: Alice's DKZ matrices are unitary. -/
@[category test, AMS 15 81]
theorem dkzUnitaryA_mem_unitaryGroup [NeZero d] (x : Fin 2) :
    dkzUnitaryA d x ∈ unitaryGroup (Fin d) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, ← sum_vonNeumannMeasurement]
  rw [← Fin.rev_rev x]
  simp only [vonNeumannMeasurement_dkzUnitaryA]
  exact (dkzPVMA d x.rev).sum_eq_one

/-- The DKZ bases are orthonormal: Bob's DKZ matrices are unitary. -/
@[category test, AMS 15 81]
theorem dkzUnitaryB_mem_unitaryGroup [NeZero d] (y : Fin 2) :
    dkzUnitaryB d y ∈ unitaryGroup (Fin d) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, ← sum_vonNeumannMeasurement]
  rw [← Fin.rev_rev y]
  simp only [vonNeumannMeasurement_dkzUnitaryB]
  exact (dkzPVMB d y.rev).sum_eq_one

/-- The internal model of the DKZ measurements of Part 0, inputs exchanged, is the DKZ strategy
`dkz d` of the proof. -/
@[category API, AMS 15 81]
lemma toStrategy_dkz_prob [NeZero d] :
    (toStrategy (fun x => vonNeumannMeasurement (dkzUnitaryA d x.rev))
      (fun y => vonNeumannMeasurement (dkzUnitaryB d y.rev))
      (fun x => isProjectiveMeasurement_vonNeumannMeasurement (dkzUnitaryA_mem_unitaryGroup x.rev))
      (fun y => isProjectiveMeasurement_vonNeumannMeasurement (dkzUnitaryB_mem_unitaryGroup y.rev))).prob =
      (dkz d).prob := by
  funext x y a b
  simp only [Strategy.prob, toStrategy, vonNeumannMeasurement_dkzUnitaryA,
    vonNeumannMeasurement_dkzUnitaryB]
  rfl

/-- **The value of the DKZ measurements**:
$F(\mathrm{DKZ}) = \frac{d-1}{2} (4 - I_{ME}(d))$. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_dkz [NeZero d] (h2 : 2 ≤ d) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) =
      ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 := by
  rw [vonNeumannBehaviour, cglmpFunctional_quantumBehaviour h2 (NeZero.pos d) _ _
    (fun x => isProjectiveMeasurement_vonNeumannMeasurement (dkzUnitaryA_mem_unitaryGroup x))
    (fun y => isProjectiveMeasurement_vonNeumannMeasurement (dkzUnitaryB_mem_unitaryGroup y))]
  rw [show (toStrategy _ _ _ _).cglmp = cglmpOf (toStrategy _ _ _ _).prob from (cglmpOf_prob _).symm]
  rw [toStrategy_dkz_prob, cglmpOf_prob, dkz_cglmp h2, cglmpMaxEntValue_eq_IME]

/-- The DKZ measurements violate the CGLMP inequality: $F(\mathrm{DKZ}) < d - 1$. -/
@[category test, AMS 15 81]
theorem cglmpFunctional_dkz_lt [NeZero d] (h2 : 2 ≤ d) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) < (d : ℝ) - 1 := by
  rw [cglmpFunctional_dkz h2]
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  have := IME_gt_two h2
  rw [cglmpMaxEntValue_eq_IME]
  nlinarith

/-- For `D = d`, the rigidity predicate `Strategy.IsDKZTensorId` says that a local unitary `u ⊗ ū`
(which leaves $\Phi_d$ invariant) conjugates the strategy into the DKZ strategy. -/
@[category API, AMS 15 81]
theorem isDKZTensorId_iff_unitary [NeZero d] (S : Strategy d d) :
    S.IsDKZTensorId ↔ ∃ u : Matrix (Fin d) (Fin d) ℂ, u * uᴴ = 1 ∧ uᴴ * u = 1 ∧
      (∀ x a, u * (S.A x).proj a * uᴴ = dkzA d x a) ∧
      (∀ y b, u.map star * (S.B y).proj b * (u.map star)ᴴ = dkzB d y b) := by
  set e : Fin d × Fin 1 ≃ Fin d := Equiv.prodUnique (Fin d) (Fin 1) with he
  have hk : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      (M ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm = M := by
    intro M
    ext i j
    simp [he, kroneckerMap_apply]
  have hk' : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      M.submatrix e e = M ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    intro M
    ext ⟨i, i'⟩ ⟨j, j'⟩
    simp [he, kroneckerMap_apply, Subsingleton.elim i' j']
  have conj : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι ≃ κ) (u : Matrix κ (Fin d) ℂ)
      (M : Matrix (Fin d) (Fin d) ℂ),
      u.submatrix f id * M * (u.submatrix f id)ᴴ = (u * M * uᴴ).submatrix f f := by
    intro ι κ _ _ f u M
    ext i j
    rfl
  have gram : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι ≃ κ) (u : Matrix κ (Fin d) ℂ),
      (u.submatrix f id)ᴴ * u.submatrix f id = uᴴ * u := by
    intro ι κ _ _ f u
    ext i j
    simp only [mul_apply, conjTranspose_apply, submatrix_apply, id]
    exact Fintype.sum_equiv f _ _ fun _ => rfl
  constructor
  · rintro ⟨K, hK, u, h1, h2, hA, hB⟩
    have hK1 : K = 1 := by
      have : d * K = d * 1 := by rw [← hK, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (NeZero.pos d) this
    subst hK1
    refine ⟨u.submatrix e.symm id, ?_, ?_, fun x a => ?_, fun y b => ?_⟩
    · have h := conj e.symm u 1
      rw [Matrix.mul_one, Matrix.mul_one, h1, submatrix_one_equiv] at h
      exact h
    · rw [gram, h2]
    · rw [conj, hA, hk]
    · rw [show (u.submatrix e.symm id).map star = (u.map star).submatrix e.symm id from rfl, conj,
        hB, hk]
  · rintro ⟨u, h1, h2, hA, hB⟩
    refine ⟨1, (mul_one d).symm, u.submatrix e id, ?_, ?_, fun x a => ?_, fun y b => ?_⟩
    · have h := conj e u 1
      rw [Matrix.mul_one, Matrix.mul_one, h1, submatrix_one_equiv] at h
      exact h
    · rw [gram, h2]
    · rw [conj, hA, hk']
    · rw [show (u.submatrix e id).map star = (u.map star).submatrix e id from rfl, conj, hB, hk']

/-- The uniqueness condition: a unitary `u` such that `u ⊗ ū` maps the measurements `A`, `B`
on $\mathbb{C}^d$ to the DKZ measurements of Part 0. -/
def IsDKZUpToLocalUnitary (A B : Fin 2 → Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ u ∈ unitaryGroup (Fin d) ℂ,
    (∀ x a, u * A x a * uᴴ = vonNeumannMeasurement (dkzUnitaryA d x) a) ∧
    (∀ y b, u.map star * B y b * (u.map star)ᴴ = vonNeumannMeasurement (dkzUnitaryB d y) b)

/-- The rigidity predicate of the internal model, for the strategy with exchanged inputs, is the
uniqueness condition `IsDKZUpToLocalUnitary`. -/
@[category API, AMS 15 81]
theorem isDKZTensorId_toStrategy_iff [NeZero d] (A B : Fin 2 → Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    (toStrategy (fun x => A x.rev) (fun y => B y.rev) (fun x => hA x.rev)
      (fun y => hB y.rev)).IsDKZTensorId ↔ IsDKZUpToLocalUnitary A B := by
  rw [isDKZTensorId_iff_unitary]
  constructor
  · rintro ⟨u, h1, h2, hA', hB'⟩
    refine ⟨u, ?_, fun x a => ?_, fun y b => ?_⟩
    · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
      exact h1
    · rw [vonNeumannMeasurement_dkzUnitaryA', ← hA' x.rev a]
      simp only [toStrategy, Fin.rev_rev]
    · rw [vonNeumannMeasurement_dkzUnitaryB', ← hB' y.rev b]
      simp only [toStrategy, Fin.rev_rev]
  · rintro ⟨u, hu, hA', hB'⟩
    have h1 : u * uᴴ = 1 := unitary_mul_conjTranspose hu
    have h2 : uᴴ * u = 1 := unitary_conjTranspose_mul hu
    refine ⟨u, h1, h2, fun x a => ?_, fun y b => ?_⟩
    · simp only [toStrategy]
      rw [hA' x.rev a, vonNeumannMeasurement_dkzUnitaryA', Fin.rev_rev]
    · simp only [toStrategy]
      rw [hB' y.rev b, vonNeumannMeasurement_dkzUnitaryB', Fin.rev_rev]

@[category API, AMS 15 81]
lemma affine_cancel {c x y : ℝ} (hc : 0 < c) : c * (4 - x) / 2 = c * (4 - y) / 2 ↔ x = y := by
  constructor
  · intro h
    have h' : c * (4 - x) = c * (4 - y) := by linarith
    have := mul_left_cancel₀ hc.ne' h'
    linarith
  · intro h
    rw [h]

/-- If the noisy statistics of `S` violate the CGLMP inequality at every visibility at which those
of the DKZ strategy do, then the CGLMP value of `S` is at least $I_{ME}(d)$. -/
@[category API, AMS 15 81]
theorem IME_le_cglmp_of_noise {d D : ℕ} [NeZero d] (h2 : 2 ≤ d) (S : Strategy d D)
    (h : ∀ v : ℝ, 2 < cglmpOf (noisy (dkz d).prob v) → 2 < cglmpOf (noisy S.prob v)) :
    IME d ≤ S.cglmp := by
  have hI : 2 < IME d := IME_gt_two h2
  have key : ∀ v : ℝ, 2 < v * IME d → 2 < v * S.cglmp := fun v hv => by
    have hS := h v ((dkz_noisy_violation_iff h2 v).2 hv)
    rwa [noisy_violation_iff] at hS
  rcases lt_or_ge S.cglmp (IME d) with hlt | hge
  · exfalso
    rcases le_or_gt S.cglmp 0 with h0 | h0
    · have hv : 4 / IME d * IME d = 4 := div_mul_cancel₀ 4 (by linarith)
      have h1 := key (4 / IME d) (by rw [hv]; norm_num)
      have h3 : 4 / IME d * S.cglmp ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) (by linarith)) h0
      linarith
    · have hpos : 0 < S.cglmp + IME d := by linarith
      have h1 := key (4 / (S.cglmp + IME d)) (by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hpos]
        linarith)
      rw [div_mul_eq_mul_div, lt_div_iff₀ hpos] at h1
      linarith
  · exact hge

end Bridge

section MainResults

/- ### OQP 27B: complete von Neumann measurements on $\Phi_d$ -/

/-- **OQP 27B, optimality of the DKZ measurements, for $2 \le d \le 20$.** On the maximally
entangled state $\Phi_d$ of two qudits, no complete von Neumann measurements give a smaller value of
the CGLMP functional (a larger violation of the CGLMP inequality) than the DKZ measurements, whose
value is $\frac{d-1}{2}(4 - I_{ME}(d)) < d - 1$ (`cglmpFunctional_dkz`). Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_optimal_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ≤
      cglmpFunctional (vonNeumannBehaviour d UA UB) := by
  have hA := fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x)
  have hB := fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y)
  rw [cglmpFunctional_dkz h2, vonNeumannBehaviour,
    cglmpFunctional_quantumBehaviour h2 (NeZero.pos d) _ _ hA hB, cglmpMaxEntValue_eq_IME]
  have hopt := (maxEntClause_le_twenty d h2 h20).1.1 d (NeZero.pos d)
    (toStrategy (fun x => vonNeumannMeasurement (UA x.rev)) (fun y => vonNeumannMeasurement (UB y.rev))
      (fun x => hA x.rev) (fun y => hB y.rev))
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  nlinarith

/-- **OQP 27B, the optimal measurements are necessarily the DKZ measurements, for
$2 \le d \le 20$.** Complete von Neumann measurements on $\Phi_d$ attain the DKZ value of the CGLMP
functional if and only if a local unitary $u \otimes \bar u$ (these are exactly the local unitaries
that leave $\Phi_d$ invariant) maps them to the DKZ measurements. Since this characterizes all
optimal strategies, every symmetry of the problem (for instance a relabelling of outputs that
preserves the functional) maps the DKZ measurements to measurements of this form. Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_unique_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d UA UB) =
        cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ↔
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y)) := by
  have hA := fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x)
  have hB := fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  rw [cglmpFunctional_dkz h2, vonNeumannBehaviour,
    cglmpFunctional_quantumBehaviour h2 (NeZero.pos d) _ _ hA hB, cglmpMaxEntValue_eq_IME,
    ← isDKZTensorId_toStrategy_iff _ _ hA hB,
    ← rigidity_iff h2 (maxEntClause_le_twenty d h2 h20).1.2 (NeZero.pos d)]
  exact affine_cancel hd1

/-- **OQP 27B, optimality, for every $d \ge 2$**, assuming the cone condition for $d \ge 21$
(`Hyp_ConeCertPos_large`); see `dkz_optimal_of_le_twenty`. -/
@[category research solved, AMS 15 81]
theorem dkz_optimal (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ≤
      cglmpFunctional (vonNeumannBehaviour d UA UB) := by
  have hA := fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x)
  have hB := fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y)
  rw [cglmpFunctional_dkz h2, vonNeumannBehaviour,
    cglmpFunctional_quantumBehaviour h2 (NeZero.pos d) _ _ hA hB, cglmpMaxEntValue_eq_IME]
  have hopt := (maxEntClause_all hlarge d h2).1.1 d (NeZero.pos d)
    (toStrategy (fun x => vonNeumannMeasurement (UA x.rev)) (fun y => vonNeumannMeasurement (UB y.rev))
      (fun x => hA x.rev) (fun y => hB y.rev))
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  nlinarith

/-- **OQP 27B, uniqueness, for every $d \ge 2$**, assuming the cone condition for $d \ge 21$
(`Hyp_ConeCertPos_large`); see `dkz_unique_of_le_twenty`. -/
@[category research solved, AMS 15 81]
theorem dkz_unique (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    cglmpFunctional (vonNeumannBehaviour d UA UB) =
        cglmpFunctional (vonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d)) ↔
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y)) := by
  have hA := fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x)
  have hB := fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  rw [cglmpFunctional_dkz h2, vonNeumannBehaviour,
    cglmpFunctional_quantumBehaviour h2 (NeZero.pos d) _ _ hA hB, cglmpMaxEntValue_eq_IME,
    ← isDKZTensorId_toStrategy_iff _ _ hA hB,
    ← rigidity_iff h2 (maxEntClause_all hlarge d h2).1.2 (NeZero.pos d)]
  exact affine_cancel hd1

/- ### The noise clause: white noise on $\Phi_d$ -/

/-- With white noise on the state, complete von Neumann measurements see the behaviour mixed with
uniformly random outputs: $\operatorname{Tr}[\rho_v (P_a \otimes Q_b)] = v\,p(a,b|x,y) + (1-v)/d^2$. -/
@[category API, AMS 15 81]
theorem noisyVonNeumannBehaviour_eq {d : ℕ} (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) (v : ℝ) :
    noisyVonNeumannBehaviour d UA UB v = noisy (vonNeumannBehaviour d UA UB) v := by
  funext x y a b
  simp only [noisyVonNeumannBehaviour, vonNeumannBehaviour, quantumBehaviour, bornProb,
    whiteNoiseState, noisy, unif, add_mul, smul_mul_assoc, Matrix.one_mul, trace_add, trace_smul,
    trace_kronecker, trace_vonNeumannMeasurement (hUA x), trace_vonNeumannMeasurement (hUB y)]
  simp only [smul_eq_mul, mul_one, Complex.add_re, Complex.re_ofReal_mul]
  rw [show ((((1 - v) / (d : ℝ) ^ 2 : ℝ) : ℂ)).re = (1 - v) / (d : ℝ) ^ 2 from Complex.ofReal_re _]
  ring

@[category API, AMS 15 81]
lemma sum_noisy_eq_one {d : ℕ} [NeZero d] (p : Behaviour d) (hp : ∀ x y, ∑ a, ∑ b, p x y a b = 1)
    (v : ℝ) (x y : Fin 2) : ∑ a, ∑ b, noisy p v x y a b = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  simp only [noisy, unif, Finset.sum_add_distrib, ← Finset.mul_sum, hp, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The CGLMP functional of the noisy behaviour in terms of the internal model. -/
@[category API, AMS 15 81]
lemma cglmpFunctional_noisyVonNeumannBehaviour {d : ℕ} [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) (v : ℝ) :
    cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) =
      ((d : ℝ) - 1) * (4 - cglmpOf (noisy (toStrategy (fun x => vonNeumannMeasurement (UA x.rev))
        (fun y => vonNeumannMeasurement (UB y.rev))
        (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x.rev))
        (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y.rev))).prob v)) / 2 := by
  set S := toStrategy (fun x => vonNeumannMeasurement (UA x.rev))
    (fun y => vonNeumannMeasurement (UB y.rev))
    (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x.rev))
    (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y.rev))
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  have hsw : swapInputs (noisyVonNeumannBehaviour d UA UB v) = noisy S.prob v := by
    rw [noisyVonNeumannBehaviour_eq UA UB hUA hUB, vonNeumannBehaviour,
      ← quantumBehaviour_eq_prob _ _ (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x.rev))
        (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y.rev))]
    rfl
  have hI := cglmpExpr_eq_cglmpFunctional h2 (noisy S.prob v)
    (sum_noisy_eq_one _ (S.sum_prob (NeZero.pos d)) v)
  have hG : cglmpFunctional (swapInputs (noisy S.prob v)) =
      cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) := by
    rw [← hsw, swapInputs_swapInputs]
  rw [cglmpExpr_eq_cglmpOf, hG] at hI
  rw [hI]
  field_simp
  ring

/-- **OQP 27B, noise clause, for $2 \le d \le 20$**: the DKZ measurements have the highest
resistance to white noise of the violation of the CGLMP inequality. Mix $\Phi_d$ with white noise,
$\rho_v = v \, |\Phi_d\rangle\langle\Phi_d| + (1 - v) \, \mathbb{1}/d^2$ with $v \ge 0$. Whenever
complete von Neumann measurements violate the CGLMP inequality on $\rho_v$, so do the DKZ
measurements; and measurements that violate it at every visibility at which DKZ does are DKZ up to
a local unitary $u \otimes \bar u$. Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_noise_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    (∀ v : ℝ, 0 ≤ v → cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1 →
      cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1) ∧
    ((∀ v : ℝ,
        cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1 →
          cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1) →
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y))) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  have hDA := fun x => dkzUnitaryA_mem_unitaryGroup (d := d) x
  have hDB := fun y => dkzUnitaryB_mem_unitaryGroup (d := d) y
  have viol : ∀ (VA VB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hVA : ∀ x, VA x ∈ unitaryGroup (Fin d) ℂ)
      (hVB : ∀ y, VB y ∈ unitaryGroup (Fin d) ℂ) (v : ℝ),
      cglmpFunctional (noisyVonNeumannBehaviour d VA VB v) < (d : ℝ) - 1 ↔
        2 < cglmpOf (noisy (toStrategy (fun x => vonNeumannMeasurement (VA x.rev))
          (fun y => vonNeumannMeasurement (VB y.rev))
          (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hVA x.rev))
          (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hVB y.rev))).prob v) := by
    intro VA VB hVA hVB v
    rw [cglmpFunctional_noisyVonNeumannBehaviour h2 VA VB hVA hVB v]
    constructor <;> intro h <;> nlinarith
  have hdkz : ∀ v : ℝ, cglmpOf (noisy (toStrategy (fun x => vonNeumannMeasurement (dkzUnitaryA d x.rev))
      (fun y => vonNeumannMeasurement (dkzUnitaryB d y.rev))
      (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hDA x.rev))
      (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hDB y.rev))).prob v) =
        cglmpOf (noisy (dkz d).prob v) := fun v => by rw [toStrategy_dkz_prob]
  refine ⟨fun v hv h => ?_, fun h => ?_⟩
  · rw [viol _ _ hDA hDB, hdkz, dkz_noisy_violation_iff h2]
    rw [viol _ _ hUA hUB] at h
    exact noisy_violation_imp_le_twenty h2 h20 (NeZero.pos d) _ hv h
  · have h' : ∀ v : ℝ, 2 < cglmpOf (noisy (dkz d).prob v) →
        2 < cglmpOf (noisy (toStrategy (fun x => vonNeumannMeasurement (UA x.rev))
          (fun y => vonNeumannMeasurement (UB y.rev))
          (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x.rev))
          (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y.rev))).prob v) := by
      intro v hv
      rw [← viol _ _ hUA hUB]
      apply h v
      rw [viol _ _ hDA hDB, hdkz]
      exact hv
    have heq := le_antisymm ((maxEntClause_le_twenty d h2 h20).1.1 d (NeZero.pos d) _)
      (IME_le_cglmp_of_noise h2 _ h')
    exact (isDKZTensorId_toStrategy_iff (fun x => vonNeumannMeasurement (UA x))
      (fun y => vonNeumannMeasurement (UB y))
      (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x))
      (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y))).1
      ((rigidity_iff h2 (maxEntClause_le_twenty d h2 h20).1.2 (NeZero.pos d)).1 heq)

/-- **OQP 27B, noise clause, for every $d \ge 2$**, assuming the cone condition for $d \ge 21$
(`Hyp_ConeCertPos_large`); see `dkz_noise_of_le_twenty`. -/
@[category research solved, AMS 15 81]
theorem dkz_noise (hlarge : Hyp_ConeCertPos_large) (d : ℕ) [NeZero d] (h2 : 2 ≤ d)
    (UA UB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hUA : ∀ x, UA x ∈ unitaryGroup (Fin d) ℂ)
    (hUB : ∀ y, UB y ∈ unitaryGroup (Fin d) ℂ) :
    (∀ v : ℝ, 0 ≤ v → cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1 →
      cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1) ∧
    ((∀ v : ℝ,
        cglmpFunctional (noisyVonNeumannBehaviour d (dkzUnitaryA d) (dkzUnitaryB d) v) < (d : ℝ) - 1 →
          cglmpFunctional (noisyVonNeumannBehaviour d UA UB v) < (d : ℝ) - 1) →
      IsDKZUpToLocalUnitary (fun x => vonNeumannMeasurement (UA x))
        (fun y => vonNeumannMeasurement (UB y))) := by
  have hDA := fun x => dkzUnitaryA_mem_unitaryGroup (d := d) x
  have hDB := fun y => dkzUnitaryB_mem_unitaryGroup (d := d) y
  have viol : ∀ (VA VB : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (hVA : ∀ x, VA x ∈ unitaryGroup (Fin d) ℂ)
      (hVB : ∀ y, VB y ∈ unitaryGroup (Fin d) ℂ) (v : ℝ),
      cglmpFunctional (noisyVonNeumannBehaviour d VA VB v) < (d : ℝ) - 1 ↔
        2 < cglmpOf (noisy (toStrategy (fun x => vonNeumannMeasurement (VA x.rev))
          (fun y => vonNeumannMeasurement (VB y.rev))
          (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hVA x.rev))
          (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hVB y.rev))).prob v) := by
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast h2
      linarith
    intro VA VB hVA hVB v
    rw [cglmpFunctional_noisyVonNeumannBehaviour h2 VA VB hVA hVB v]
    constructor <;> intro h <;> nlinarith
  have hdkz : ∀ v : ℝ, cglmpOf (noisy (toStrategy (fun x => vonNeumannMeasurement (dkzUnitaryA d x.rev))
      (fun y => vonNeumannMeasurement (dkzUnitaryB d y.rev))
      (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hDA x.rev))
      (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hDB y.rev))).prob v) =
        cglmpOf (noisy (dkz d).prob v) := fun v => by rw [toStrategy_dkz_prob]
  refine ⟨fun v hv h => ?_, fun h => ?_⟩
  · rw [viol _ _ hDA hDB, hdkz, dkz_noisy_violation_iff h2]
    rw [viol _ _ hUA hUB] at h
    exact noisy_violation_imp hlarge h2 (NeZero.pos d) _ hv h
  · have h' : ∀ v : ℝ, 2 < cglmpOf (noisy (dkz d).prob v) →
        2 < cglmpOf (noisy (toStrategy (fun x => vonNeumannMeasurement (UA x.rev))
          (fun y => vonNeumannMeasurement (UB y.rev))
          (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x.rev))
          (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y.rev))).prob v) := by
      intro v hv
      rw [← viol _ _ hUA hUB]
      apply h v
      rw [viol _ _ hDA hDB, hdkz]
      exact hv
    have heq := le_antisymm ((maxEntClause_all hlarge d h2).1.1 d (NeZero.pos d) _)
      (IME_le_cglmp_of_noise h2 _ h')
    exact (isDKZTensorId_toStrategy_iff (fun x => vonNeumannMeasurement (UA x))
      (fun y => vonNeumannMeasurement (UB y))
      (fun x => isProjectiveMeasurement_vonNeumannMeasurement (hUA x))
      (fun y => isProjectiveMeasurement_vonNeumannMeasurement (hUB y))).1
      ((rigidity_iff h2 (maxEntClause_all hlarge d h2).1.2 (NeZero.pos d)).1 heq)

/- ### Strengthening: all projective measurements, every local dimension -/

/-- **Optimality for all projective measurements on maximally entangled states of every local
dimension $D$**, for $2 \le d \le 20$: $F \ge \frac{d-1}{2}(4 - I_{ME}(d))$ for all $d$-outcome
projective measurements (of any ranks) on $\Phi_D$. Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_optimal_any_dim_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (D : ℕ)
    (hD : 0 < D) (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 ≤
      cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) := by
  rw [cglmpFunctional_quantumBehaviour h2 hD A B hA hB, cglmpMaxEntValue_eq_IME]
  have hopt := (maxEntClause_le_twenty d h2 h20).1.1 D hD
    (toStrategy (fun x => A x.rev) (fun y => B y.rev) (fun x => hA x.rev) (fun y => hB y.rev))
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  nlinarith

/-- **Uniqueness for all projective measurements on $\Phi_D$, every $D$**, for $2 \le d \le 20$:
the bound of `dkz_optimal_any_dim_of_le_twenty` is attained if and only if $D = dK$ and a unitary
$V : \mathbb{C}^D \to \mathbb{C}^d \otimes \mathbb{C}^K$ maps the measurements to the DKZ measurements
tensored with the identity, $V A_{x,a} V^{\dagger} = A^{DKZ}_{x,a} \otimes 1_K$ and
$\bar V B_{y,b} \bar V^{\dagger} = B^{DKZ}_{y,b} \otimes 1_K$ (then
$(V \otimes \bar V) \Phi_D = \Phi_d \otimes \Phi_K$). Unconditional. -/
@[category research solved, AMS 15 81]
theorem dkz_unique_any_dim_of_le_twenty (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (D : ℕ)
    (hD : 0 < D) (A B : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ x, IsProjectiveMeasurement (A x)) (hB : ∀ y, IsProjectiveMeasurement (B y)) :
    cglmpFunctional (quantumBehaviour (densityMatrix (maxEntangledState D)) A B) =
        ((d : ℝ) - 1) * (4 - cglmpMaxEntValue d) / 2 ↔
      ∃ K : ℕ, D = d * K ∧ ∃ V : Matrix (Fin d × Fin K) (Fin D) ℂ, V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
        (∀ x a, V * A x a * Vᴴ =
          vonNeumannMeasurement (dkzUnitaryA d x) a ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) ∧
        (∀ y b, V.map star * B y b * (V.map star)ᴴ =
          vonNeumannMeasurement (dkzUnitaryB d y) b ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast h2
    linarith
  rw [cglmpFunctional_quantumBehaviour h2 hD A B hA hB, cglmpMaxEntValue_eq_IME]
  rw [affine_cancel hd1, rigidity_iff h2 (maxEntClause_le_twenty d h2 h20).1.2 hD]
  simp only [Strategy.IsDKZTensorId, toStrategy, vonNeumannMeasurement_dkzUnitaryA',
    vonNeumannMeasurement_dkzUnitaryB']
  constructor
  · rintro ⟨K, hK, V, h1, h2', hA', hB'⟩
    exact ⟨K, hK, V, h1, h2', fun x a => by rw [← hA' x.rev a, Fin.rev_rev],
      fun y b => by rw [← hB' y.rev b, Fin.rev_rev]⟩
  · rintro ⟨K, hK, V, h1, h2', hA', hB'⟩
    exact ⟨K, hK, V, h1, h2', fun x a => by rw [hA' x.rev a, Fin.rev_rev],
      fun y b => by rw [hB' y.rev b, Fin.rev_rev]⟩

/- ### Special case $d = 2$: Tsirelson's bound -/

/-- **Special case $d = 2$: Tsirelson's bound.** For $d = 2$ the CGLMP functional is the CHSH
functional $\frac{4 - \mathrm{CHSH}}{2}$; on two maximally entangled qubits no complete von Neumann
measurements go below $2 - \sqrt{2}$ (that is, CHSH $\le 2\sqrt{2}$), and the DKZ measurements attain
it. -/
@[category test, AMS 15 81]
theorem dkz_tsirelson (UA UB : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin 2) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin 2) ℂ) :
    2 - Real.sqrt 2 ≤ cglmpFunctional (vonNeumannBehaviour 2 UA UB) ∧
      cglmpFunctional (vonNeumannBehaviour 2 (dkzUnitaryA 2) (dkzUnitaryB 2)) = 2 - Real.sqrt 2 := by
  have hv : cglmpFunctional (vonNeumannBehaviour 2 (dkzUnitaryA 2) (dkzUnitaryB 2)) =
      2 - Real.sqrt 2 := by
    rw [cglmpFunctional_dkz le_rfl, cglmpMaxEntValue_two]
    push_cast
    ring
  refine ⟨?_, hv⟩
  rw [← hv]
  exact dkz_optimal_of_le_twenty 2 le_rfl (by norm_num) UA UB hUA hUB

/- ### A related question: non-maximally entangled states -/

/-- **The maximally entangled state is not optimal for $d = 3$** (Acín, Durt, Gisin and Latorre
2002), a counterexample to a question related to OQP 27: with the DKZ measurements, the
non-maximally entangled state $(|00\rangle + \tfrac{4}{5} |11\rangle + |22\rangle)/\sqrt{2 + 16/25}$
gives a smaller value of the CGLMP functional, $\frac{82}{33} - \frac{80}{99}\sqrt{3}$, than any
complete von Neumann measurements on $\Phi_3$, whose minimum is $\frac{24 - 8\sqrt{3}}{9}$. -/
@[category test, AMS 15 81]
theorem adglState_beats_maxEntangledState (UA UB : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hUA : ∀ x, UA x ∈ unitaryGroup (Fin 3) ℂ) (hUB : ∀ y, UB y ∈ unitaryGroup (Fin 3) ℂ) :
    cglmpFunctional (quantumBehaviour (densityMatrix (adglState (4 / 5)))
      (fun x => vonNeumannMeasurement (dkzUnitaryA 3 x))
      (fun y => vonNeumannMeasurement (dkzUnitaryB 3 y))) <
      cglmpFunctional (vonNeumannBehaviour 3 UA UB) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hdkz : cglmpFunctional (vonNeumannBehaviour 3 (dkzUnitaryA 3) (dkzUnitaryB 3)) =
      (24 - 8 * Real.sqrt 3) / 9 := by
    rw [cglmpFunctional_dkz (by norm_num), cglmpMaxEntValue_three]
    push_cast
    ring
  calc _ = 82 / 33 - 80 / 99 * Real.sqrt 3 := cglmpFunctional_adglState
    _ < (24 - 8 * Real.sqrt 3) / 9 := by nlinarith
    _ = cglmpFunctional (vonNeumannBehaviour 3 (dkzUnitaryA 3) (dkzUnitaryB 3)) := hdkz.symm
    _ ≤ cglmpFunctional (vonNeumannBehaviour 3 UA UB) :=
        dkz_optimal_of_le_twenty 3 (by norm_num) (by norm_num) UA UB hUA hUB

/- ### The strip inequality -/

/-- **The strip inequality $(*)$.** For every $M$, every orthogonal projection $B$ on
$\mathbb{C}^M$ (with $P = 1 - B$), every Hermitian $g$ and every real $\lambda$,
$\operatorname{Tr}[(P(g - \lambda)P)_+] \le \sum_{\nu \in \operatorname{spec}(B + ig)} h_\lambda(\nu)$,
the eigenvalues counted with algebraic multiplicity (`posPartTrace`, `stripSum`, `hStrip`).
Unconditional. -/
@[category research solved, AMS 15 81]
theorem strip_inequality (M : ℕ) (B g : Matrix (Fin M) (Fin M) ℂ) (hB : B.IsHermitian)
    (hB2 : B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) ≤ stripSum lam B g :=
  stripInequality M B g ⟨hB, hB2⟩ hg lam

/-- **Equality case of the strip inequality $(*)$**: equality forces $B$ and $g$ to commute.
Unconditional. -/
@[category research solved, AMS 15 81]
theorem strip_equality (M : ℕ) (B g : Matrix (Fin M) (Fin M) ℂ) (hB : B.IsHermitian)
    (hB2 : B * B = B) (hg : g.IsHermitian) (lam : ℝ)
    (h : stripSum lam B g = posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))) :
    B * g = g * B :=
  stripEquality M B g ⟨hB, hB2⟩ hg lam h

end MainResults

end OpenQuantumProblem27
