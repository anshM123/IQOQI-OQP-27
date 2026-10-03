import OQP27.StripTheorem2
import OQP27.Skeleton

/-!
# The strip hypotheses of the skeleton, from the Radon identity (module L3a)

`OQP27/Skeleton.lean` (module L1) states the strip inequality (*) and its equality case as the
hypotheses `OQP27.Hyp_StripInequality` and `OQP27.Hyp_StripEquality`, with its own copies of `h_λ`
(`OQP27.hStrip`), of `Tr X_+` (`OQP27.posPartTrace`) and of the spectral sum (`OQP27.stripSum`).
This file identifies those definitions with the ones of module L3a and proves both hypotheses from
the Radon identity `OQP27.StripL3b.Hyp_RI` of module L3b (for every matrix size), via Theorem 1
(module L3b) and Theorem 2 (module L3a).

Hypothesis remaining: `∀ M, OQP27.StripL3b.Hyp_RI M` (paper proof:
`iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, sections 1-2).
-/

namespace OQP27.StripL3a

variable {M : ℕ}

lemma hStrip_eq_hLam (lam : ℝ) (w : ℂ) : OQP27.hStrip lam w = OQP27.StripL3a.hLam lam w := by
  unfold OQP27.hStrip OQP27.StripL3a.hLam OQP27.stripPoissonKernel
  split_ifs
  · rfl
  · rfl
  · congr 1
    funext s
    rw [mul_comm]
    rfl

lemma skeleton_posPartTrace_eq (A : Matrix (Fin M) (Fin M) ℂ) :
    OQP27.posPartTrace A = OQP27.StripL3a.posPartTrace A := by
  unfold OQP27.posPartTrace OQP27.StripL3a.posPartTrace
  by_cases h : A.IsHermitian
  · simp only [dif_pos h]
  · simp only [dif_neg h]

lemma skeleton_stripSum_eq (lam : ℝ) (B g : Matrix (Fin M) (Fin M) ℂ) :
    OQP27.stripSum lam B g
      = ((B + Complex.I • g).charpoly.roots.map (OQP27.StripL3a.hLam lam)).sum := by
  unfold OQP27.stripSum
  congr 1
  exact Multiset.map_congr rfl (fun w _ => hStrip_eq_hLam lam w)

/-- **`Hyp_StripInequality` of the skeleton from (RI).** -/
theorem hyp_StripInequality_of_RI (hRI : ∀ M : ℕ, OQP27.StripL3b.Hyp_RI M) :
    OQP27.Hyp_StripInequality := by
  intro M B g hB hg lam
  rw [skeleton_posPartTrace_eq, skeleton_stripSum_eq]
  exact OQP27.StripL3a.strip_inequality_of_RI (hRI M) hB hg lam

/-- **`Hyp_StripEquality` of the skeleton from (RI).** -/
theorem hyp_StripEquality_of_RI (hRI : ∀ M : ℕ, OQP27.StripL3b.Hyp_RI M) :
    OQP27.Hyp_StripEquality := by
  intro M B g hB hg lam heq
  rw [skeleton_posPartTrace_eq, skeleton_stripSum_eq] at heq
  exact (OQP27.StripL3a.strip_equality_iff_of_RI (hRI M) hB hg lam).mp heq

end OQP27.StripL3a
