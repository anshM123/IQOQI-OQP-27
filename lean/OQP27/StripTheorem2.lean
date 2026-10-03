import OQP27.StripFromBMV
import OQP27.StripBMV

/-!
# Theorem 2 for the explicit density, from the Radon identity (modules L3a + L3b)

This file connects module L3a (`OQP27/StripFromBMV.lean`: Theorem 2 from Theorem 1) with module
L3b (`OQP27/StripBMV.lean`: Theorem 1 from the Radon identity (RI)).  For the explicit density
`F = OQP27.StripL3b.stripF (1 - B) g`, i.e. `F(s, τ) = (1/2π) Σ_i |Im x_i(s, τ)|` for `0 < τ < 1`
with `x_i(s, τ)` the roots of `det(g - s - x(P - τ))`, `P = 1 - B`:
* `densityReg_stripF`: the regularity `DensityReg` (proved by L3b, no hypotheses);
* `hyp_BMV2_of_RI`: `Hyp_BMV2 B g F` follows from `Hyp_RI M`;
* `strip_defect_formula_of_RI`, `strip_inequality_of_RI`, `strip_equality_iff_of_RI`: Theorem 2
  (exact defect, the strip inequality (*), equality iff `[B, g] = 0`) under `Hyp_RI M` only.

Hypothesis remaining: `OQP27.StripL3b.Hyp_RI M` (the Radon identity); paper proof in
`iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, sections 1-2.
-/

open Real MeasureTheory Complex Matrix

namespace OQP27.StripL3a

variable {M : ℕ} {B g : Matrix (Fin M) (Fin M) ℂ}

lemma isProj_one_sub (hB : B.IsHermitian ∧ B * B = B) : OQP27.StripL3b.IsProj (1 - B) :=
  ⟨(proj_compl_facts hB).1, (proj_compl_facts hB).2.1⟩

/-- `D(a, t)` of module L3a is the paper's form `bmvDPaper` of module L3b, with `P = 1 - B`. -/
lemma stripD_eq_bmvDPaper (a t : ℂ) :
    stripD B g a t = OQP27.StripL3b.bmvDPaper (1 - B) g a t := by
  unfold stripD OQP27.StripL3b.bmvDPaper
  rw [sub_sub_cancel]

/-- The explicit density satisfies `DensityReg` (Lemma 1 of the paper, proved in module L3b). -/
theorem densityReg_stripF (hRI : OQP27.StripL3b.Hyp_RI M) (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) : DensityReg (OQP27.StripL3b.stripF (1 - B) g) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := OQP27.StripL3b.bmv2_package hRI (isProj_one_sub hB) hg
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Theorem 1 (2BMV) from (RI)**, in the form `Hyp_BMV2` used by module L3a. -/
theorem hyp_BMV2_of_RI (hRI : OQP27.StripL3b.Hyp_RI M) (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) : Hyp_BMV2 B g (OQP27.StripL3b.stripF (1 - B) g) := by
  obtain ⟨-, -, -, -, -, hint, hbmv⟩ :=
    OQP27.StripL3b.bmv2_package hRI (isProj_one_sub hB) hg
  have hF := densityReg_stripF hRI hB hg
  intro a t
  rw [stripD_eq_bmvDPaper, hbmv a t]
  congr 1
  exact (hF.iterated_eq_prod (fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2)) (hint a t)).symm

/-- **Theorem 2 from (RI)**: the exact defect formula for the explicit density. -/
theorem strip_defect_formula_of_RI (hRI : OQP27.StripL3b.Hyp_RI M)
    (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
      - posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))
      = stripBalayage (OQP27.StripL3b.stripF (1 - B) g) lam :=
  strip_defect_formula hB hg (densityReg_stripF hRI hB hg) (hyp_BMV2_of_RI hRI hB hg) lam

/-- **The strip inequality (*) from (RI)**. -/
theorem strip_inequality_of_RI (hRI : OQP27.StripL3b.Hyp_RI M)
    (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))
      ≤ ((B + I • g).charpoly.roots.map (hLam lam)).sum :=
  strip_inequality hB hg (densityReg_stripF hRI hB hg) (hyp_BMV2_of_RI hRI hB hg) lam

/-- **Equality case from (RI)**: equality in (*) iff `[B, g] = 0`. -/
theorem strip_equality_iff_of_RI (hRI : OQP27.StripL3b.Hyp_RI M)
    (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
      = posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) ↔ Commute B g :=
  strip_equality_iff hB hg (densityReg_stripF hRI hB hg) (hyp_BMV2_of_RI hRI hB hg) lam

end OQP27.StripL3a
