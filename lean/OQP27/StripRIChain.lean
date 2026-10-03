import OQP27.StripRIMain
import OQP27.StripSkeleton

/-!
# The strip chain without hypotheses (module L3b, using the bridges of modules L3a and L1)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`OQP27.StripL3b.hyp_RI` (`OQP27/StripRIMain.lean`) proves the Radon identity `Hyp_RI M` for every `M`.
Plugged into the bridges of module L3a (`OQP27/StripTheorem2.lean`, `OQP27/StripSkeleton.lean`), it gives,
with no hypotheses:
* `hyp_BMV2_stripF`: Theorem 1 (2BMV) in the form `OQP27.StripL3a.Hyp_BMV2 B g F` used by module L3a, for
  the explicit density `F = stripF (1 - B) g`;
* `strip_defect_formula_noHyp`, `strip_inequality_noHyp`, `strip_equality_iff_noHyp`: Theorem 2 of
  `Q_2bmv/PROOF.md` (exact defect formula, the strip inequality (*), equality iff `[B, g] = 0`);
* `hyp_StripInequality`, `hyp_StripEquality`: the hypotheses `OQP27.Hyp_StripInequality` and
  `OQP27.Hyp_StripEquality` of the skeleton of module L1 (`OQP27/Skeleton.lean`).

Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, sections 2, 4, 5; `Q_2bmv/PROOF.md`, Theorems 1, 2.
-/

namespace OQP27.StripL3b

open Complex

variable {M : ℕ} {B g : Matrix (Fin M) (Fin M) ℂ}

/-- **Theorem 1 (2BMV)** in the form `Hyp_BMV2` of module L3a, for the explicit density. -/
theorem hyp_BMV2_stripF (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) :
    OQP27.StripL3a.Hyp_BMV2 B g (stripF (1 - B) g) :=
  OQP27.StripL3a.hyp_BMV2_of_RI (hyp_RI M) hB hg

/-- **Theorem 2 (exact defect formula)**, no hypotheses. -/
theorem strip_defect_formula_noHyp (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (OQP27.StripL3a.hLam lam)).sum
      - OQP27.StripL3a.posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))
      = OQP27.StripL3a.stripBalayage (stripF (1 - B) g) lam :=
  OQP27.StripL3a.strip_defect_formula_of_RI (hyp_RI M) hB hg lam

/-- **The strip inequality (*)**, no hypotheses. -/
theorem strip_inequality_noHyp (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    OQP27.StripL3a.posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))
      ≤ ((B + I • g).charpoly.roots.map (OQP27.StripL3a.hLam lam)).sum :=
  OQP27.StripL3a.strip_inequality_of_RI (hyp_RI M) hB hg lam

/-- **Equality case of (*)**, no hypotheses: equality iff `[B, g] = 0`. -/
theorem strip_equality_iff_noHyp (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (OQP27.StripL3a.hLam lam)).sum
      = OQP27.StripL3a.posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) ↔ Commute B g :=
  OQP27.StripL3a.strip_equality_iff_of_RI (hyp_RI M) hB hg lam

/-- **The skeleton hypothesis `Hyp_StripInequality` of module L1 holds.** -/
theorem hyp_StripInequality : OQP27.Hyp_StripInequality :=
  OQP27.StripL3a.hyp_StripInequality_of_RI hyp_RI

/-- **The skeleton hypothesis `Hyp_StripEquality` of module L1 holds.** -/
theorem hyp_StripEquality : OQP27.Hyp_StripEquality :=
  OQP27.StripL3a.hyp_StripEquality_of_RI hyp_RI

end OQP27.StripL3b
