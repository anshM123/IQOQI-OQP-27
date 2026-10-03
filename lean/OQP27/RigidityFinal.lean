import OQP27.RigidityStrip
import OQP27.RigidityClassicalTwo
import OQP27.CertPos

/-!
# OQP 27B rigidity (Theorem R): the final statements of module L6

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, Theorem R.  Target: module L1's
`OQP27.RigidityStatement d` (`OQP27/Statement.lean`).

Proved here from the theorems of modules L1, L2, L4 and L6 (the hypotheses are listed in each statement):
* `OQP27.Rig.rigidity_two`: **Theorem R for `d = 2`** from the analytic hypotheses only (the single cell
  inequalities (1.3) and the continuum equality analysis); CONE_2 is module L4's `coneCertPos_2` and the
  classical Theorem B for `d = 2` is `OQP27.Rig.classicalTheoremB_two`.
* `OQP27.Rig.rigidity_le_twenty`: **Theorem R for `2 ≤ d ≤ 20`** from the analytic hypotheses and the classical
  Theorem B (CONE_d with a positive cell vector is module L4's `coneCertPos_le_twenty`).
* `OQP27.Rig.rigidity_every_d`: **Theorem R for every `d ≥ 2`** from the analytic hypotheses, the classical
  Theorem B, and module L4's computer-assisted `Hyp_ConeCertPos_large` (`d ≥ 21`).
* `OQP27.Rig.rigidity_every_d_strip`: the same with the analytic hypotheses in strip form: the strip
  inequality `(*)` and its equality case (module L1), and the continuum statements "(*) implies QD2-L1",
  "(*) implies (1.3) for positive cells", "(*) implies step (a) of s.3.7".
-/

set_option linter.unusedSectionVars false

namespace OQP27.Rig

/-- **Theorem R for `d = 2`** (CHSH), from the single cell inequalities and the continuum equality
analysis only. -/
theorem rigidity_two (h1 : Hyp_CellIneqSingle 2) (h2 : Hyp_ContinuumEquality 2) :
    RigidityStatement 2 :=
  rigidity_all_d' le_rfl h1 h2 coneCertPos_2 classicalTheoremB_two

/-- **Theorem R for `2 ≤ d ≤ 20`**: CONE_d with an all-positive cell vector is checked in Lean (module L4). -/
theorem rigidity_le_twenty {d : ℕ} [NeZero d] (hd2 : 2 ≤ d) (hd20 : d ≤ 20)
    (h1 : Hyp_CellIneqSingle d) (h2 : Hyp_ContinuumEquality d) (hB : Hyp_ClassicalTheoremB d) :
    RigidityStatement d :=
  rigidity_all_d' hd2 h1 h2 (coneCertPos_le_twenty d hd2 hd20) hB

/-- **Theorem R for every `d ≥ 2`** from the named hypotheses. -/
theorem rigidity_every_d (hlarge : Hyp_ConeCertPos_large)
    (h1 : ∀ d [NeZero d], 2 ≤ d → Hyp_CellIneqSingle d)
    (h2 : ∀ d [NeZero d], 2 ≤ d → Hyp_ContinuumEquality d)
    (hB : ∀ d [NeZero d], 2 ≤ d → Hyp_ClassicalTheoremB d)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) : RigidityStatement d :=
  rigidity_all_d' hd (h1 d hd) (h2 d hd) (coneCertPos_all hlarge d hd) (hB d hd)

/-- **Theorem R for every `d ≥ 2`**, with the analytic hypotheses in strip form. -/
theorem rigidity_every_d_strip (hlarge : Hyp_ConeCertPos_large) (hstrip : Hyp_StripInequality)
    (hstripEq : Hyp_StripEquality)
    (hcont : ∀ d [NeZero d], 2 ≤ d → Hyp_ContinuumCell d)
    (h1 : ∀ d [NeZero d], 2 ≤ d → Hyp_StripInequality → Hyp_CellIneqSinglePos d)
    (htight : ∀ d [NeZero d], 2 ≤ d → Hyp_StripInequality → Hyp_ContinuumTight d)
    (hB : ∀ d [NeZero d], 2 ≤ d → Hyp_ClassicalTheoremB d)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) : RigidityStatement d :=
  rigidity_of_strip_tight hd (hcont d hd hstrip) (h1 d hd hstrip) (htight d hd hstrip) hstripEq
    (coneCertPos_all hlarge d hd) (hB d hd)

end OQP27.Rig
